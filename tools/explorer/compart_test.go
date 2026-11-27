package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"os"
	"path/filepath"
	"testing"
)

// A five-file tree with the two traps 447 met: two files named Main.lean under
// different prefixes (they once collided into one node), and a cone that must
// follow imports transitively but stay inside its own branch.
var tinyTree = map[string]string{
	"src/Statements.lean":      "import Mathlib\ndef S : Prop := True\n",
	"src/Main.lean":            "import New.Main\ntheorem top : S := New.last\n",
	"src/New/Main.lean":        "import New.A.X\n/-!\n# The last step\n-/\ntheorem New.last : S := New.x\n",
	"src/New/A/X.lean":         "import Lib.Y\n/-!\n# Ex\n-/\ntheorem New.x : S := New.y\n",
	"src/Lib/Y.lean":           "import Statements\ntheorem New.y : S := trivial\n",
	"scripts/PrintAxioms.lean": "import Main\n",
}

const tinySpec = `{"id":"r","title":"root","summary":"s","children":[
 {"id":"top","title":"top","prefixes":["src/Main.lean","src/Statements.lean","src/New/Main.lean"]},
 {"id":"a","title":"A","prefixes":["src/New/A/"]},
 {"id":"lib","title":"Lib","prefixes":["src/Lib/"]}]}`

func TestCompartmentsOnTinyTree(t *testing.T) {
	dir := t.TempDir()
	for p, s := range tinyTree {
		full := filepath.Join(dir, p)
		os.MkdirAll(filepath.Dir(full), 0o755)
		os.WriteFile(full, []byte(s), 0o644)
	}
	spec := filepath.Join(dir, "spec.json")
	os.WriteFile(spec, []byte(tinySpec), 0o644)
	files, decls, toks, strs, ctxs, ctxM = nil, nil, newInterner(), newInterner(), nil, map[string]int32{}
	*flagSrc = dir
	defer func() { *flagSrc = "" }()
	var seen []string
	err := parallelParse(func(fn func(string, []byte)) error { return walkDir(dir, fn) },
		func(name string, data []byte) bool {
			seen = append(seen, name)
			return filepath.Ext(name) == ".lean" && name != "lean/scripts/PrintAxioms.lean"
		},
		false, func(name string, pf pfile) {
			files = append(files, file{path: name[len("lean/"):], module: pf.module, imports: pf.imports, lines: pf.lines, bytes: pf.bytes, heading: pf.heading, ndecls: int32(len(pf.decls))})
			for _, d := range pf.decls {
				nd := decl{name: d.name, kind: d.kind, file: int32(len(files) - 1), line: d.line, declLine: d.declLine, endLine: d.endLine, ctx: addCtx(pf.ctxs[d.ctx])}
				for _, x := range d.stmtToks {
					nd.sToks = append(nd.sToks, toks.id(x))
				}
				for _, x := range d.bodyToks {
					nd.bToks = append(nd.bToks, toks.id(x))
				}
				decls = append(decls, nd)
			}
		})
	if err != nil {
		t.Fatal(err)
	}
	if len(seen) != len(tinyTree) {
		t.Fatalf("walkDir saw %d files, want %d: %v", len(seen), len(tinyTree), seen)
	}
	r := resolve(nil)
	cm := buildCompartments(r, spec)
	byPath := map[string]compNode{}
	byID := map[string]compNode{}
	for _, n := range cm.Nodes {
		if n.Kind == "file" {
			byPath[n.Path] = n
		}
		byID[n.ID] = n
	}
	for _, p := range []string{"src/Main.lean", "src/New/Main.lean", "src/Statements.lean", "src/New/A/X.lean", "src/Lib/Y.lean"} {
		if _, ok := byPath[p]; !ok {
			t.Errorf("no file node for %s", p)
		}
	}
	if got := byPath["src/New/Main.lean"].Summary; got != "The last step" {
		t.Errorf("file summary %q, want the module heading", got)
	}
	// A's cone: X, Y, Statements (3 files); Lib's: Y, Statements (2); the root's: all 5
	if c := byID["a"].Cone.Files; c != 3 {
		t.Errorf("cone of A has %d files, want 3", c)
	}
	if c := byID["lib"].Cone.Files; c != 2 {
		t.Errorf("cone of Lib has %d files, want 2", c)
	}
	if c := byID["r"].Size.Files; c != 5 {
		t.Errorf("root holds %d files, want 5", c)
	}
	if len(cm.Roots) != 1 || cm.Roots[0].Decls != 5 {
		t.Errorf("roots %+v, want one root reaching 5 declarations", cm.Roots)
	}
}

// The tarball path after 447's refactor: parallelParse over walkTarGz still
// sees every regular file, in order.
func TestTarGzWalker(t *testing.T) {
	var buf bytes.Buffer
	gz := gzip.NewWriter(&buf)
	tw := tar.NewWriter(gz)
	for _, n := range []string{"lean/src/A.lean", "lean/src/B.lean", "lean/lean-toolchain"} {
		body := []byte("theorem t : True := trivial\n")
		tw.WriteHeader(&tar.Header{Name: n, Mode: 0o644, Size: int64(len(body)), Typeflag: tar.TypeReg})
		tw.Write(body)
	}
	tw.Close()
	gz.Close()
	var got []string
	err := parallelParse(func(fn func(string, []byte)) error { return walkTarGz(&buf, fn) },
		func(name string, _ []byte) bool { return filepath.Ext(name) == ".lean" }, false,
		func(name string, _ pfile) { got = append(got, name) })
	if err != nil || len(got) != 2 || got[0] != "lean/src/A.lean" || got[1] != "lean/src/B.lean" {
		t.Fatalf("got %v, %v", got, err)
	}
}
