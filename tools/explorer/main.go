// Command explorer builds the data for explorer/ — a browsable map of Levent
// Alpöge's released Lean development (RH and GRH for Dirichlet L-functions).
//
// It streams the release (https://alpo.ge/lean.tar.gz.part01 … part14) through
// gzip and tar, checks the concatenation's SHA-256 against COMPARISON.md §7, and
// parses each .lean file as it passes. The tree is never written to disk; only
// compact JSON shards under -out are.
//
// What the edges are. This is a SOURCE-LEVEL parse, not an elaboration. For
// every declaration it records the identifiers its statement and its body
// mention, and resolves each one the way Lean's name lookup would on the
// surface — current namespace and its parents, the declaration's own prefix,
// `open`s in scope — against the tree's own declaration names and, failing
// that, against the declaration names of Mathlib and the other pinned
// dependencies (read the same way, from their source at the pinned revisions).
// Such an edge is labelled [parsed]. It can be wrong in both directions:
//   - missed: anything the elaborator supplies without a name in the text —
//     instances found by type-class search, `simp` sets, coercions, notation,
//     tactic-generated terms, dot notation `x.foo` on a local `x`;
//   - spurious: a local binder whose name happens to equal a declaration in an
//     enclosing namespace.
//
// An [elaborated] edge would come from Lean's own environment after a build,
// which needs the 17M-line tree compiled; this generator does not do that.
//
// Usage:
//
//	go run ./tools/explorer -out explorer/data            # fetch and stream
//	go run ./tools/explorer -parts DIR -out explorer/data # read cached parts
//	go run ./tools/explorer -src DIR -commit SHA -repo URL \
//	    -compartments FILE -out explorer/data/grh          # a checked-out edition
//
// With -src the tree is a directory (a checkout of another edition, e.g.
// lsernau/grh-lean's grh/ at a pinned commit, which the caller checks out by
// SHA); no tarball hash applies, and -commit is recorded as the pin. With
// -compartments the generator also writes c.json, the fractal compartment map
// (compart.go).
package main

import (
	"archive/tar"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

const releaseSHA = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"

var (
	flagOut     = flag.String("out", "explorer/data", "output directory")
	flagParts   = flag.String("parts", "", "directory holding lean.tar.gz.partNN (default: fetch from alpo.ge)")
	flagURL     = flag.String("url", "https://alpo.ge/lean.tar.gz.part", "release part URL prefix")
	flagNParts  = flag.Int("nparts", 14, "number of parts")
	flagStmts   = flag.Bool("statements", false, "include statements and docstrings (off: the release carries no licence)")
	flagNoExt   = flag.Bool("no-ext", false, "skip resolving against Mathlib and the other dependencies")
	flagExtDir  = flag.String("ext-cache", "", "directory to cache dependency tarballs (default: stream, no cache)")
	flagShard   = flag.Int("shard", 400, "declarations per node shard")
	flagSketchK = flag.Int("k", 128, "bottom-k sketch size for subtree sizes (exact below k)")
	flagSrc     = flag.String("src", "", "read the tree from this directory instead of the release parts")
	flagCommit  = flag.String("commit", "", "with -src: the pinned commit the directory is checked out at")
	flagRepo    = flag.String("repo", "", "with -src: the repository URL and subdirectory, for source links")
	flagEdition = flag.String("edition", "", "with -src: the edition's name, shown by the viewer")
	flagComp    = flag.String("compartments", "", "compartment spec (JSON) for the fractal map, c.json")
	flagDot     = flag.Int("dot", 0, "resolve dot notation on a local (x.foo.bar) to every tree declaration ending in .foo.bar, if there are at most this many (0: off)")
)

func logf(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "[%s] "+f+"\n", append([]any{time.Now().Format("15:04:05")}, a...)...)
}

// ---------------------------------------------------------------- streaming

type multiFetch struct {
	urls []string
	cur  io.ReadCloser
	i    int
}

func (m *multiFetch) Read(p []byte) (int, error) {
	for {
		if m.cur == nil {
			if m.i >= len(m.urls) {
				return 0, io.EOF
			}
			u := m.urls[m.i]
			m.i++
			var rc io.ReadCloser
			if strings.HasPrefix(u, "http") {
				resp, err := http.Get(u)
				if err != nil {
					return 0, err
				}
				if resp.StatusCode != 200 {
					return 0, fmt.Errorf("%s: HTTP %d", u, resp.StatusCode)
				}
				rc = resp.Body
			} else {
				f, err := os.Open(u)
				if err != nil {
					return 0, err
				}
				rc = f
			}
			m.cur = rc
		}
		n, err := m.cur.Read(p)
		if err == io.EOF {
			m.cur.Close()
			m.cur = nil
			if n > 0 {
				return n, nil
			}
			continue
		}
		return n, err
	}
}

// walkTarGz streams a .tar.gz and calls fn for each regular file.
func walkTarGz(r io.Reader, fn func(name string, data []byte)) error {
	gz, err := gzip.NewReader(r)
	if err != nil {
		return err
	}
	tr := tar.NewReader(gz)
	for {
		h, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if h.Typeflag != tar.TypeReg {
			continue
		}
		data, err := io.ReadAll(tr)
		if err != nil {
			return err
		}
		fn(h.Name, data)
	}
	// drain, so the hash sees every byte
	_, err = io.Copy(io.Discard, gz)
	return err
}

// walkDir calls fn for each regular file under dir, named as the release names
// its entries ("lean/" + relative path), in a stable (sorted) order. It skips
// .git and .lake, and reads only .lean files plus the two pin files.
func walkDir(dir string, fn func(name string, data []byte)) error {
	var paths []string
	err := filepath.WalkDir(dir, func(p string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if n := d.Name(); n == ".git" || n == ".lake" {
				return filepath.SkipDir
			}
			return nil
		}
		if !d.Type().IsRegular() {
			return nil
		}
		rel, _ := filepath.Rel(dir, p)
		rel = filepath.ToSlash(rel)
		if strings.HasSuffix(rel, ".lean") || rel == "lake-manifest.json" || rel == "lean-toolchain" {
			paths = append(paths, rel)
		}
		return nil
	})
	if err != nil {
		return err
	}
	sort.Strings(paths)
	for _, rel := range paths {
		data, err := os.ReadFile(filepath.Join(dir, rel))
		if err != nil {
			return err
		}
		fn("lean/"+rel, data)
	}
	return nil
}

// ---------------------------------------------------------------- interning

type interner struct {
	m map[string]int32
	s []string
}

func newInterner() *interner { return &interner{m: map[string]int32{}} }
func (in *interner) id(s string) int32 {
	if v, ok := in.m[s]; ok {
		return v
	}
	v := int32(len(in.s))
	in.m[s] = v
	in.s = append(in.s, s)
	return v
}

// ---------------------------------------------------------------- model

type decl struct {
	name     string
	kind     string
	file     int32
	line     int32
	declLine int32
	endLine  int32
	doc      string
	stmt     string
	ctx      int32   // global ctx id
	sToks    []int32 // interned identifiers, statement
	bToks    []int32 // interned identifiers, body
	aliases  []string
	private  bool
}

type file struct {
	path    string
	module  string
	imports []string
	lines   int32
	bytes   int64
	heading string
	ndecls  int32
}

type extDecl struct {
	name string
	lib  int32
	file int32
	line int32
}

type extLib struct {
	Name string `json:"name"`
	Rev  string `json:"rev"`
	URL  string `json:"url"`
	Blob string `json:"blob"` // source link prefix: Blob + path + "#L" + line
}

var (
	toks  = newInterner()
	strs  = newInterner() // context prefixes
	ctxs  [][]int32       // global ctx id -> prefix ids
	ctxM  = map[string]int32{}
	files []file
	decls []decl
)

func addCtx(pre []string) int32 {
	key := strings.Join(pre, "\x00")
	if v, ok := ctxM[key]; ok {
		return v
	}
	ids := make([]int32, len(pre))
	for i, p := range pre {
		ids[i] = strs.id(p)
	}
	v := int32(len(ctxs))
	ctxs = append(ctxs, ids)
	ctxM[key] = v
	return v
}

func main() {
	flag.Parse()
	t0 := time.Now()

	// ---- the release, streamed once
	var urls []string
	for i := 1; i <= *flagNParts; i++ {
		name := fmt.Sprintf("%02d", i)
		if *flagParts != "" {
			urls = append(urls, filepath.Join(*flagParts, "lean.tar.gz.part"+name))
		} else {
			urls = append(urls, *flagURL+name)
		}
	}
	h := sha256.New()
	var counted int64
	var walker func(fn func(name string, data []byte)) error
	if *flagSrc != "" {
		if *flagCommit == "" {
			fatal("-src needs -commit, the pin the directory is checked out at")
		}
		walker = func(fn func(string, []byte)) error { return walkDir(*flagSrc, fn) }
	} else {
		src := io.TeeReader(&multiFetch{urls: urls}, h)
		walker = func(fn func(string, []byte)) error { return walkTarGz(src, fn) }
	}
	var manifest, toolchain []byte
	var nLean, totalLines int64
	err := parallelParse(walker, func(name string, data []byte) bool {
		counted += int64(len(data))
		switch {
		case name == "lean/lake-manifest.json":
			manifest = data
			return false
		case name == "lean/lean-toolchain":
			toolchain = data
			return false
		case !strings.HasSuffix(name, ".lean"):
			logf("non-.lean entry: %s (%d bytes)", name, len(data))
			return false
		case *flagSrc != "" && !strings.HasPrefix(name, "lean/src/"):
			// Challenge.lean (the Comparator stub, five sorries) and scripts/:
			// outside the library, imported by nothing
			logf("outside src/, not parsed: %s", name)
			return false
		}
		return true
	}, *flagStmts, func(name string, pf pfile) {
		nLean++
		totalLines += int64(pf.lines)
		fi := int32(len(files))
		files = append(files, file{path: strings.TrimPrefix(name, "lean/"), module: pf.module, imports: pf.imports, lines: pf.lines, bytes: pf.bytes, heading: pf.heading, ndecls: int32(len(pf.decls))})
		gctx := make([]int32, len(pf.ctxs))
		for i, c := range pf.ctxs {
			gctx[i] = addCtx(c)
		}
		for _, d := range pf.decls {
			nd := decl{name: d.name, kind: d.kind, file: fi, line: d.line, declLine: d.declLine, endLine: d.endLine,
				doc: d.doc, stmt: d.stmt, ctx: gctx[d.ctx], aliases: d.aliases, private: d.private}
			nd.sToks = make([]int32, len(d.stmtToks))
			for i, t := range d.stmtToks {
				nd.sToks[i] = toks.id(t)
			}
			nd.bToks = make([]int32, len(d.bodyToks))
			for i, t := range d.bodyToks {
				nd.bToks[i] = toks.id(t)
			}
			decls = append(decls, nd)
		}
		if nLean%20000 == 0 {
			logf("%d files, %d decls, %d tokens", nLean, len(decls), len(toks.s))
		}
	})
	if err != nil {
		fatal("release stream: %v", err)
	}
	got := hex.EncodeToString(h.Sum(nil))
	if *flagSrc == "" && got != releaseSHA {
		fatal("release SHA-256 %s, expected %s (COMPARISON.md §7) — refusing to publish", got, releaseSHA)
	}
	tStream := time.Since(t0)
	logf("release: SHA-256 ok, %d .lean files, %d lines, %d declarations, %s", nLean, totalLines, len(decls), tStream)

	// ---- the dependencies, from the pins in the release's own manifest
	var libs []extLib
	var exts []extDecl
	if !*flagNoExt {
		libs, exts = loadExternals(manifest, toolchain)
	}
	tExt := time.Since(t0) - tStream

	res := resolve(exts)
	res.libs = libs
	res.stats.Files = len(files)
	res.stats.Lines = totalLines
	res.stats.Bytes = counted
	res.stats.StreamSec = tStream.Seconds()
	res.stats.ExtSec = tExt.Seconds()
	var comp *compMap
	if *flagComp != "" {
		comp = buildCompartments(res, *flagComp)
	}
	write(res, strings.TrimSpace(string(toolchain)), comp)
	var ms runtime.MemStats
	runtime.ReadMemStats(&ms)
	logf("done in %s (peak heap ~%d MB)", time.Since(t0).Round(time.Second), ms.Sys>>20)
}

func fatal(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "explorer: "+f+"\n", a...)
	os.Exit(1)
}

// ---------------------------------------------------------------- externals

type manifestT struct {
	Packages []struct {
		URL  string `json:"url"`
		Rev  string `json:"rev"`
		Name string `json:"name"`
	} `json:"packages"`
}

// libraries whose declarations count as "the edge": the release's pinned
// dependencies that ship Lean declarations a proof can use, plus Lean core.
var extWanted = map[string]bool{"mathlib": true, "batteries": true, "aesop": true, "Qq": true, "plausible": true}

func loadExternals(manifest, toolchain []byte) ([]extLib, []extDecl) {
	var m manifestT
	if err := json.Unmarshal(manifest, &m); err != nil {
		fatal("release lake-manifest.json: %v", err)
	}
	var libs []extLib
	for _, p := range m.Packages {
		if !extWanted[p.Name] {
			continue
		}
		repo := strings.TrimSuffix(strings.TrimPrefix(p.URL, "https://github.com/"), ".git")
		libs = append(libs, extLib{Name: p.Name, Rev: p.Rev, URL: p.URL,
			Blob: "https://github.com/" + repo + "/blob/" + p.Rev + "/"})
	}
	// Lean core at the release's toolchain tag, e.g. leanprover/lean4:v4.33.1
	tc := strings.TrimSpace(string(toolchain))
	if i := strings.Index(tc, ":"); i >= 0 {
		tag := tc[i+1:]
		libs = append(libs, extLib{Name: "lean4", Rev: tag, URL: "https://github.com/leanprover/lean4",
			Blob: "https://github.com/leanprover/lean4/blob/" + tag + "/"})
	}
	var exts []extDecl
	for li, lib := range libs {
		repo := strings.TrimPrefix(lib.URL, "https://github.com/")
		ref := lib.Rev
		if lib.Name == "lean4" {
			ref = "refs/tags/" + lib.Rev
		}
		u := "https://codeload.github.com/" + repo + "/tar.gz/" + ref
		var r io.Reader
		var closer io.Closer
		cache := ""
		if *flagExtDir != "" {
			cache = filepath.Join(*flagExtDir, lib.Name+"-"+lib.Rev+".tar.gz")
		}
		if cache != "" {
			if _, err := os.Stat(cache); err != nil {
				if err := download(u, cache); err != nil {
					fatal("%s: %v", u, err)
				}
			}
			f, err := os.Open(cache)
			if err != nil {
				fatal("%v", err)
			}
			r, closer = f, f
		} else {
			resp, err := http.Get(u)
			if err != nil || resp.StatusCode != 200 {
				fatal("%s: %v", u, err)
			}
			r, closer = resp.Body, resp.Body
		}
		n0 := len(exts)
		nf := 0
		err := parallelParse(func(fn func(string, []byte)) error { return walkTarGz(r, fn) }, func(name string, data []byte) bool {
			if !strings.HasSuffix(name, ".lean") {
				return false
			}
			// strip the "<repo>-<rev>/" top directory
			if i := strings.IndexByte(name, '/'); i >= 0 {
				name = name[i+1:]
			}
			if lib.Name == "lean4" {
				return strings.HasPrefix(name, "src/Init") || strings.HasPrefix(name, "src/Std") || strings.HasPrefix(name, "src/Lean")
			}
			return !(strings.HasPrefix(name, "test") || strings.HasPrefix(name, "scripts/") || strings.HasPrefix(name, "Archive/") || strings.HasPrefix(name, "Counterexamples/") || strings.HasPrefix(name, "docs/"))
		}, false, func(name string, pf pfile) {
			if i := strings.IndexByte(name, '/'); i >= 0 {
				name = name[i+1:]
			}
			nf++
			fi := extFile(name)
			for _, d := range pf.decls {
				exts = append(exts, extDecl{name: d.name, lib: int32(li), file: fi, line: d.declLine})
				for _, a := range d.aliases {
					exts = append(exts, extDecl{name: a, lib: int32(li), file: fi, line: d.declLine})
				}
			}
		})
		closer.Close()
		if err != nil {
			fatal("%s: %v", u, err)
		}
		logf("dependency %s@%s: %d files, %d names", lib.Name, short(lib.Rev), nf, len(exts)-n0)
	}
	return libs, exts
}

var extFiles []string
var extFileM = map[string]int32{}

func extFile(p string) int32 {
	if v, ok := extFileM[p]; ok {
		return v
	}
	v := int32(len(extFiles))
	extFiles = append(extFiles, p)
	extFileM[p] = v
	return v
}

func short(s string) string {
	if len(s) > 10 {
		return s[:10]
	}
	return s
}

func download(u, path string) error {
	resp, err := http.Get(u)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return fmt.Errorf("HTTP %d", resp.StatusCode)
	}
	f, err := os.Create(path + ".tmp")
	if err != nil {
		return err
	}
	if _, err := io.Copy(f, resp.Body); err != nil {
		f.Close()
		return err
	}
	f.Close()
	return os.Rename(path+".tmp", path)
}

// ---------------------------------------------------------------- resolution

type stats struct {
	Files          int     `json:"files"`
	Lines          int64   `json:"lines"`
	Bytes          int64   `json:"bytes"`
	Decls          int     `json:"decls"`
	Reachable      int     `json:"reachable"`
	ReachableLines int64   `json:"reachableLines"`
	ExtNames       int     `json:"extNames"`
	ExtUsed        int     `json:"extUsed"`
	TokRefs        int64   `json:"identifierMentions"`
	TreeEdges      int64   `json:"treeEdges"`
	ExtEdges       int64   `json:"extEdges"`
	Unresolved     int64   `json:"unresolvedMentions"`
	ViaParent      int64   `json:"edgesViaGeneratedName"`
	ViaDot         int64   `json:"lookupsViaDotNotation"`
	Ambiguous      int64   `json:"ambiguousLookups"`
	AmbigByImports int64   `json:"ambiguousLookupsSettledByImports"`
	AmbigUnsettled int64   `json:"ambiguousLookupsUnsettled"`
	DupNames       int     `json:"namesDeclaredMoreThanOnce"`
	StreamSec      float64 `json:"streamSeconds"`
	ExtSec         float64 `json:"dependencySeconds"`
	ResolveSec     float64 `json:"resolveSeconds"`
}

type result struct {
	order    []int32   // node id -> decl index
	nodeOf   []int32   // decl index -> node id
	sUses    [][]int32 // per decl index: tree decl indices used in the statement
	bUses    [][]int32 // … in the body only
	sExt     [][]int32 // ext indices (into extUsed numbering) used in the statement
	bExt     [][]int32
	usedBy   []int32
	reach    []bool
	subDecls []int64
	subLines []int64
	subExact []bool
	roots    []int32
	extList  []extDecl // used externals only
	libs     []extLib
	stats    stats
}

func resolve(exts []extDecl) *result {
	t0 := time.Now()
	r := &result{}
	n := len(decls)
	// name -> decl indices (a name can be declared in several modules that are
	// never imported together)
	byName := make(map[string][]int32, n)
	for i := range decls {
		byName[decls[i].name] = append(byName[decls[i].name], int32(i))
	}
	for _, v := range byName {
		if len(v) > 1 {
			r.stats.DupNames++
		}
	}
	alias := map[string][]int32{}
	for i := range decls {
		for _, a := range decls[i].aliases {
			if _, ok := byName[a]; !ok {
				alias[a] = append(alias[a], int32(i))
			}
		}
	}
	extBy := make(map[string]int32, len(exts))
	for i, e := range exts {
		if _, ok := extBy[e.name]; !ok {
			extBy[e.name] = int32(i)
		}
	}
	r.stats.ExtNames = len(extBy)
	modFile := map[string]int32{}
	for i, f := range files {
		modFile[f.module] = int32(i)
	}
	imports := make([][]int32, len(files))
	for i, f := range files {
		for _, m := range f.imports {
			if j, ok := modFile[m]; ok {
				imports[i] = append(imports[i], j)
			}
		}
	}
	// Ambiguity is settled by imports: of several declarations with one name,
	// the one a file can see is the one in its import closure. A = the files
	// that declare a duplicated name; reachA[f] = the A-files f imports
	// (transitively, itself included), as a bitset, built bottom-up.
	aIdx := map[int32]int{}
	for _, v := range byName {
		if len(v) > 1 {
			for _, c := range v {
				if _, ok := aIdx[decls[c].file]; !ok {
					aIdx[decls[c].file] = len(aIdx)
				}
			}
		}
	}
	for _, v := range alias {
		if len(v) > 1 {
			for _, c := range v {
				if _, ok := aIdx[decls[c].file]; !ok {
					aIdx[decls[c].file] = len(aIdx)
				}
			}
		}
	}
	words := (len(aIdx) + 63) / 64
	logf("ambiguity: %d names declared more than once, in %d files; import bitsets %d MB", r.stats.DupNames, len(aIdx), len(files)*words*8>>20)
	reachA := make([][]uint64, len(files))
	state := make([]uint8, len(files)) // 0 new, 1 on stack, 2 done
	for root := range files {
		if state[root] == 2 {
			continue
		}
		type fr struct{ f, k int32 }
		st := []fr{{int32(root), 0}}
		state[root] = 1
		for len(st) > 0 {
			top := &st[len(st)-1]
			if int(top.k) < len(imports[top.f]) {
				y := imports[top.f][top.k]
				top.k++
				if state[y] == 0 {
					state[y] = 1
					st = append(st, fr{y, 0})
				}
				continue
			}
			f := top.f
			st = st[:len(st)-1]
			b := make([]uint64, words)
			if a, ok := aIdx[f]; ok {
				b[a/64] |= 1 << (a % 64)
			}
			for _, y := range imports[f] {
				if yb := reachA[y]; yb != nil {
					for w := range b {
						b[w] |= yb[w]
					}
				}
			}
			reachA[f] = b
			state[f] = 2
		}
	}
	inClosure := func(from, target int32) bool {
		a, ok := aIdx[target]
		if !ok || reachA[from] == nil {
			return false
		}
		return reachA[from][a/64]&(1<<(a%64)) != 0
	}
	extUsedIdx := map[int32]int32{}
	pick := func(di int32, cands []int32) int32 {
		if len(cands) == 1 {
			if c := cands[0]; decls[c].private && decls[c].file != decls[di].file {
				return -1 // private to another file
			}
			return cands[0]
		}
		r.stats.Ambiguous++
		f := decls[di].file
		var hit []int32
		for _, c := range cands { // a declaration in the same file wins
			if decls[c].file == f {
				hit = append(hit, c)
			}
		}
		if len(hit) == 0 {
			for _, c := range cands { // private declarations are file-local
				if !decls[c].private && inClosure(f, decls[c].file) {
					hit = append(hit, c)
				}
			}
		}
		if len(hit) == 1 {
			r.stats.AmbigByImports++
			return hit[0]
		}
		r.stats.AmbigUnsettled++
		return -1
	}
	lookup := func(di int32, name string) (int32, int32, bool) { // tree, ext, viaParent
		if c, ok := byName[name]; ok {
			return pick(di, c), -1, false
		}
		if e, ok := extBy[name]; ok {
			return -1, e, false
		}
		if c, ok := alias[name]; ok {
			return pick(di, c), -1, true
		}
		return -1, -1, false
	}
	r.sUses = make([][]int32, n)
	r.bUses = make([][]int32, n)
	r.sExt = make([][]int32, n)
	r.bExt = make([][]int32, n)
	r.usedBy = make([]int32, n)
	// the last component of every known name: a mention whose last component
	// is not among them cannot resolve, which disposes of most local variables
	lastSet := map[string]struct{}{}
	addLast := func(n string) {
		if k := strings.LastIndexByte(n, '.'); k >= 0 {
			n = n[k+1:]
		}
		lastSet[n] = struct{}{}
	}
	for nm := range byName {
		addLast(nm)
	}
	for nm := range alias {
		addLast(nm)
	}
	for nm := range extBy {
		addLast(nm)
	}
	lastOf := func(n string) string {
		if k := strings.LastIndexByte(n, '.'); k >= 0 {
			return n[k+1:]
		}
		return n
	}
	// for -dot: tree declarations by the last component of their name
	byLast := map[string][]int32{}
	if *flagDot > 0 {
		for nm, cs := range byName {
			byLast[lastOf(nm)] = append(byLast[lastOf(nm)], cs...)
		}
	}
	type hit struct {
		tree, ext int32
		via       bool
		more      []int32 // -dot: the other candidates, all taken
	}
	cache := map[int64]hit{}
	cacheFile := int32(-1)
	resolveTok := func(i int, t int32) hit {
		d := &decls[i]
		if d.file != cacheFile {
			cacheFile = d.file
			clear(cache)
		}
		key := int64(d.ctx)<<32 | int64(t)
		if h, ok := cache[key]; ok {
			return h
		}
		pre := ctxs[d.ctx]
		name := strings.TrimPrefix(toks.s[t], "_root_.")
		res := hit{-1, -1, false, nil}
		found := false
		if _, ok := lastSet[lastOf(name)]; ok {
			for _, p := range pre {
				full := name
				if ps := strs.s[p]; ps != "" {
					full = ps + "." + name
				}
				tr, ex, v := lookup(int32(i), full)
				if tr >= 0 || ex >= 0 {
					res, found = hit{tr, ex, v, nil}, true
					break
				}
				if _, ok := byName[full]; ok { // ambiguous, unsettled
					found = true
					break
				}
			}
		}
		if !found {
			// a generated name (Foo.ext, Foo.rec, Foo.eq_1, …): credit Foo
			if k := strings.LastIndexByte(name, '.'); k > 0 {
				base := name[:k]
				if _, ok := lastSet[lastOf(base)]; ok {
					for _, p := range pre {
						full := base
						if ps := strs.s[p]; ps != "" {
							full = ps + "." + base
						}
						if c, ok := byName[full]; ok {
							res = hit{pick(int32(i), c), -1, true, nil}
							break
						}
						if e, ok := extBy[full]; ok {
							res = hit{-1, e, true, nil}
							break
						}
					}
				}
			}
		}
		if !found && res.tree < 0 && res.ext < 0 && *flagDot > 0 {
			// dot notation on a local: `D.integral_forms_long` with `D : Data P`
			// names `Data.integral_forms_long`. The local's type is unknown to a
			// parse, so take the suffix after the first component and accept it
			// only if exactly one tree declaration ends with it.
			if k := strings.IndexByte(name, '.'); k > 0 && k < len(name)-1 {
				suf := name[k+1:]
				var hitc []int32
				for _, c := range byLast[lastOf(suf)] {
					if nm := decls[c].name; (nm == suf || strings.HasSuffix(nm, "."+suf)) && !(decls[c].private && decls[c].file != d.file) {
						hitc = append(hitc, c)
					}
				}
				if len(hitc) >= 1 && len(hitc) <= *flagDot {
					res = hit{hitc[0], -1, false, hitc[1:]}
					r.stats.ViaDot++
				}
			}
		}
		cache[key] = res
		return res
	}
	for i := range decls {
		d := &decls[i]
		if i%200000 == 0 {
			logf("resolving: %d / %d declarations", i, n)
		}
		seenT := map[int32]bool{int32(i): true}
		seenE := map[int32]bool{}
		for part := 0; part < 2; part++ {
			ts := d.sToks
			if part == 1 {
				ts = d.bToks
			}
			for _, t := range ts {
				r.stats.TokRefs++
				hr := resolveTok(i, t)
				for _, m := range hr.more {
					if !seenT[m] {
						seenT[m] = true
						r.stats.TreeEdges++
						if part == 0 {
							r.sUses[i] = append(r.sUses[i], m)
						} else {
							r.bUses[i] = append(r.bUses[i], m)
						}
						r.usedBy[m]++
					}
				}
				tree, ext, via := hr.tree, hr.ext, hr.via
				switch {
				case tree >= 0:
					if via {
						r.stats.ViaParent++
					}
					if !seenT[tree] {
						seenT[tree] = true
						r.stats.TreeEdges++
						if part == 0 {
							r.sUses[i] = append(r.sUses[i], tree)
						} else {
							r.bUses[i] = append(r.bUses[i], tree)
						}
						r.usedBy[tree]++
					}
				case ext >= 0:
					if via {
						r.stats.ViaParent++
					}
					if !seenE[ext] {
						seenE[ext] = true
						r.stats.ExtEdges++
						u, ok := extUsedIdx[ext]
						if !ok {
							u = int32(len(r.extList))
							extUsedIdx[ext] = u
							r.extList = append(r.extList, exts[ext])
						}
						if part == 0 {
							r.sExt[i] = append(r.sExt[i], u)
						} else {
							r.bExt[i] = append(r.bExt[i], u)
						}
					}
				default:
					r.stats.Unresolved++
				}
			}
		}
		d.sToks, d.bToks = nil, nil
	}
	r.stats.ExtUsed = len(r.extList)
	r.stats.Decls = n
	logf("resolved: %d tree edges, %d dependency edges, %d unresolved mentions, %d ambiguous (%d settled by imports)",
		r.stats.TreeEdges, r.stats.ExtEdges, r.stats.Unresolved, r.stats.Ambiguous, r.stats.AmbigByImports)

	// node order: by file path, then line
	r.order = make([]int32, n)
	for i := range r.order {
		r.order[i] = int32(i)
	}
	sort.Slice(r.order, func(a, b int) bool {
		da, db := &decls[r.order[a]], &decls[r.order[b]]
		if da.file != db.file {
			return files[da.file].path < files[db.file].path
		}
		return da.line < db.line
	})
	r.nodeOf = make([]int32, n)
	for id, di := range r.order {
		r.nodeOf[di] = int32(id)
	}
	// roots: the theorems of src/Main.lean
	for i := range decls {
		if files[decls[i].file].path == "src/Main.lean" {
			r.roots = append(r.roots, int32(i))
		}
	}
	sort.Slice(r.roots, func(a, b int) bool { return decls[r.roots[a]].line < decls[r.roots[b]].line })
	// reachability from the roots
	r.reach = make([]bool, n)
	stack := append([]int32{}, r.roots...)
	for _, x := range r.roots {
		r.reach[x] = true
	}
	for len(stack) > 0 {
		x := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		r.stats.Reachable++
		r.stats.ReachableLines += int64(decls[x].endLine - decls[x].line + 1)
		for _, ys := range [][]int32{r.sUses[x], r.bUses[x]} {
			for _, y := range ys {
				if !r.reach[y] {
					r.reach[y] = true
					stack = append(stack, y)
				}
			}
		}
	}
	sizes(r)
	// the roots' sizes exactly, by search (the sketch estimates them)
	for _, rt := range r.roots {
		seen := map[int32]bool{rt: true}
		st := []int32{rt}
		var ln int64
		for len(st) > 0 {
			x := st[len(st)-1]
			st = st[:len(st)-1]
			ln += int64(decls[x].endLine - decls[x].line + 1)
			for _, ys := range [][]int32{r.sUses[x], r.bUses[x]} {
				for _, y := range ys {
					if !seen[y] {
						seen[y] = true
						st = append(st, y)
					}
				}
			}
		}
		logf("root %s: %d declarations exactly (sketch said %d)", decls[rt].name, len(seen), r.subDecls[rt])
		r.subDecls[rt], r.subLines[rt], r.subExact[rt] = int64(len(seen)), ln, true
	}
	r.stats.ResolveSec = time.Since(t0).Seconds()
	return r
}

// ---------------------------------------------------------------- sizes

// mix is a bijection on uint64 (splitmix64's finaliser), so a sketch entry can
// be inverted back to the declaration it stands for.
func mix(x uint64) uint64 {
	x ^= x >> 30
	x *= 0xbf58476d1ce4e5b9
	x ^= x >> 27
	x *= 0x94d049bb133111eb
	x ^= x >> 31
	return x
}

func unmix(x uint64) uint64 {
	x ^= x>>31 ^ x>>62
	x *= 0x319642b2d24d8ec3
	x ^= x>>27 ^ x>>54
	x *= 0x96de1b173f119089
	x ^= x>>30 ^ x>>60
	return x
}

// sizes computes, for each declaration, the number of distinct declarations
// reachable from it (itself included) and their total source lines. Exact when
// fewer than k; otherwise a bottom-k estimate (relative error about 1/sqrt(k)).
func sizes(r *result) {
	n := len(decls)
	K := *flagSketchK
	adj := func(x int32) [2][]int32 { return [2][]int32{r.sUses[x], r.bUses[x]} }
	lines := func(x int32) int64 { return int64(decls[x].endLine - decls[x].line + 1) }
	// Tarjan, iterative
	index := make([]int32, n)
	low := make([]int32, n)
	onStack := make([]bool, n)
	for i := range index {
		index[i] = -1
	}
	comp := make([]int32, n)
	var compMembers [][]int32
	var st []int32
	type frame struct {
		v    int32
		part int
		ei   int
	}
	idx := int32(0)
	for s := 0; s < n; s++ {
		if index[s] >= 0 {
			continue
		}
		call := []frame{{v: int32(s)}}
		index[s], low[s] = idx, idx
		idx++
		st = append(st, int32(s))
		onStack[s] = true
		for len(call) > 0 {
			f := &call[len(call)-1]
			a := adj(f.v)
			if f.part < 2 && f.ei < len(a[f.part]) {
				w := a[f.part][f.ei]
				f.ei++
				if index[w] < 0 {
					index[w], low[w] = idx, idx
					idx++
					st = append(st, w)
					onStack[w] = true
					call = append(call, frame{v: w})
				} else if onStack[w] && index[w] < low[f.v] {
					low[f.v] = index[w]
				}
				continue
			}
			if f.part < 2 {
				f.part++
				f.ei = 0
				continue
			}
			v := f.v
			call = call[:len(call)-1]
			if len(call) > 0 {
				p := call[len(call)-1].v
				if low[v] < low[p] {
					low[p] = low[v]
				}
			}
			if low[v] == index[v] {
				c := int32(len(compMembers))
				var mem []int32
				for {
					w := st[len(st)-1]
					st = st[:len(st)-1]
					onStack[w] = false
					comp[w] = c
					mem = append(mem, w)
					if w == v {
						break
					}
				}
				compMembers = append(compMembers, mem)
			}
		}
	}
	// components come out in reverse topological order: successors first.
	nc := len(compMembers)
	parents := make([]int32, nc) // remaining predecessors, to free sketches
	for x := 0; x < n; x++ {
		for _, ys := range adj(int32(x)) {
			for _, y := range ys {
				if comp[y] != comp[x] {
					parents[comp[y]]++
				}
			}
		}
	}
	sk := make([][]uint64, nc)
	r.subDecls = make([]int64, n)
	r.subLines = make([]int64, n)
	r.subExact = make([]bool, n)
	buf := make([]uint64, 0, 4*K)
	for c := 0; c < nc; c++ {
		buf = buf[:0]
		for _, x := range compMembers[c] {
			buf = append(buf, mix(uint64(x)))
		}
		for _, x := range compMembers[c] {
			for _, ys := range adj(x) {
				for _, y := range ys {
					cy := comp[y]
					if cy == int32(c) {
						continue
					}
					buf = append(buf, sk[cy]...)
					parents[cy]--
					if parents[cy] == 0 {
						sk[cy] = nil
					}
					if len(buf) > 3*K {
						buf = bottomK(buf, K+1)
					}
				}
			}
		}
		buf = bottomK(buf, K+1)
		exact := len(buf) <= K
		var cnt int64
		var ln int64
		if exact {
			cnt = int64(len(buf))
			for _, hv := range buf {
				ln += lines(int32(unmix(hv)))
			}
		} else {
			kth := buf[K-1]
			frac := float64(kth) / 18446744073709551616.0
			est := float64(K-1) / frac
			var sl int64
			for _, hv := range buf[:K] {
				sl += lines(int32(unmix(hv)))
			}
			cnt = int64(est + 0.5)
			ln = int64(est*float64(sl)/float64(K) + 0.5)
		}
		for _, x := range compMembers[c] {
			r.subDecls[x], r.subLines[x], r.subExact[x] = cnt, ln, exact
		}
		if parents[c] > 0 {
			sk[c] = append([]uint64(nil), buf...)
		}
	}
}

// bottomK sorts, deduplicates and keeps the k smallest.
func bottomK(b []uint64, k int) []uint64 {
	sort.Slice(b, func(i, j int) bool { return b[i] < b[j] })
	out := b[:0]
	for i, v := range b {
		if i > 0 && v == b[i-1] {
			continue
		}
		out = append(out, v)
		if len(out) == k {
			break
		}
	}
	return out
}

// parallelParse streams a .tar.gz, parses the files keep accepts on all cores,
// and hands the results to consume in archive order (so the output does not
// depend on scheduling).
func parallelParse(walk func(fn func(name string, data []byte)) error, keep func(string, []byte) bool, keepText bool, consume func(string, pfile)) error {
	type job struct {
		seq  int
		name string
		data []byte
	}
	type res struct {
		seq  int
		name string
		pf   pfile
	}
	jobs := make(chan job, 256)
	results := make(chan res, 256)
	var wg sync.WaitGroup
	for w := 0; w < runtime.NumCPU(); w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := range jobs {
				results <- res{j.seq, j.name, parseFile(j.name, string(j.data), keepText)}
			}
		}()
	}
	done := make(chan struct{})
	go func() {
		pending := map[int]res{}
		next := 0
		for x := range results {
			pending[x.seq] = x
			for {
				y, ok := pending[next]
				if !ok {
					break
				}
				delete(pending, next)
				consume(y.name, y.pf)
				next++
			}
		}
		close(done)
	}()
	seq := 0
	err := walk(func(name string, data []byte) {
		if keep(name, data) {
			jobs <- job{seq, name, data}
			seq++
		}
	})
	close(jobs)
	wg.Wait()
	close(results)
	<-done
	return err
}
