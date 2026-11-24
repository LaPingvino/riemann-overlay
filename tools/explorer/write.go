package main

import (
	"bufio"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"
)

const extShard = 2000

// searchKey is the bucket a name component falls in: its first two runes,
// lower-cased, hex-encoded (the viewer computes the same thing).
func searchKey(s string) string {
	var b []byte
	k := 0
	for _, r := range s {
		if k == 2 {
			break
		}
		r = unicode.ToLower(r)
		var tmp [4]byte
		n := utf8.EncodeRune(tmp[:], r)
		b = append(b, tmp[:n]...)
		k++
	}
	return hex.EncodeToString(b)
}

func writeJSON(path string, v any) int64 {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		fatal("%v", err)
	}
	f, err := os.Create(path)
	if err != nil {
		fatal("%v", err)
	}
	w := bufio.NewWriter(f)
	enc := json.NewEncoder(w)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(v); err != nil {
		fatal("%s: %v", path, err)
	}
	w.Flush()
	st, _ := f.Stat()
	f.Close()
	return st.Size()
}

func write(r *result, toolchain string) {
	out := *flagOut
	for _, sub := range []string{"n", "x", "s"} {
		os.RemoveAll(filepath.Join(out, sub))
	}
	var total int64
	S := *flagShard
	n := len(r.order)
	nShards := (n + S - 1) / S
	ids := func(xs []int32) []int32 {
		o := make([]int32, len(xs))
		for i, x := range xs {
			o[i] = r.nodeOf[x]
		}
		sort.Slice(o, func(a, b int) bool { return o[a] < o[b] })
		return o
	}
	for s := 0; s < nShards; s++ {
		var paths []string
		pidx := map[int32]int{}
		var rows [][]any
		for id := s * S; id < (s+1)*S && id < n; id++ {
			di := r.order[id]
			d := &decls[di]
			pi, ok := pidx[d.file]
			if !ok {
				pi = len(paths)
				pidx[d.file] = pi
				paths = append(paths, files[d.file].path)
			}
			exact, reach := 0, 0
			if r.subExact[di] {
				exact = 1
			}
			if r.reach[di] {
				reach = 1
			}
			row := []any{d.name, d.kind, pi, d.line, d.declLine, d.endLine,
				ids(r.sUses[di]), ids(r.bUses[di]), r.sExt[di], r.bExt[di],
				r.usedBy[di], r.subDecls[di], r.subLines[di], exact, reach}
			if *flagStmts {
				row = append(row, d.stmt, d.doc)
			}
			rows = append(rows, row)
		}
		total += writeJSON(filepath.Join(out, "n", itoa(s)+".json"), map[string]any{"f": paths, "d": rows})
	}
	nx := len(r.extList)
	for s := 0; s*extShard < nx; s++ {
		var rows [][]any
		for i := s * extShard; i < (s+1)*extShard && i < nx; i++ {
			e := r.extList[i]
			rows = append(rows, []any{e.name, e.lib, extFiles[e.file], e.line})
		}
		total += writeJSON(filepath.Join(out, "x", itoa(s)+".json"), rows)
	}
	// search buckets: every declaration under the key of each component of its
	// name, so "VW", "rh_of" and "Formalism.VW.rh" all land in a bucket that
	// holds Formalism.VW.rh_of_every.
	buckets := map[string][][]any{}
	for id := 0; id < n; id++ {
		d := &decls[r.order[id]]
		seen := map[string]bool{}
		for _, comp := range strings.Split(d.name, ".") {
			k := searchKey(comp)
			if k == "" || seen[k] {
				continue
			}
			seen[k] = true
			reach := 0
			if r.reach[r.order[id]] {
				reach = 1
			}
			buckets[k] = append(buckets[k], []any{d.name, id, reach})
		}
	}
	var bsizes []int64
	for k, rows := range buckets {
		sz := writeJSON(filepath.Join(out, "s", k+".json"), rows)
		bsizes = append(bsizes, sz)
		total += sz
	}
	sort.Slice(bsizes, func(a, b int) bool { return bsizes[a] > bsizes[b] })
	roots := make([]int32, len(r.roots))
	for i, x := range r.roots {
		roots[i] = r.nodeOf[x]
	}
	meta := map[string]any{
		"generated": time.Now().UTC().Format(time.RFC3339),
		"release": map[string]any{
			"urls":   *flagURL + "01 … " + itoa(*flagNParts),
			"sha256": releaseSHA,
			"note":   "https://alpo.ge/remark.pdf",
			"site":   "https://alpo.ge/",
		},
		"toolchain":  toolchain,
		"libs":       r.libs,
		"stats":      r.stats,
		"roots":      roots,
		"shard":      S,
		"nodes":      n,
		"extShard":   extShard,
		"extNodes":   nx,
		"statements": *flagStmts,
		"edges":      "parsed",
		"sketchK":    *flagSketchK,
		"licence":    "The release tarball carries no LICENSE or README (its only non-.lean files are lake-manifest.json, lakefile.toml and lean-toolchain). Statements and docstrings are therefore left out of this data; the generator's -statements flag switches them on.",
	}
	total += writeJSON(filepath.Join(out, "meta.json"), meta)
	big := int64(0)
	if len(bsizes) > 0 {
		big = bsizes[0]
	}
	logf("wrote %s: %d node shards, %d dependency shards, %d search buckets (largest %d KB), %.1f MB total",
		out, nShards, (nx+extShard-1)/extShard, len(buckets), big>>10, float64(total)/1e6)
}
