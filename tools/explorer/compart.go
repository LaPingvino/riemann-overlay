package main

// The fractal compartment map, c.json (SESSION 447).
//
// A hand-written spec (JSON) names the top levels — compartments and their
// sub-compartments — each with a plain-language summary and the path prefixes
// of the files it holds. Everything below the spec is generated: a file goes to
// the spec node with the longest matching prefix, and under that node the
// generator adds one node per directory and one per file, so the map zooms from
// the five theorems down to a file, whose declarations link into the node view.
//
// Every node carries its own size (files, lines, bytes, declarations, and how
// many of those the parsed cone of the five theorems reaches) and its CONE: the
// files it transitively imports inside the tree, i.e. what a reader or a build
// needs besides Mathlib to check that node alone. Tokens are bytes/4, a rough
// rule stated in the data, not a tokenizer's count.
//
// Edges between nodes are module imports (exact, read from the import lines),
// counted at the node's own depth. Declaration-level membership is the parsed
// reach of resolve() — [parsed], like every edge of the explorer.

import (
	"encoding/json"
	"os"
	"sort"
	"strings"
)

type compSpec struct {
	ID       string     `json:"id"`
	Title    string     `json:"title"`
	Summary  string     `json:"summary"`
	Align    string     `json:"align,omitempty"`
	Prefixes []string   `json:"prefixes,omitempty"`
	Children []compSpec `json:"children,omitempty"`
}

type compSize struct {
	Files      int   `json:"files"`
	Lines      int64 `json:"lines"`
	Bytes      int64 `json:"bytes"`
	Tokens     int64 `json:"tokens"`
	Decls      int64 `json:"decls"`
	Reach      int64 `json:"reach"`      // declarations in the parsed cone of the five theorems
	ReachLines int64 `json:"reachLines"` // their source lines
}

type compNode struct {
	ID       string   `json:"id"`
	Parent   int      `json:"parent"`
	Depth    int      `json:"depth"`
	Kind     string   `json:"kind"` // root | spec | dir | file
	Title    string   `json:"title"`
	Summary  string   `json:"summary,omitempty"`
	Align    string   `json:"align,omitempty"`
	Path     string   `json:"path,omitempty"`
	Children []int    `json:"children,omitempty"`
	Size     compSize `json:"size"`
	Cone     compSize `json:"cone"`             // transitive in-tree imports, the node's own files included
	Uses     [][2]int `json:"uses,omitempty"`   // [node at this depth, import lines into it]
	UsedBy   [][2]int `json:"usedBy,omitempty"` // the same, inward
	Decls    []int32  `json:"decls,omitempty"`  // file nodes: node ids of its declarations
	files    []int32
}

type compRoot struct {
	Node   int32    `json:"node"` // declaration node id
	Name   string   `json:"name"`
	Decls  int      `json:"decls"`
	Lines  int64    `json:"lines"`
	Tokens int64    `json:"tokens"` // ≈ declaration lines × the bytes per line of their files / 4
	ByComp [][2]int `json:"byComp"` // [top-level node, declarations of the cone in it]
}

type compMap struct {
	Rule  string     `json:"rule"`
	Nodes []compNode `json:"nodes"`
	Roots []compRoot `json:"roots"`
}

func buildCompartments(r *result, specPath string) *compMap {
	raw, err := os.ReadFile(specPath)
	if err != nil {
		fatal("compartments: %v", err)
	}
	var spec compSpec
	if err := json.Unmarshal(raw, &spec); err != nil {
		fatal("compartments %s: %v", specPath, err)
	}
	cm := &compMap{Rule: "tokens ≈ bytes / 4 (a rough rule, not a tokenizer); lines as wc -l counts; edges are module imports"}
	type pre struct {
		p    string
		node int
	}
	var pres []pre
	var add func(s compSpec, parent, depth int) int
	add = func(s compSpec, parent, depth int) int {
		kind := "spec"
		if parent < 0 {
			kind = "root"
		}
		i := len(cm.Nodes)
		cm.Nodes = append(cm.Nodes, compNode{ID: s.ID, Parent: parent, Depth: depth, Kind: kind, Title: s.Title, Summary: s.Summary, Align: s.Align})
		for _, p := range s.Prefixes {
			pres = append(pres, pre{p, i})
		}
		for _, c := range s.Children {
			k := add(c, i, depth+1)
			cm.Nodes[i].Children = append(cm.Nodes[i].Children, k)
		}
		return i
	}
	add(spec, -1, 0)
	sort.Slice(pres, func(a, b int) bool { return len(pres[a].p) > len(pres[b].p) })

	// files -> nodes, with generated directory and file nodes below the spec
	byKey := map[string]int{}
	child := func(parent int, key, kind, title, path string) int {
		k := cm.Nodes[parent].ID + "/" + key
		if path != "" { // two prefixes can end in files of one name (src/Main.lean, src/New/Main.lean)
			k = cm.Nodes[parent].ID + ":" + path
		}
		if i, ok := byKey[k]; ok {
			return i
		}
		i := len(cm.Nodes)
		cm.Nodes = append(cm.Nodes, compNode{ID: k, Parent: parent, Depth: cm.Nodes[parent].Depth + 1, Kind: kind, Title: title, Path: path})
		cm.Nodes[parent].Children = append(cm.Nodes[parent].Children, i)
		byKey[k] = i
		return i
	}
	fileNode := make([]int, len(files))
	unassigned := -1
	for fi := range files {
		path := files[fi].path
		at, rest := -1, ""
		for _, p := range pres {
			if strings.HasPrefix(path, p.p) {
				at, rest = p.node, strings.TrimPrefix(path[len(p.p):], "/")
				break
			}
		}
		if at < 0 {
			if unassigned < 0 {
				unassigned = child(0, "unassigned", "spec", "Not in any compartment of the spec", "")
				cm.Nodes[unassigned].Summary = "Files the spec's prefixes do not cover."
			}
			at, rest = unassigned, path
			logf("compartments: %s matches no prefix", path)
		}
		if rest == "" { // the prefix named the file itself
			rest = path[strings.LastIndexByte(path, '/')+1:]
		}
		parts := strings.Split(rest, "/")
		cur := at
		dirPath := strings.TrimSuffix(path, rest)
		for _, d := range parts[:len(parts)-1] {
			dirPath += d + "/"
			cur = child(cur, d, "dir", d+"/", dirPath)
		}
		leaf := child(cur, parts[len(parts)-1], "file", strings.TrimSuffix(parts[len(parts)-1], ".lean"), path)
		cm.Nodes[leaf].Summary = files[fi].heading // the file's own title, from its module docstring
		cm.Nodes[leaf].files = []int32{int32(fi)}
		fileNode[fi] = leaf
	}

	// a directory's summary: the titles of the files directly in it
	for i := range cm.Nodes {
		n := &cm.Nodes[i]
		if n.Kind != "dir" {
			continue
		}
		var ts []string
		for _, ch := range n.Children {
			if t := cm.Nodes[ch].Summary; cm.Nodes[ch].Kind == "file" && t != "" {
				ts = append(ts, t)
			}
		}
		if len(ts) > 0 {
			n.Summary = "Its files, by their own titles: " + strings.Join(ts, "; ") + "."
		}
	}

	// declarations of each file, and per-file reach
	perFile := make([][]int32, len(files))
	reachN := make([]int64, len(files))
	reachL := make([]int64, len(files))
	for di := range decls {
		d := &decls[di]
		perFile[d.file] = append(perFile[d.file], int32(di))
		if r.reach[di] {
			reachN[d.file]++
			reachL[d.file] += int64(d.endLine - d.line + 1)
		}
	}
	for fi, ds := range perFile {
		sort.Slice(ds, func(a, b int) bool { return decls[ds[a]].line < decls[ds[b]].line })
		ids := make([]int32, len(ds))
		for i, di := range ds {
			ids[i] = r.nodeOf[di]
		}
		cm.Nodes[fileNode[fi]].Decls = ids
	}

	// files of every node (post-order: children before parents)
	var collect func(i int) []int32
	collect = func(i int) []int32 {
		fs := append([]int32(nil), cm.Nodes[i].files...)
		for _, c := range cm.Nodes[i].Children {
			fs = append(fs, collect(c)...)
		}
		cm.Nodes[i].files = fs
		return fs
	}
	collect(0)

	// in-tree import closure of every file, as bitsets
	modFile := map[string]int32{}
	for i, f := range files {
		modFile[f.module] = int32(i)
	}
	W := (len(files) + 63) / 64
	closure := make([][]uint64, len(files))
	state := make([]uint8, len(files))
	var clo func(fi int32) []uint64
	clo = func(fi int32) []uint64 {
		if state[fi] == 2 {
			return closure[fi]
		}
		b := make([]uint64, W)
		b[fi/64] |= 1 << (fi % 64)
		if state[fi] == 1 { // an import cycle cannot compile; do not loop on one
			return b
		}
		state[fi] = 1
		for _, im := range files[fi].imports {
			if j, ok := modFile[im]; ok {
				for k, w := range clo(j) {
					b[k] |= w
				}
			}
		}
		closure[fi], state[fi] = b, 2
		return b
	}
	sizeOf := func(fs []int32) compSize {
		var s compSize
		for _, fi := range fs {
			f := &files[fi]
			s.Files++
			s.Lines += int64(f.lines)
			s.Bytes += f.bytes
			s.Decls += int64(f.ndecls)
			s.Reach += reachN[fi]
			s.ReachLines += reachL[fi]
		}
		s.Tokens = s.Bytes / 4
		return s
	}
	for i := range cm.Nodes {
		n := &cm.Nodes[i]
		n.Size = sizeOf(n.files)
		b := make([]uint64, W)
		for _, fi := range n.files {
			for k, w := range clo(fi) {
				b[k] |= w
			}
		}
		var cone []int32
		for k, w := range b {
			for w != 0 {
				t := trailingZeros(w)
				cone = append(cone, int32(k*64+t))
				w &= w - 1
			}
		}
		n.Cone = sizeOf(cone)
	}

	// import edges, at each node's own depth
	ancAt := func(node, depth int) int {
		for node >= 0 && cm.Nodes[node].Depth > depth {
			node = cm.Nodes[node].Parent
		}
		if node >= 0 && cm.Nodes[node].Depth == depth {
			return node
		}
		return -1
	}
	maxDepth := 0
	for _, n := range cm.Nodes {
		if n.Depth > maxDepth {
			maxDepth = n.Depth
		}
	}
	for depth := 1; depth <= maxDepth; depth++ {
		uses := map[[2]int]int{}
		for fi := range files {
			a := ancAt(fileNode[fi], depth)
			if a < 0 {
				continue
			}
			for _, im := range files[fi].imports {
				j, ok := modFile[im]
				if !ok {
					continue
				}
				b := ancAt(fileNode[j], depth)
				if b >= 0 && b != a && cm.Nodes[b].Parent == cm.Nodes[a].Parent {
					uses[[2]int{a, b}]++
				}
			}
		}
		for e, c := range uses {
			cm.Nodes[e[0]].Uses = append(cm.Nodes[e[0]].Uses, [2]int{e[1], c})
			cm.Nodes[e[1]].UsedBy = append(cm.Nodes[e[1]].UsedBy, [2]int{e[0], c})
		}
	}
	for i := range cm.Nodes {
		n := &cm.Nodes[i]
		sort.Slice(n.Uses, func(a, b int) bool { u, v := n.Uses[a], n.Uses[b]; return u[1] > v[1] || u[1] == v[1] && u[0] < v[0] })
		sort.Slice(n.UsedBy, func(a, b int) bool {
			u, v := n.UsedBy[a], n.UsedBy[b]
			return u[1] > v[1] || u[1] == v[1] && u[0] < v[0]
		})
		ch := n.Children
		sort.SliceStable(ch, func(a, b int) bool {
			ka, kb := cm.Nodes[ch[a]].Kind, cm.Nodes[ch[b]].Kind
			if (ka == "spec") != (kb == "spec") {
				return ka == "spec"
			}
			if ka == "spec" {
				return false // spec order is the author's order
			}
			return cm.Nodes[ch[a]].Size.Lines > cm.Nodes[ch[b]].Size.Lines
		})
	}

	// the five theorems: each one's parsed declaration cone
	for _, rt := range r.roots {
		seen := map[int32]bool{rt: true}
		st := []int32{rt}
		var ln int64
		var by float64
		count := map[int]int{}
		for len(st) > 0 {
			x := st[len(st)-1]
			st = st[:len(st)-1]
			d := &decls[x]
			l := int64(d.endLine - d.line + 1)
			ln += l
			f := &files[d.file]
			if f.lines > 0 {
				by += float64(l) * float64(f.bytes) / float64(f.lines)
			}
			if a := ancAt(fileNode[d.file], 1); a >= 0 {
				count[a]++
			}
			for _, ys := range [][]int32{r.sUses[x], r.bUses[x]} {
				for _, y := range ys {
					if !seen[y] {
						seen[y] = true
						st = append(st, y)
					}
				}
			}
		}
		cr := compRoot{Node: r.nodeOf[rt], Name: decls[rt].name, Decls: len(seen), Lines: ln, Tokens: int64(by / 4)}
		for a, c := range count {
			cr.ByComp = append(cr.ByComp, [2]int{a, c})
		}
		sort.Slice(cr.ByComp, func(a, b int) bool {
			u, v := cr.ByComp[a], cr.ByComp[b]
			return u[1] > v[1] || u[1] == v[1] && u[0] < v[0]
		})
		cm.Roots = append(cm.Roots, cr)
	}
	for i := range cm.Nodes {
		cm.Nodes[i].files = nil
	}
	logf("compartments: %d nodes (%d from the spec), %d roots", len(cm.Nodes), len(pres), len(cm.Roots))
	return cm
}

func trailingZeros(w uint64) int {
	n := 0
	for w&1 == 0 {
		w >>= 1
		n++
	}
	return n
}
