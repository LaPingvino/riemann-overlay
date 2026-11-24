package main

import (
	"strings"
)

// A parsed declaration, before resolution.
type pdecl struct {
	name      string // full name, namespace applied
	kind      string
	line      int32 // first line (docstring or attribute included)
	declLine  int32 // line of the keyword
	endLine   int32
	doc       string
	stmt      string   // signature text, as written
	aliases   []string // fields / constructors (full names), which resolve to this decl
	private   bool     // visible from its own file only
	ctx       int      // index into the file's contexts
	stmtToks  []string // identifiers in the statement
	bodyToks  []string // identifiers in the body
}

type pfile struct {
	path    string
	module  string
	imports []string
	decls   []pdecl
	ctxs    [][]string // resolution prefixes, in priority order ("" = root)
	lines   int32
}

var declKinds = map[string]bool{
	"theorem": true, "lemma": true, "def": true, "abbrev": true, "instance": true,
	"structure": true, "class": true, "inductive": true, "axiom": true, "opaque": true,
	"example": true, "irreducible_def": true, "alias": true,
}

var modifiers = map[string]bool{
	"private": true, "protected": true, "noncomputable": true, "partial": true,
	"nonrec": true, "unsafe": true, "scoped": true, "local": true,
}

// col-0 words that start a new command (anything else at column 0 continues
// the previous one: `termination_by`, `where`, `|`, `deriving`, …)
var cmdStarts = map[string]bool{
	"namespace": true, "section": true, "end": true, "open": true, "variable": true,
	"universe": true, "import": true, "set_option": true, "notation": true,
	"infix": true, "infixl": true, "infixr": true, "prefix": true, "postfix": true,
	"macro": true, "syntax": true, "elab": true, "macro_rules": true, "elab_rules": true,
	"attribute": true, "mutual": true, "export": true, "deriving": true,
	"initialize": true, "builtin_initialize": true, "run_cmd": true, "run_elab": true,
	"add_decl_doc": true, "library_note": true, "assert_not_exists": true,
	"suppress_compilation": true, "omit": true, "include": true, "unseal": true,
	"seal": true, "simproc": true, "dsimproc": true, "compile_inductive": true,
	"declare_syntax_cat": true, "register_option": true, "variables": true,
}

func isCmdStart(t tok) bool {
	if t.col != 0 {
		return false
	}
	if t.s == "@[" || t.s == "#" {
		return true
	}
	if !t.id {
		return false
	}
	return declKinds[t.s] || modifiers[t.s] || cmdStarts[t.s] ||
		strings.HasPrefix(t.s, "register_") || t.s == "class" || t.s == "termination_by?"
}

type scope struct {
	kind  string // "namespace", "section", "mutual"
	parts int    // namespace components pushed
	opens []string
}

func joinNS(ns []string) string { return strings.Join(ns, ".") }

// parseFile turns one .lean source into declarations.
func parseFile(path, src string, keepText bool) pfile {
	toks, docs := lexFile(src)
	f := pfile{path: path, module: moduleOf(path)}
	f.lines = int32(strings.Count(src, "\n")) // as wc -l counts, and COMPARISON.md §3
	lines := strings.Split(src, "\n")

	var ns []string
	var scopes []scope
	ctxKey := map[string]int{}
	ctxFor := func(extraNS []string, local []string) int {
		var pre []string
		seen := map[string]bool{}
		add := func(p string) {
			if !seen[p] {
				seen[p] = true
				pre = append(pre, p)
			}
		}
		full := append(append([]string{}, ns...), extraNS...)
		for k := len(full); k >= 0; k-- {
			add(joinNS(full[:k]))
		}
		addOpen := func(o string) {
			for k := len(ns); k >= 0; k-- {
				if k == 0 {
					add(o)
				} else {
					add(joinNS(ns[:k]) + "." + o)
				}
			}
		}
		for _, s := range scopes {
			for _, o := range s.opens {
				addOpen(o)
			}
		}
		for _, o := range local {
			addOpen(o)
		}
		key := strings.Join(pre, "\x00")
		if c, ok := ctxKey[key]; ok {
			return c
		}
		ctxKey[key] = len(f.ctxs)
		f.ctxs = append(f.ctxs, pre)
		return len(f.ctxs) - 1
	}

	// split tokens into commands
	var starts []int
	for i, t := range toks {
		if i == 0 || isCmdStart(t) {
			// `@[simp]`, `private`, `open X in` on their own line belong to the
			// declaration on the next line
			if len(starts) > 0 && prefixOnly(toks[starts[len(starts)-1]:i]) {
				continue
			}
			starts = append(starts, i)
		}
	}
	di := 0 // docstring cursor
	for ci, s := range starts {
		e := len(toks)
		if ci+1 < len(starts) {
			e = starts[ci+1]
		}
		cmd := toks[s:e]
		if len(cmd) == 0 {
			continue
		}
		cmdLine := cmd[0].line
		endLine := cmd[len(cmd)-1].line
		// the docstring immediately before this command (after the previous one)
		var doc *docstr
		prevLast := int32(0)
		if s > 0 {
			prevLast = toks[s-1].line
		}
		for di < len(docs) && docs[di].endLine <= cmdLine {
			if docs[di].startLine >= prevLast {
				dd := docs[di]
				doc = &dd
			}
			di++
		}
		// strip attributes, modifiers, `set_option … in`, `open … in`
		j := 0
		var localOpens []string
		isPrivate := false
		for j < len(cmd) {
			t := cmd[j]
			if t.s == "@[" {
				depth := 1
				j++
				for j < len(cmd) && depth > 0 {
					if cmd[j].s == "[" || cmd[j].s == "@[" {
						depth++
					} else if cmd[j].s == "]" {
						depth--
					}
					j++
				}
				continue
			}
			if t.id && modifiers[t.s] {
				if t.s == "private" {
					isPrivate = true
				}
				j++
				continue
			}
			if t.id && t.s == "set_option" {
				// set_option name value in
				k := j + 1
				for k < len(cmd) && cmd[k].line == t.line && !(cmd[k].id && cmd[k].s == "in") {
					k++
				}
				if k < len(cmd) && cmd[k].s == "in" {
					j = k + 1
					continue
				}
				break
			}
			if t.id && t.s == "open" {
				k := j + 1
				var os []string
				depth := 0
				for k < len(cmd) && !(cmd[k].id && cmd[k].s == "in" && depth == 0) {
					if cmd[k].line != t.line && depth == 0 {
						break
					}
					if cmd[k].s == "(" {
						depth++
					} else if cmd[k].s == ")" {
						depth--
					} else if cmd[k].id && depth == 0 && cmd[k].s != "scoped" {
						if cmd[k].s == "hiding" || cmd[k].s == "renaming" {
							for k < len(cmd) && cmd[k].line == t.line && cmd[k].s != "in" {
								k++
							}
							break
						}
						os = append(os, cmd[k].s)
					}
					k++
				}
				if k < len(cmd) && cmd[k].s == "in" {
					localOpens = append(localOpens, os...)
					j = k + 1
					continue
				}
				// a plain `open`: applies to the enclosing scope
				if len(scopes) == 0 {
					scopes = append(scopes, scope{kind: "file"})
				}
				scopes[len(scopes)-1].opens = append(scopes[len(scopes)-1].opens, os...)
				j = len(cmd)
				break
			}
			break
		}
		if j >= len(cmd) {
			continue
		}
		head := cmd[j]
		if !head.id {
			continue
		}
		switch head.s {
		case "import":
			for _, t := range cmd[j+1:] {
				if t.id {
					f.imports = append(f.imports, t.s)
				}
			}
			continue
		case "namespace":
			if j+1 < len(cmd) && cmd[j+1].id {
				parts := strings.Split(cmd[j+1].s, ".")
				ns = append(ns, parts...)
				scopes = append(scopes, scope{kind: "namespace", parts: len(parts)})
			}
			continue
		case "section", "mutual":
			scopes = append(scopes, scope{kind: head.s})
			continue
		case "noncomputable":
			continue
		case "end":
			// pop the innermost non-file scope
			for k := len(scopes) - 1; k >= 0; k-- {
				if scopes[k].kind == "file" {
					continue
				}
				ns = ns[:len(ns)-scopes[k].parts]
				scopes = append(scopes[:k], scopes[k+1:]...)
				break
			}
			continue
		}
		kind := head.s
		if kind == "class" && j+1 < len(cmd) && cmd[j+1].s == "inductive" {
			kind = "class inductive"
			j++
		}
		if !declKinds[head.s] {
			continue
		}
		if kind == "example" {
			continue
		}
		d := pdecl{kind: kind, declLine: head.line, line: cmdLine, endLine: endLine, private: isPrivate}
		if kind == "lemma" {
			d.kind = "theorem"
		}
		if doc != nil {
			d.doc = doc.text
			if doc.startLine < d.line {
				d.line = doc.startLine
			}
		}
		k := j + 1
		var short string
		if k < len(cmd) && cmd[k].id && !(kind == "instance" && cmd[k].s == "priority") {
			short = cmd[k].s
			k++
		}
		if short == "" {
			if kind != "instance" {
				continue
			}
			short = "instance@" + itoa(int(head.line))
			k = j + 1
		}
		var declNS []string
		if strings.HasPrefix(short, "_root_.") {
			short = strings.TrimPrefix(short, "_root_.")
			d.name = short
		} else if len(ns) > 0 {
			d.name = joinNS(ns) + "." + short
		} else {
			d.name = short
		}
		if p := strings.LastIndex(short, "."); p > 0 {
			declNS = strings.Split(short[:p], ".")
		}
		// statement: up to the first depth-0 `:=`, `where`, or line-initial `|`
		depth := 0
		stmtEnd := len(cmd)
		for m := k; m < len(cmd); m++ {
			t := cmd[m]
			switch t.s {
			case "(", "[", "{", "⟨", "⦃", "@[":
				depth++
			case ")", "]", "}", "⟩", "⦄":
				depth--
			}
			if depth <= 0 && (t.s == ":=" || (t.id && t.s == "where") || (t.s == "|" && m > 0 && cmd[m-1].line != t.line)) {
				stmtEnd = m
				break
			}
		}
		if keepText {
			last := cmd[len(cmd)-1]
			if stmtEnd < len(cmd) {
				last = cmd[stmtEnd]
			}
			d.stmt = sliceText(lines, head.line, head.col, last.line, last.col, stmtEnd < len(cmd))
		} else {
			d.doc = ""
		}
		// aliases: structure fields and inductive constructors
		if (kind == "structure" || kind == "class" || kind == "inductive" || kind == "class inductive") && stmtEnd < len(cmd) {
			for m := stmtEnd; m < len(cmd); m++ {
				t := cmd[m]
				if t.s == "|" && m+1 < len(cmd) && cmd[m+1].id {
					d.aliases = append(d.aliases, d.name+"."+cmd[m+1].s)
				}
				if t.id && m > 0 && cmd[m-1].line != t.line && m+1 < len(cmd) && (cmd[m+1].s == ":" || cmd[m+1].s == "::" || cmd[m+1].s == ":=" || cmd[m+1].s == "(" || cmd[m+1].s == "{" || cmd[m+1].s == "[") {
					if t.s != "deriving" && t.s != "where" && t.s != "extends" {
						d.aliases = append(d.aliases, d.name+"."+t.s)
					}
				}
				if t.s == "(" && m > 0 && cmd[m-1].line != t.line && m+1 < len(cmd) && cmd[m+1].id {
					d.aliases = append(d.aliases, d.name+"."+cmd[m+1].s)
				}
			}
			d.aliases = append(d.aliases, d.name+".mk")
		}
		d.ctx = ctxFor(declNS, localOpens)
		seen := map[string]bool{}
		for m := k; m < len(cmd); m++ {
			t := cmd[m]
			if !t.id || t.dot || seen[t.s] || keywords[t.s] {
				continue
			}
			seen[t.s] = true
			if m < stmtEnd {
				d.stmtToks = append(d.stmtToks, t.s)
			} else {
				d.bodyToks = append(d.bodyToks, t.s)
			}
		}
		f.decls = append(f.decls, d)
	}
	return f
}

func sliceText(lines []string, l1, c1, l2, c2 int32, exclusive bool) string {
	if int(l1) > len(lines) || l1 < 1 {
		return ""
	}
	var b strings.Builder
	for l := l1; l <= l2 && int(l) <= len(lines); l++ {
		r := []rune(lines[l-1])
		from, to := 0, len(r)
		if l == l1 {
			from = int(c1)
		}
		if l == l2 && exclusive {
			to = int(c2)
		}
		if from > len(r) {
			from = len(r)
		}
		if to > len(r) {
			to = len(r)
		}
		if to < from {
			to = from
		}
		b.WriteString(string(r[from:to]))
		if l < l2 {
			b.WriteByte('\n')
		}
		if b.Len() > 6000 {
			b.WriteString(" …")
			break
		}
	}
	return strings.TrimRight(b.String(), " \n\t")
}

func moduleOf(path string) string {
	p := strings.TrimSuffix(path, ".lean")
	for _, pre := range []string{"lean/src/", "src/"} {
		if strings.HasPrefix(p, pre) {
			p = p[len(pre):]
			break
		}
	}
	return strings.ReplaceAll(p, "/", ".")
}

func itoa(i int) string {
	if i == 0 {
		return "0"
	}
	var b [20]byte
	p := len(b)
	neg := i < 0
	if neg {
		i = -i
	}
	for i > 0 {
		p--
		b[p] = byte('0' + i%10)
		i /= 10
	}
	if neg {
		p--
		b[p] = '-'
	}
	return string(b[p:])
}

var keywords = map[string]bool{}

func init() {
	for _, w := range strings.Fields(`fun λ have show by let in if then else match with do at from
		Type Sort Prop theorem lemma def where calc suffices obtain using exact intro intros
		rfl simp rw rwa simpa apply refine constructor cases rcases induction omega linarith
		nlinarith positivity norm_num ring field_simp push_cast exact_mod_cast gcongr
		this true false True False fun_prop decide aesop tauto use exists left right
		ext funext congr unfold dsimp change specialize subst contradiction exfalso trivial
		assumption all_goals any_goals first repeat try sorry termination_by decreasing_by
		deriving instance structure class inductive extends mut return for unless`) {
		keywords[w] = true
	}
}

// prefixOnly reports whether seq is nothing but attributes, modifiers and
// `set_option … in` / `open … in` prefixes.
func prefixOnly(seq []tok) bool {
	j := 0
	for j < len(seq) {
		t := seq[j]
		switch {
		case t.s == "@[":
			depth := 1
			j++
			for j < len(seq) && depth > 0 {
				if seq[j].s == "[" || seq[j].s == "@[" {
					depth++
				} else if seq[j].s == "]" {
					depth--
				}
				j++
			}
			if depth > 0 {
				return true // attribute still open: keep going
			}
		case t.id && modifiers[t.s]:
			j++
		case t.id && (t.s == "set_option" || t.s == "open"):
			k := j + 1
			for k < len(seq) && !(seq[k].id && seq[k].s == "in") {
				k++
			}
			if k >= len(seq) {
				return false
			}
			j = k + 1
		default:
			return false
		}
	}
	return len(seq) > 0
}
