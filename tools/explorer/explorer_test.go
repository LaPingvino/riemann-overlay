package main

import (
	"strings"
	"testing"
)

func TestMixInverts(t *testing.T) {
	for _, x := range []uint64{0, 1, 2, 12345, 1 << 40, ^uint64(0)} {
		if unmix(mix(x)) != x {
			t.Fatalf("unmix(mix(%d)) = %d", x, unmix(mix(x)))
		}
	}
}

const sample = `import Mathlib
import Foo.Bar

/-! module doc mentioning fake_name -/

open Complex DirichletCharacter

namespace Formalism.VW

/-- The doc of every. -/
@[simp]
theorem rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis := by
  -- a comment naming ghost_lemma
  exact helper h "string with fake_name"

private lemma helper {x : ℕ} (h : P) : Q x := h.trans (inner_lemma x)

structure Box where
  lo : ℝ
  hi : ℝ

end Formalism.VW

open Foo in
theorem _root_.top (n : ℕ) : n = n := Formalism.VW.Box.lo rfl

instance : Inhabited ℕ := ⟨0⟩
`

func TestParseSample(t *testing.T) {
	f := parseFile("lean/src/X/Y.lean", sample, true)
	if f.module != "X.Y" {
		t.Errorf("module %q", f.module)
	}
	if strings.Join(f.imports, ",") != "Mathlib,Foo.Bar" {
		t.Errorf("imports %v", f.imports)
	}
	var names []string
	for _, d := range f.decls {
		names = append(names, d.kind+" "+d.name)
	}
	want := "theorem Formalism.VW.rh_of_every|theorem Formalism.VW.helper|structure Formalism.VW.Box|theorem top|instance instance@27"
	if strings.Join(names, "|") != want {
		t.Fatalf("decls\n got %s\nwant %s", strings.Join(names, "|"), want)
	}
	d := f.decls[0]
	if d.doc != "The doc of every." || d.line != 10 || d.declLine != 12 {
		t.Errorf("doc/line: %q %d %d", d.doc, d.line, d.declLine)
	}
	if d.stmt != "theorem rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis" {
		t.Errorf("stmt %q", d.stmt)
	}
	all := strings.Join(append(d.stmtToks, d.bodyToks...), " ")
	for _, bad := range []string{"ghost_lemma", "fake_name"} {
		if strings.Contains(all, bad) {
			t.Errorf("comment/string leaked: %s in %s", bad, all)
		}
	}
	if !strings.Contains(strings.Join(d.bodyToks, " "), "helper") {
		t.Errorf("body tokens %v", d.bodyToks)
	}
	if strings.Contains(strings.Join(f.decls[1].bodyToks, " "), " trans") {
		t.Errorf("dot notation should not yield a bare token: %v", f.decls[1].bodyToks)
	}
	if strings.Join(f.decls[2].aliases, ",") != "Formalism.VW.Box.lo,Formalism.VW.Box.hi,Formalism.VW.Box.mk" {
		t.Errorf("aliases %v", f.decls[2].aliases)
	}
	ctx := f.ctxs[f.decls[0].ctx]
	if strings.Join(ctx[:3], ",") != "Formalism.VW,Formalism," || !contains(ctx, "Complex") {
		t.Errorf("ctx %q", ctx)
	}
	if !contains(f.ctxs[f.decls[3].ctx], "Foo") {
		t.Errorf("open … in not applied: %q", f.ctxs[f.decls[3].ctx])
	}
	if contains(f.ctxs[f.decls[4].ctx], "Foo") {
		t.Errorf("open … in leaked: %q", f.ctxs[f.decls[4].ctx])
	}
}

func contains(xs []string, s string) bool {
	for _, x := range xs {
		if x == s {
			return true
		}
	}
	return false
}
