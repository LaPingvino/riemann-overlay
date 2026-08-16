/-
# The zeta family, constructed (discharging `axiom zetaFamily`)

`ofMult` asked for four things: a finite zero set in the window, a
multiplicity function, closure under `ρ ↦ 1 − conj ρ`, and invariance of the
multiplicity under it.  All four are theorems in `zeta-23-lean`:

* `Zeta23.zerosIn_finite`   — every ordinate window holds finitely many zeros;
* `Zeta23.zeroMult`         — multiplicity via Mathlib's `analyticOrderAt`;
* `Zeta23.zeta_reflect_zero`— `ρ ↦ 1 − conj ρ` maps nontrivial zeros to zeros;
* `Zeta23.zeta_mult_reflect`— and preserves their multiplicity.

`Zeta23.reflect ρ = 1 − conj ρ` is our `Riemann.refl` in `(β, γ)` coordinates.
-/
import Riemann.Gaps
import Zeta23.Statement.SeamClosed
import Zeta23.ZetaReflect

namespace Riemann

open Zeta23

/-- `(β, γ) ↦ β + iγ`, the inverse of the coordinates `ZeroData` uses. -/
noncomputable def toC (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

@[simp] lemma toC_re (p : ℝ × ℝ) : (toC p).re = p.1 := rfl
@[simp] lemma toC_im (p : ℝ × ℝ) : (toC p).im = p.2 := rfl

@[simp] lemma reflect_re (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re := by
  simp [Zeta23.reflect]

@[simp] lemma reflect_im (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im := by
  simp [Zeta23.reflect]

/-- The zeros of `ζ` with `0 < Im ρ ≤ T`, with multiplicity, as `ZeroData`. -/
noncomputable def zetaZeroData (T : ℝ) : ZeroData := by
  classical
  refine ZeroData.ofMult
    ((Zeta23.zerosIn_finite 0 T).toFinset.image fun ρ => (ρ.re, ρ.im))
    (fun p => Zeta23.zeroMult (toC p)) ?_ ?_
  · -- closure under reflection
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hp
    have hρ' : ρ ∈ Zeta23.zerosIn 0 T := (Set.Finite.mem_toFinset _).1 hρ
    refine Finset.mem_image.2 ⟨Zeta23.reflect ρ, (Set.Finite.mem_toFinset _).2 ?_, ?_⟩
    · exact ⟨Zeta23.zeta_reflect_zero ρ hρ'.1, by simpa using hρ'.2.1, by simpa using hρ'.2.2⟩
    · simp [Riemann.refl]
  · -- multiplicity is reflection-invariant
    intro p hp
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hp
    have hρ' : ρ ∈ Zeta23.zerosIn 0 T := (Set.Finite.mem_toFinset _).1 hρ
    have hcoe : toC (Riemann.refl (ρ.re, ρ.im)) = Zeta23.reflect ρ := by
      apply Complex.ext <;> simp [Riemann.refl, toC]
    have hcoe' : toC (ρ.re, ρ.im) = ρ := by
      apply Complex.ext <;> simp [toC]
    rw [hcoe, hcoe', Zeta23.zeta_mult_reflect ρ hρ'.1]

/-- **The `N` of our `ZeroData` is zeta-23's `Ncount`.**  `SESSION 270`.

`Assumptions.lean`'s `zetaNonempty` docstring names the two steps left in
discharging that axiom: *"`(zetaZeroData T).N = Zeta23.Ncount 0 T` (a `finsum` ↔
`Finset.sum` conversion) and eventual positivity of `Ncount` from
`Zeta23.RvM.riemannVonMangoldt`. Plumbing, not mathematics."*  This is the first
step, and it needs no import our build does not already have — `Ncount` and
`zeroMult` are in the `17`-module closure we reach today.

`ofMult_N` turns the left side into a `Finset.sum` over the image of
`ρ ↦ (ρ.re, ρ.im)`; that map is injective, so `Finset.sum_image` moves the sum
back to the zeros themselves, and `finsum_mem_finset` matches the right side. -/
theorem zetaZeroData_N (T : ℝ) : (zetaZeroData T).N = Zeta23.Ncount 0 T := by
  classical
  have hinj : ∀ ρ ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
      ∀ σ ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
        (ρ.re, ρ.im) = (σ.re, σ.im) → ρ = σ := by
    intro ρ _ σ _ h
    exact Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  rw [zetaZeroData, ZeroData.ofMult_N, Finset.sum_image hinj]
  have hcoe : ∀ ρ : ℂ, toC (ρ.re, ρ.im) = ρ := fun ρ => Complex.ext rfl rfl
  simp only [hcoe]
  rw [Zeta23.Ncount,
    finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite 0 T)]

end Riemann
