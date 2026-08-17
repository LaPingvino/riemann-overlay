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
back to the zeros themselves, and `finsum_mem_eq_finite_toFinset_sum` matches
the right side.

*(**Name corrected, `SESSION 301`.** This sentence said `finsum_mem_finset`,
which does not resolve under this project's imports — `270` tried that name,
recorded at `SESSION.md:12645` that it does not exist, used the right one on
line `81`, and left the wrong one in the prose describing the fixed proof.
`forensics/citation_check.py` exists because of this.)* -/
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

/-- **Widening the window can only add zeros.**  `SESSION 271`. -/
theorem Ncount_mono_left {a b T : ℝ} (hab : a ≤ b) :
    Zeta23.Ncount b T ≤ Zeta23.Ncount a T := by
  classical
  have hsub : Zeta23.zerosIn b T ⊆ Zeta23.zerosIn a T := by
    rintro ρ ⟨hz, h1, h2⟩; exact ⟨hz, lt_of_le_of_lt hab h1, h2⟩
  rw [Zeta23.Ncount, Zeta23.Ncount,
    finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite b T),
    finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite a T)]
  refine Finset.sum_le_sum_of_subset ?_
  intro ρ hρ
  simp only [Set.Finite.mem_toFinset] at *
  exact hsub hρ

/-- **What is left of `zetaNonempty`, stated exactly.**  `SESSION 271`.

`270` bridged the counts (`zetaZeroData_N`).  This reduces the axiom to a single
statement *about the dependency*: eventual positivity of the **dyadic** count.

The distinction matters and cost `271` a look.  `Zeta23.RiemannVonMangoldt.main`
is dyadic — `|Z.N T (2·T) − T/(2π)·ell1 T| ≤ C·log T` — while the axiom asks
about the **cumulative** window `(0, T]`.  Importing `RvM.Statement` therefore
does *not* finish the job on its own; the step from dyadic to cumulative is
`Ncount_mono_left`, which is ours and needs no import.

With this, discharging `zetaNonempty` is `import Zeta23.RvM.Statement` plus
`import Zeta23.GammaFacts.Complete` (`Zeta23.gammaFacts` is not in the former's
closure — checked, `271`), and then deriving the hypothesis below from
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts`.  The price of those imports is
`270`'s measurement and Joop's ruling. -/
theorem zetaNonempty_of_dyadic
    (h : ∀ᶠ T in Filter.atTop, 0 < Zeta23.Ncount T (2 * T)) :
    ∀ᶠ T in Filter.atTop, 0 < (zetaZeroData T).N := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨2 * max T₀ 0, fun S hS => ?_⟩
  have h0 : (0 : ℝ) ≤ max T₀ 0 := le_max_right _ _
  have hhalf : T₀ ≤ S / 2 := by
    have := le_trans (le_max_left T₀ 0) (by linarith : max T₀ 0 ≤ S / 2)
    exact this
  have hpos := hT₀ (S / 2) hhalf
  have hSeq : 2 * (S / 2) = S := by ring
  rw [hSeq] at hpos
  have hmono : Zeta23.Ncount (S / 2) S ≤ Zeta23.Ncount 0 S :=
    Ncount_mono_left (by linarith : (0:ℝ) ≤ S / 2)
  rw [zetaZeroData_N]
  omega

/-- `ℓ₁ → ∞`, so eventually `1 ≤ ℓ₁ T`.  `SESSION 272`. -/
theorem eventually_one_le_ell1 : ∀ᶠ T in Filter.atTop, (1:ℝ) ≤ Zeta23.ell1 T := by
  have hpi : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have heq : (fun T : ℝ => Zeta23.ell1 T)
      = fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1) := by
    funext T; unfold Zeta23.ell1 Zeta23.l; ring
  have h : Filter.Tendsto (fun T : ℝ => Zeta23.ell1 T) Filter.atTop Filter.atTop := by
    rw [heq]
    exact Filter.tendsto_atTop_add_const_right _ _
      (Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const hpi))
  exact h.eventually_ge_atTop 1

/-- `log` is eventually beaten by any multiple of the identity.  `SESSION 272`. -/
theorem eventually_const_mul_log_lt (c : ℝ) :
    ∀ᶠ T in Filter.atTop, c * Real.log T < T := by
  have h2 := (Real.isLittleO_log_id_atTop.const_mul_left c).def (c := 1/2) (by norm_num)
  filter_upwards [h2, Filter.eventually_gt_atTop 0] with T hT hT0
  simp only [Real.norm_eq_abs, id_eq] at hT
  rw [abs_of_pos hT0] at hT
  calc c * Real.log T ≤ |c * Real.log T| := le_abs_self _
    _ ≤ (1/2) * T := hT
    _ < T := by linarith

/-- **`zetaNonempty` reduces to zeta-23's `RiemannVonMangoldt.main`, and nothing
else.**  `SESSION 272`.

`270` bridged the counts, `271` reduced the axiom to eventual positivity of the
*dyadic* count.  This closes the last gap on our side: the asymptotic
`|N(T,2T) − T·ℓ₁/2π| ≤ C·log T` gives positivity, because `ℓ₁ → ∞` bounds the
main term below by `T/2π` and `log` is eventually beaten by any multiple of the
identity.

So the hypothesis below is **exactly** what the import buys — it is
`RiemannVonMangoldt.main` for `zetaZeroConfig`, modulo `zetaZeroConfig_N`, which
is a simp lemma we already reach.  Everything else in the discharge is proved
here, unconditionally, at no build cost. -/
theorem zetaNonempty_of_rvm_main
    (h : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(Zeta23.Ncount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T|
        ≤ C * Real.log T) :
    ∀ᶠ T in Filter.atTop, 0 < (zetaZeroData T).N := by
  refine zetaNonempty_of_dyadic ?_
  obtain ⟨C, T₀, hmain⟩ := h
  have hpi : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  filter_upwards [Filter.eventually_ge_atTop T₀, eventually_one_le_ell1,
    Filter.eventually_gt_atTop (0:ℝ),
    eventually_const_mul_log_lt (2 * Real.pi * C)] with T hT hell hT0 hlog
  have hb := hmain T hT
  have hmain_lb : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * Zeta23.ell1 T := by
    have : (0:ℝ) < T / (2 * Real.pi) := by positivity
    nlinarith
  have hCl : C * Real.log T < T / (2 * Real.pi) := by
    rw [lt_div_iff₀ hpi]; nlinarith
  have hgap : (0:ℝ) < (Zeta23.Ncount T (2 * T) : ℝ) := by
    have := abs_le.1 hb
    linarith [this.1, this.2]
  exact_mod_cast hgap

/-- **Our `NscStd` is zeta-23's `N0simple`.**  `SESSION 274`.

The `NscStd`-side counterpart of `270`'s `zetaZeroData_N`, and the second of the
two count bridges `baseline_zeta23` needs.  Their `N0simple` takes the `ncard` of
`zerosIn ∩ {re = 1/2} ∩ {zeroMult = 1}`; ours filters the multiset on
`p.1 = 1/2 ∧ Z.count p = 1`.  `ofMult_NscStd` puts ours in `Finset` form,
`ρ ↦ (ρ.re, ρ.im)` is injective so the filter and the image commute, and the
two sides are the same set counted the same way.

**The kill condition `273` filed did not fire, and that is the finding.**  The
project's `NscStd` and zeta-23's `N0simple` coincide on `zetaZeroData` with no
separating case — an on-line zero is determined by its ordinate, so "the on-line
part has mass one" and "this zero is simple and on the line" pick out the same
points.  The two vocabularies were one vocabulary at the point of contact. -/
theorem zetaZeroData_NscStd (T : ℝ) : (zetaZeroData T).NscStd = Zeta23.N0simple 0 T := by
  classical
  rw [zetaZeroData, ZeroData.ofMult_NscStd]
  have hinj : Set.InjOn (fun ρ : ℂ => (ρ.re, ρ.im))
      ((Zeta23.zerosIn_finite 0 T).toFinset : Set ℂ) := by
    intro a _ b _ h
    exact Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfil : ((Zeta23.zerosIn_finite 0 T).toFinset.image fun ρ : ℂ => (ρ.re, ρ.im)).filter
      (fun p => p.1 = 1 / 2 ∧ Zeta23.zeroMult (toC p) = 1)
      = ((Zeta23.zerosIn_finite 0 T).toFinset.filter
          (fun ρ => ρ.re = 1 / 2 ∧ Zeta23.zeroMult ρ = 1)).image
          (fun ρ : ℂ => (ρ.re, ρ.im)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨ρ, hρ, rfl⟩, h1, h2⟩
      have hc : toC (ρ.re, ρ.im) = ρ := Complex.ext rfl rfl
      rw [hc] at h2
      exact ⟨ρ, ⟨hρ, h1, h2⟩, rfl⟩
    · rintro ⟨ρ, ⟨hρ, h1, h2⟩, rfl⟩
      have hc : toC (ρ.re, ρ.im) = ρ := Complex.ext rfl rfl
      exact ⟨⟨ρ, hρ, rfl⟩, h1, by rw [hc]; exact h2⟩
  rw [hfil, Finset.card_image_of_injOn (hinj.mono (by intro x hx; simpa using
      (Finset.mem_filter.1 hx).1))]
  have hfin : (Zeta23.zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | Zeta23.zeroMult ρ = 1}).Finite :=
    (Zeta23.zerosIn_finite 0 T).subset (fun x hx => hx.1.1)
  rw [Zeta23.N0simple, Set.ncard_eq_toFinset_card _ hfin]
  congr 1
  ext ρ
  simp [Set.Finite.mem_toFinset, and_assoc]

/-- **`cos` to order ten.**  `SESSION 276`.

`275` priced `baseline_zeta23`'s numeric step and found Mathlib's shipped
`Complex.cos_bound` `43,711×` too coarse for it — it is `Complex.exp_bound`'s
`range 4` instance, and the bound needed here wants `range 10`. This is that
instance, assembled the way `cos_bound` assembles its own.

At `x = 1/√2` the error is `≈9.5·10⁻⁹` against the `2.98·10⁻⁷` the `cot` bound
requires, and `274` showed the polynomial evaluates in `ℚ` there because
`x² = 1/2`. The `sin` analogue and the final quotient are the remaining steps.

It lives here rather than in `Basic.lean` because it exists for the
`baseline_zeta23` bridge; it mentions no `ZeroData` and depends only on
Mathlib. -/
theorem cos_bound10 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320)|
      ≤ |x| ^ 10 * (11 / (3628800 * 10)) := by
  have hI : ‖(x:ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]; simpa using hx
  have hI' : ‖-(x:ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one]; simpa using hx
  have e1 := Complex.exp_bound hI (n := 10) (by norm_num)
  have e2 := Complex.exp_bound hI' (n := 10) (by norm_num)
  have hnorm : ‖(x:ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]; rfl
  have hnorm' : ‖-(x:ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one]; simp
  have key : ‖Complex.cos (x:ℂ) - (1 - (x:ℂ)^2/2 + (x:ℂ)^4/24 - (x:ℂ)^6/720 + (x:ℂ)^8/40320)‖
      ≤ |x| ^ 10 * (11 / (3628800 * 10)) := by
    have hcos : Complex.cos (x:ℂ)
        = (Complex.exp ((x:ℂ) * Complex.I) + Complex.exp (-(x:ℂ) * Complex.I)) / 2 := by
      rw [Complex.cos]
    have hsum : (∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial
        + ∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial) / 2
        = ((1 : ℂ) - (x:ℂ)^2/2 + (x:ℂ)^4/24 - (x:ℂ)^6/720 + (x:ℂ)^8/40320) := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hcos, ← hsum, ← sub_div, ← sub_add_sub_comm]
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le
      (Complex.exp ((x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial)
      (Complex.exp (-(x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial)
    rw [hnorm] at e1; rw [hnorm'] at e2
    have hf : ((10 : ℕ).factorial : ℝ) = 3628800 := by norm_num [Nat.factorial]
    rw [hf] at e1 e2
    simp only [Nat.succ_eq_add_one] at e1 e2
    nlinarith [norm_nonneg (Complex.exp ((x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial)]
  have hre : Real.cos x = (Complex.cos (x:ℂ)).re := by
    rw [← Complex.ofReal_cos]; rfl
  calc |Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320)|
      = ‖((Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; rfl
    _ ≤ _ := by push_cast [Complex.ofReal_cos]; exact key

/-- **`sin` to order ten.**  `SESSION 277`.

The companion to `cos_bound10`, same order and same error bound.

**The pattern transferred, with one difference worth recording.**  `cos` is
`(e₊ + e₋)/2` and its error factors by `sub_div` alone; `sin` is `(e₋ − e₊)·I/2`,
where the `I` has to come out through the subtraction as well, and chaining
`sub_div` with `sub_mul` does not match.  An explicit `ring` identity for the
factoring does, and is shorter than finding the right rewrite order. -/
theorem sin_bound10 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880)|
      ≤ |x| ^ 10 * (11 / (3628800 * 10)) := by
  have hI : ‖(x:ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]; simpa using hx
  have hI' : ‖-(x:ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one]; simpa using hx
  have e1 := Complex.exp_bound hI (n := 10) (by norm_num)
  have e2 := Complex.exp_bound hI' (n := 10) (by norm_num)
  have hnorm : ‖(x:ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]; rfl
  have hnorm' : ‖-(x:ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one]; simp
  have key : ‖Complex.sin (x:ℂ)
      - ((x:ℂ) - (x:ℂ)^3/6 + (x:ℂ)^5/120 - (x:ℂ)^7/5040 + (x:ℂ)^9/362880)‖
      ≤ |x| ^ 10 * (11 / (3628800 * 10)) := by
    have hsin : Complex.sin (x:ℂ)
        = (Complex.exp (-(x:ℂ) * Complex.I) - Complex.exp ((x:ℂ) * Complex.I)) * Complex.I / 2 := by
      rw [Complex.sin]
    have hsum : (∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial
        - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial) * Complex.I / 2
        = ((x:ℂ) - (x:ℂ)^3/6 + (x:ℂ)^5/120 - (x:ℂ)^7/5040 + (x:ℂ)^9/362880) := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hsin, ← hsum]
    have hfac : (Complex.exp (-(x:ℂ) * Complex.I) - Complex.exp ((x:ℂ) * Complex.I)) * Complex.I / 2
        - (∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial
           - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial) * Complex.I / 2
        = ((Complex.exp (-(x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial)
           - (Complex.exp ((x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial))
          * Complex.I / 2 := by ring
    rw [hfac, norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_I, mul_one]
    have := norm_sub_le
      (Complex.exp (-(x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, (-(x:ℂ) * Complex.I) ^ m / m.factorial)
      (Complex.exp ((x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial)
    rw [hnorm] at e1; rw [hnorm'] at e2
    have hf : ((10 : ℕ).factorial : ℝ) = 3628800 := by norm_num [Nat.factorial]
    rw [hf] at e1 e2
    simp only [Nat.succ_eq_add_one] at e1 e2
    nlinarith [norm_nonneg (Complex.exp ((x:ℂ) * Complex.I) - ∑ m ∈ Finset.range 10, ((x:ℂ) * Complex.I) ^ m / m.factorial)]
  calc |Real.sin x - (x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880)|
      = ‖((Real.sin x - (x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; rfl
    _ ≤ _ := by push_cast [Complex.ofReal_sin]; exact key

/-- **Our decimal is a valid floor for zeta-23's exact constant.**  `SESSION 279`.

`ThmD` proves `2 − 1/c₁* = 3/2 − cot(1/√2)/√2` and states in as many words that
*"decimals are not formalized; the constant is exact"*.  `Assumptions.lean`
asserts the decimal `0.6725`.  `268` recorded that gap as an unpriced second cost
of discharging `baseline_zeta23`, on the reading that it needed certified
numerics this project has none of.

It needed none.  `274`: at `x = 1/√2` both `x² = 1/2` and `x·√2 = 1` hold with no
approximation, so the Taylor polynomials are rational and the `√2` cancels out of
the quotient.  `276`/`277`: `cos_bound10` and `sin_bound10` supply the error at
order ten, `≈9.5·10⁻⁹` against the `2.98·10⁻⁷` needed.  What is left, and what
this proves, is one comparison of explicit rationals with slack
`191159/309657600000`.

**This does not discharge `baseline_zeta23`** — *written at `279`, and `337` did
discharge it.*  At the time, that axiom still needed `ThmD`'s `44,441`-line build
to obtain the exact constant; `337` took the build and `baseline_zeta23` is a
theorem in `Riemann/Assumptions.lean`, proved through `Zeta23.ThmD.Mult` with this
lemma supplying the decimal step.  What `279` removed was the *second* cost: the
decimal no longer stood between their theorem and our row, which is why the
remaining cost was only the build. -/
theorem baseline_decimal_le_exact :
    (0.6725 : ℝ) ≤ 3/2 - Real.cos (1/Real.sqrt 2) / Real.sin (1/Real.sqrt 2) / Real.sqrt 2 := by
  have hs0 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set x := 1 / Real.sqrt 2 with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hx2 : x ^ 2 = 1/2 := by rw [hxdef, div_pow, one_pow, hs]
  have hxs : x * Real.sqrt 2 = 1 := by rw [hxdef]; field_simp
  have hx1 : |x| ≤ 1 := by
    rw [abs_of_pos hxpos, hxdef, div_le_one hs0]; nlinarith [hs, hs0]
  have hsle : Real.sqrt 2 ≤ 3/2 := by nlinarith [hs, hs0]
  have hsinpos : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi hxpos
    nlinarith [Real.pi_gt_three, hs, hs0, hxdef]
  -- powers of x collapse
  have h4 : x^4 = 1/4 := by rw [show x^4 = (x^2)^2 by ring, hx2]; norm_num
  have h6 : x^6 = 1/8 := by rw [show x^6 = (x^2)^3 by ring, hx2]; norm_num
  have h8 : x^8 = 1/16 := by rw [show x^8 = (x^2)^4 by ring, hx2]; norm_num
  have h10 : |x|^10 = 1/32 := by
    rw [abs_of_pos hxpos, show x^10 = (x^2)^5 by ring, hx2]; norm_num
  have h3 : x^3 = x * (1/2) := by rw [show x^3 = x * x^2 by ring, hx2]
  have h5 : x^5 = x * (1/4) := by rw [show x^5 = x * (x^2)^2 by ring, hx2]; norm_num
  have h7 : x^7 = x * (1/8) := by rw [show x^7 = x * (x^2)^3 by ring, hx2]; norm_num
  have h9 : x^9 = x * (1/16) := by rw [show x^9 = x * (x^2)^4 by ring, hx2]; norm_num
  -- the two bounds, evaluated
  have hc := cos_bound10 hx1
  have hsn := sin_bound10 hx1
  rw [hx2, h4, h6, h8, h10] at hc
  rw [h3, h5, h7, h9, h10] at hsn
  have hcos : Real.cos x ≤ 163483/215040 + 11/1161216000 := by
    have := abs_le.1 hc; linarith [this.2]
  have hsin : x * (5334193/5806080) - 11/1161216000 ≤ Real.sin x := by
    have := abs_le.1 hsn; linarith [this.1]
  -- assemble
  have key : Real.cos x / Real.sin x / Real.sqrt 2 ≤ 8275/10000 := by
    rw [div_le_iff₀ hs0, div_le_iff₀ hsinpos]
    have hlow : (8275/10000 : ℝ) * Real.sqrt 2 * Real.sin x
        ≥ 8275/10000 * (5334193/5806080 - (3/2) * (11/1161216000)) := by
      have hxR : Real.sqrt 2 * (x * (5334193/5806080)) = 5334193/5806080 := by
        rw [show Real.sqrt 2 * (x * (5334193/5806080))
          = (x * Real.sqrt 2) * (5334193/5806080) by ring, hxs, one_mul]
      nlinarith [hsin, hs0, hsle, hxR, hxpos]
    nlinarith [hcos, hlow]
  linarith [key]

end Riemann
