/-
# Route I: what an effective Fujii constant actually buys

§2 of the program document reduces to the Gallagher–Mueller / Fujii identity

  `N⊛ + (2/λ) ∫₀^λ 𝒩(α) dα = TL ( λ + log(2+λ)/(π²λ) + O(√log(2+λ)/λ) )`.

Discarding `𝒩 ≥ 0` and writing the implied constant as `c₀` gives

  `N⊛ ≤ (Cbound c₀ λ + o(1)) · N(T)`  for every fixed `λ > 0`,
  `Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀ √log(2+λ) / λ`.

**[OPEN 0]** is exactly: pin down an admissible `c₀`.  This file computes,
with fully proved numerical bounds, what the answer has to be for the route
to pay:

* `c₀ ≥ 0.16` is **forced** (`c0_lower_bound`) — a smaller constant would
  contradict the trivial floor `N⊛ ≥ N`.  So the target window is closed
  from below; no one should hope for an arbitrarily small constant, and any
  claimed effective constant below `0.16` is wrong.
* `c₀ ≤ 0.8` already gives a **positive proportion** of simple critical
  zeros (`positive_proportion_of_le`), via `λ = 9/10`.
* `c₀ ≤ 0.33` already **beats the current record** `3/2 - (1/√2)cot(1/√2)
  ≈ 0.6725` (`beats_record_of_le`), via `λ = 61/100`.

(The exact optima, computed with true log values, are `c₀ < 0.8550` for
`C < 2` and `c₀ < 0.3476` for beating the record; the Lean numbers above are
the slightly weaker values that survive the crude provable bound
`log (2+λ) ≤ log 2 + λ/2`.)

This is what Lean adds to §2: OPEN 0 is not open-ended.  It is the question
*"is Fujii's constant below 0.8 (resp. 0.33)?"*, and the answer is at
least 0.16.
-/
import Riemann.Transfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Filter Real

namespace Riemann

/-- The constant produced by Route I at parameter `λ`, given an effective
Fujii constant `c₀`. -/
noncomputable def Cbound (c₀ lam : ℝ) : ℝ :=
  lam + Real.log (2 + lam) / (Real.pi ^ 2 * lam)
      + c₀ * Real.sqrt (Real.log (2 + lam)) / lam

/-- **[OPEN 0], stated.**  An effective form of Fujii's second-moment theorem:
the implied constant in the error term is `c₀`, so that Route I yields `(★)`
with constant `Cbound c₀ λ` for every fixed `λ > 0`.

Unconditionally *some* `c₀` exists (Fujii 1974/81, via Selberg's explicit
formula for `S(t)`); the open problem is to name one. -/
def EffectiveFujii (K : Counts) (c₀ : ℝ) : Prop :=
  ∀ lam > 0, K.StarBound (Cbound c₀ lam)

-- (Fujii's ineffective theorem itself is an axiom in `Assumptions.lean`.)

/-! ### Numerical toolkit -/

private lemma sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- `log (2 + λ) ≤ log 2 + λ/2 ≤ 0.6931471808 + λ/2`. -/
private lemma log_two_add_le {lam : ℝ} (h : 0 ≤ lam) :
    Real.log (2 + lam) ≤ 0.6931471808 + lam / 2 := by
  have h2 : (0:ℝ) < (2 + lam) / 2 := by linarith
  have hsplit : Real.log (2 + lam) = Real.log 2 + Real.log ((2 + lam) / 2) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt h2)]
    ring_nf
  have hle : Real.log ((2 + lam) / 2) ≤ (2 + lam) / 2 - 1 :=
    Real.log_le_sub_one_of_pos h2
  have := Real.log_two_lt_d9
  rw [hsplit]
  linarith

private lemma log_two_add_nonneg {lam : ℝ} (h : 0 ≤ lam) :
    0 ≤ Real.log (2 + lam) :=
  Real.log_nonneg (by linarith)

private lemma pi_sq_gt : (9.8695:ℝ) < Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_d6, Real.pi_pos]

/-- The core numerical estimate: an explicit upper bound for `Cbound` at a
given `λ`, from a rational upper bound `L` for `log (2+λ)` and a rational
`S` with `S² ≥ L`. -/
private lemma Cbound_le {c₀ lam L S : ℝ} (hlam : 0 < lam) (hc : 0 ≤ c₀)
    (hL : Real.log (2 + lam) ≤ L) (hS : 0 ≤ S) (hS2 : L ≤ S ^ 2) :
    Cbound c₀ lam ≤ lam + L / (9.8695 * lam) + c₀ * S / lam := by
  have hlognn : 0 ≤ Real.log (2 + lam) := log_two_add_nonneg hlam.le
  have hpi := pi_sq_gt
  have hL0 : 0 ≤ L := le_trans hlognn hL
  have h1 : Real.log (2 + lam) / (Real.pi ^ 2 * lam) ≤ L / (9.8695 * lam) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : Real.log (2 + lam) * (9.8695 * lam) ≤ L * (9.8695 * lam) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    have hb : L * (9.8695 * lam) ≤ L * (Real.pi ^ 2 * lam) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hL0
    linarith
  have hsq : Real.sqrt (Real.log (2 + lam)) ≤ S := sqrt_le_of_sq hS (hL.trans hS2)
  have h2 : c₀ * Real.sqrt (Real.log (2 + lam)) / lam ≤ c₀ * S / lam := by
    rw [div_le_div_iff₀ hlam hlam]
    have h3 : c₀ * Real.sqrt (Real.log (2 + lam)) ≤ c₀ * S :=
      mul_le_mul_of_nonneg_left hsq hc
    linarith [mul_le_mul_of_nonneg_right h3 hlam.le]
  unfold Cbound
  linarith

/-! ### The three numerical consequences -/

/-- **A positive proportion follows from `c₀ ≤ 0.8`.**  Taking `λ = 9/10`. -/
theorem Cbound_lt_two {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 0.8) :
    Cbound c₀ (9/10) < 2 := by
  have := Cbound_le (c₀ := c₀) (lam := 9/10) (L := 1.1431471808) (S := 1.07)
    (by norm_num) hc0 (le_trans (log_two_add_le (lam := 9/10) (by norm_num)) (by norm_num))
    (by norm_num) (by norm_num)
  nlinarith [this]

/-- **The record falls at `c₀ ≤ 0.33`.**  Taking `λ = 61/100`;
`2 - 1.3275 = 0.6725` is the current unconditional record. -/
theorem Cbound_lt_record {c₀ : ℝ} (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 0.33) :
    Cbound c₀ (61/100) < 1.3275 := by
  have := Cbound_le (c₀ := c₀) (lam := 61/100) (L := 0.9981471808) (S := 1)
    (by norm_num) hc0 (le_trans (log_two_add_le (lam := 61/100) (by norm_num)) (by norm_num))
    (by norm_num) (by norm_num)
  nlinarith [this]

/-- **Route I cannot do better than `c₀ ≈ 0.16`.**  Any effective constant is
`≥ 0.16`: at `λ = 0.462` the route would otherwise assert `N⊛ < N`. -/
theorem c0_lower_bound {K : Counts} {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (h : EffectiveFujii K c₀) : 0.16 ≤ c₀ := by
  have h1 : (1:ℝ) ≤ Cbound c₀ (462/1000) :=
    Counts.one_le_of_starBound (h (462/1000) (by norm_num))
  have h2 := Cbound_le (c₀ := c₀) (lam := 462/1000) (L := 0.9241471808) (S := 0.962)
    (by norm_num) hc0 (le_trans (log_two_add_le (lam := 462/1000) (by norm_num)) (by norm_num))
    (by norm_num) (by norm_num)
  nlinarith [h1, h2]

/-! ### Assembly: OPEN 0 ⟹ unconditional proportions -/

/-- With `c₀ ≤ 0.8`: a positive proportion of the zeros are simple and on the
critical line. -/
theorem positive_proportion_of_le {K : Counts} {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : c₀ ≤ 0.8) (h : EffectiveFujii K c₀) :
    ∃ κ > 0, K.Proportion κ := by
  refine ⟨2 - Cbound c₀ (9/10), by linarith [Cbound_lt_two hc0 hc], ?_⟩
  exact Counts.proportion_of_starBound (h (9/10) (by norm_num))

/-- With `c₀ ≤ 0.33`: strictly more than the current record `0.6725`. -/
theorem beats_record_of_le {K : Counts} {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : c₀ ≤ 0.33) (h : EffectiveFujii K c₀) :
    ∃ κ, 0.6725 < κ ∧ K.Proportion κ := by
  refine ⟨2 - Cbound c₀ (61/100), by linarith [Cbound_lt_record hc0 hc], ?_⟩
  exact Counts.proportion_of_starBound (h (61/100) (by norm_num))

end Riemann
