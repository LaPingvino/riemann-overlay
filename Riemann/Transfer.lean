/-
# From a bound on `N⊛` to a proportion of simple critical zeros

This file formalises the second half of §1: the implication

  `N⊛(T) ≤ (C + o(1)) N(T)`  ⟹  at least a proportion `2 - C` of zeros are
  simple and on the critical line.

Fully proved; it is elementary real analysis on abstract counting functions.
The link to the actual zero counts is `Riemann.ZeroData.prop1` in `Basic.lean`.
-/
import Riemann.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Riemann

/-- The counting functions of a height-`T` family of zero data.  `Nz` is
`N(T)`, `Ns` is `N⊛(T)`, `Nsc` is `N_sc(T)`. -/
structure Counts where
  Nz : ℝ → ℝ
  Ns : ℝ → ℝ
  Nsc : ℝ → ℝ
  /-- Positivity of the zero count for large `T`. -/
  pos : ∀ᶠ T in atTop, 0 < Nz T
  /-- Proposition 1, transported to the analytic side. -/
  prop1 : ∀ T, 2 * Nz T - Ns T ≤ Nsc T
  /-- The trivial floor `N⊛ ≥ N`. -/
  floor : ∀ T, Nz T ≤ Ns T

namespace Counts

variable (K : Counts)

/-- `(★)`: `N⊛(T) ≤ (C + o(1)) N(T)`. -/
def StarBound (C : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, K.Ns T ≤ (C + ε) * K.Nz T

/-- At least a proportion `κ - o(1)` of the zeros are simple and critical. -/
def Proportion (κ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, κ - ε ≤ K.Nsc T / K.Nz T

variable {K}

/-- **The transfer theorem.**  `(★)` with constant `C` gives a proportion
`2 - C` of simple critical zeros.  In particular `C < 2` gives a positive
proportion and `C → 1` gives `100%`. -/
theorem proportion_of_starBound {C : ℝ} (h : K.StarBound C) :
    K.Proportion (2 - C) := by
  intro ε hε
  filter_upwards [h ε hε, K.pos] with T hT hpos
  have h1 : (2 - C - ε) * K.Nz T ≤ K.Nsc T := by
    have := K.prop1 T
    nlinarith [hT]
  rw [le_div_iff₀ hpos]
  linarith

/-- Any admissible constant in `(★)` is at least `1`: the trivial floor
`N⊛ ≥ N`.  This is the consistency check that later pins a *lower* bound on
the effective Fujii constant. -/
theorem one_le_of_starBound {C : ℝ} (h : K.StarBound C) : 1 ≤ C := by
  by_contra hC
  push_neg at hC
  have hεpos : (0:ℝ) < (1 - C) / 2 := by linarith
  have hfalse : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [h ((1 - C) / 2) hεpos, K.pos] with T hT hpos
    have hfloor := K.floor T
    have hlt : C + (1 - C) / 2 < 1 := by linarith
    nlinarith
  exact hfalse.exists.elim fun _ h => h

/-- **The star-bound currency's ceiling is `1`, not `κ`.**  `SESSION 241`.

`240` priced the project's other two exchanges — off-line control and the
multiplicity ladder — and found both saturating at the certified `NscStd` row
`κ`.  This one does not.

`proportion_of_starBound` pays `2 − C`, and `one_le_of_starBound` above is the
floor `C ≥ 1`, so the payout is at most `1`, reached exactly at `C = 1`.

That is why `RULING.md`'s two rows above `κ` — Route I and `[OPEN D]` — are the
ones reaching the ledger through `(★)`: theirs is the currency whose ceiling is
a proportion of `1` rather than the baseline the project was handed. -/
theorem starBound_ceiling {C : ℝ} (h : K.StarBound C) : 2 - C ≤ 1 := by
  have := one_le_of_starBound h
  linarith

/-- …and the ceiling is reached exactly at the floor `C = 1`.  `SESSION 241`. -/
theorem starBound_ceiling_iff {C : ℝ} : 2 - C = 1 ↔ C = 1 := by
  constructor <;> intro hc <;> linarith

end Counts

end Riemann
