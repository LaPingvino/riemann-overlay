/-
# Proposition 1 is LP-optimal in the two moments — certified

`Gauge.lean`'s docstring asserts, as part of the R16 audit, that
`prop1 : Nsc ≥ 2N − N⊛` is **optimal** among linear bounds in `(N, N⊛)`: that no
`Nsc ≥ αN + βN⊛` beats it in the useful regime.  Only a single tightness
witness (`prop1_tight`) was ever proved; the optimality claim was prose.

The ladder audit (`FAILURES.md`, W34d) established the standard: a claim about
what a *class* cannot do needs a machine-checked statement, not a docstring.
Applying that standard to our own earlier docstring is what this file does.

**The argument, and it needs exactly two configurations.**

* A single simple on-line zero has `N = 1`, `N⊛ = 1`, `Nsc = 1`, forcing
  `α + β ≤ 1`.
* One mirror pair at a single ordinate has `N = 2`, `N⊛ = 4`, `Nsc = 0`
  (`Gauge.pairOnly`), forcing `2α + 4β ≤ 0`, i.e. `α + 2β ≤ 0`.

Under a star bound `N⊛ ≤ C·N` a linear bound with `β ≤ 0` yields the proportion
`α + βC`.  Those two constraints already force `α + βC ≤ 2 − C` throughout
`1 ≤ C ≤ 2`, with equality at `(α, β) = (2, −1)`.

**Kill condition, stated before the file was written:** *if two configurations
do not suffice — if some `(α, β)` satisfying both constraints still beats
`2 − C` somewhere in the regime — then prop1's optimality needs more
constraints and the docstring claim is downgraded.*  It did not fire.

The consequence is the one the register already draws and can now rely on:
**improving Proposition 1 requires leaving the two-moment world**, i.e. a third
moment `Σ m³` — [OPEN D]'s currency.  The reduction and the ceiling want the
same missing input.
-/
import Riemann.Gauge

namespace Riemann
namespace Optimal

open Multiset

/-- A single simple zero on the critical line. -/
noncomputable def single : ZeroData where
  Z := {((1/2 : ℝ), (0 : ℝ))}
  refl_inv := by
    show Multiset.map refl (((1/2 : ℝ), (0:ℝ)) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_zero]
    norm_num [refl]

@[simp] lemma single_N : single.N = 1 := by
  show Multiset.card (((1/2 : ℝ), (0:ℝ)) ::ₘ 0) = 1
  simp

lemma single_H : single.H 0 = 1 := by
  classical
  show Multiset.card (Multiset.filter _ (((1/2 : ℝ), (0:ℝ)) ::ₘ 0)) = 1
  rw [Multiset.filter_cons_of_pos]
  · simp
  · rfl

lemma single_Nstar : single.Nstar = 1 := by
  show ((((1/2 : ℝ), (0:ℝ)) ::ₘ 0).map fun p => single.H p.2).sum = 1
  rw [Multiset.map_cons, Multiset.map_zero]
  simp [single_H]

lemma single_Nsc : single.Nsc = 1 := by
  classical
  show Multiset.card (Multiset.filter _ (((1/2 : ℝ), (0:ℝ)) ::ₘ 0)) = 1
  rw [Multiset.filter_cons_of_pos]
  · simp
  · exact ⟨rfl, single_H⟩

/-! ### The class of linear bounds, and what the two witnesses force -/

/-- A linear bound in the two moments: `Nsc ≥ αN + βN⊛`, asserted for **every**
configuration.  This is the class `prop1` lives in. -/
def LinearBound (a b : ℝ) : Prop :=
  ∀ D : ZeroData, a * D.N + b * D.Nstar ≤ D.Nsc

/-- `prop1` is a member of the class. -/
theorem linearBound_prop1 : LinearBound 2 (-1) := by
  intro D
  have h := ZeroData.prop1 D
  have h' : (2 * (D.N : ℤ) - D.Nstar : ℤ) ≤ (D.Nsc : ℤ) := h
  have : ((2 * (D.N : ℤ) - D.Nstar : ℤ) : ℝ) ≤ ((D.Nsc : ℤ) : ℝ) := by
    exact_mod_cast h'
  push_cast at this ⊢
  linarith

/-- The simple zero forces `α + β ≤ 1`. -/
theorem linearBound_le_one {a b : ℝ} (h : LinearBound a b) : a + b ≤ 1 := by
  have := h single
  rw [single_N, single_Nstar, single_Nsc] at this
  push_cast at this
  linarith

/-- The lone mirror pair forces `α + 2β ≤ 0`.  This is the configuration that
saturates `prop1` (`Gauge.prop1_tight`), so it is the binding constraint. -/
theorem linearBound_mass2 {a b : ℝ} (h : LinearBound a b) : a + 2 * b ≤ 0 := by
  have := h Gauge.pairOnly
  rw [Gauge.pairOnly_N, Gauge.pairOnly_Nstar, Gauge.pairOnly_Nsc] at this
  push_cast at this
  linarith

/-! ### Optimality -/

/-- **Proposition 1 is LP-optimal in `(N, N⊛)`.**  Under a star bound `C` in the
useful regime `1 ≤ C ≤ 2`, no linear bound in the two moments yields a
proportion exceeding `2 − C`, which is exactly what `prop1` yields.

Only two configurations are used — and **no sign hypothesis on `β` is needed**.
The docstring being certified here guessed that `β ≤ 0` would be required; it is
not, so the statement is strictly stronger than the claim it replaces. -/
theorem prop1_LP_optimal {a b : ℝ} (h : LinearBound a b)
    {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) : a + b * C ≤ 2 - C := by
  have h1 : a + b ≤ 1 := linearBound_le_one h
  have h2 : a + 2 * b ≤ 0 := linearBound_mass2 h
  rcases le_or_gt (-1 : ℝ) b with hcase | hcase
  · -- `−1 ≤ b ≤ 0`: the mass-two constraint binds
    nlinarith [h2, hcase, hC2]
  · -- `b < −1`: the simple-zero constraint binds
    nlinarith [h1, hcase, hC1]

/-- **And the bound is attained**, so `2 − C` is the exact optimum of the class,
not merely an upper bound for it. -/
theorem prop1_LP_optimal_attained {C : ℝ} : (2 : ℝ) + (-1) * C = 2 - C := by
  ring

end Optimal
end Riemann
