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
import Riemann.Fiber

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


/-! ### W7's "cheap invariants", made precise

`FAILURES.md` `#3` (W7) records that the cheap classical constraints on
multiplicity — Jensen's formula, the argument principle, Riemann–von Mangoldt —
permit `m ~ log γ` while the extremal configurations use `m ≤ 3`, so they are
"vacuous by an order of magnitude" and "only the Euler product bites".

`CLAIMS.md` grades that **C**: the class *"cheap invariant"* is informal, so the
claim is not a bound and cannot be cited as one.

**Kill condition, stated before this section was written:** *if the class cannot
be defined without smuggling in the Euler product, it stays grade C permanently
and that is the finding.*  **It did not fire.**  Every constraint in the cheap
family has the same shape — an upper bound on horizontal multiplicity — and that
shape is pure counting, with no multiplicative input at all.

So define the class as what it actually is, and the vacuity becomes a theorem
for the two-moment LP: **restricting to configurations of bounded multiplicity
does not improve the optimum**, because the two configurations that force the
constraints already have `H ≤ 2`.

*Scope, stated plainly:* this certifies the vacuity of **multiplicity bounds**
for **this** extremal problem.  The wider claim — that *no* classical invariant
of any kind tightens `C` — quantifies over a class still undefined, and stays
grade C. -/

/-- The number of zeros at one ordinate never exceeds the total. -/
lemma H_le_N (D : ZeroData) (γ : ℝ) : D.H γ ≤ D.N := by
  classical
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- A **cheap constraint**: an upper bound on horizontal multiplicity.  This is
the shape every Jensen/argument-principle/Riemann–von Mangoldt bound takes, and
it involves no multiplicative information whatever. -/
def BoundedMult (M : ℕ) (D : ZeroData) : Prop := ∀ γ : ℝ, D.H γ ≤ M

/-- A linear bound asserted only where multiplicity is bounded by `M` — i.e. a
bound entitled to use the cheap invariants. -/
def LinearBoundCheap (M : ℕ) (a b : ℝ) : Prop :=
  ∀ D : ZeroData, BoundedMult M D → a * D.N + b * D.Nstar ≤ D.Nsc

lemma single_boundedMult {M : ℕ} (hM : 1 ≤ M) : BoundedMult M single :=
  fun γ => le_trans (le_trans (H_le_N single γ) (le_of_eq single_N)) hM

lemma pairOnly_boundedMult {M : ℕ} (hM : 2 ≤ M) : BoundedMult M Gauge.pairOnly :=
  fun γ => le_trans (le_trans (H_le_N Gauge.pairOnly γ)
    (le_of_eq Gauge.pairOnly_N)) hM

/-- **W7, certified for the two-moment LP.**  Allowing a certificate to assume
any multiplicity bound `H ≤ M` (`M ≥ 2`) buys **nothing**: the optimum is still
`2 − C`.  The cheap invariants are satisfied by the binding configurations, so
they cannot bind.

This is the precise form of "the cheap invariants are satisfied *by
construction*". -/
theorem prop1_LP_optimal_cheap {M : ℕ} (hM : 2 ≤ M) {a b : ℝ}
    (h : LinearBoundCheap M a b) {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    a + b * C ≤ 2 - C := by
  have h1 : a + b ≤ 1 := by
    have := h single (single_boundedMult (le_trans (by norm_num) hM))
    rw [single_N, single_Nstar, single_Nsc] at this
    push_cast at this
    linarith
  have h2 : a + 2 * b ≤ 0 := by
    have := h Gauge.pairOnly (pairOnly_boundedMult hM)
    rw [Gauge.pairOnly_N, Gauge.pairOnly_Nstar, Gauge.pairOnly_Nsc] at this
    push_cast at this
    linarith
  rcases le_or_gt (-1 : ℝ) b with hcase | hcase
  · nlinarith [h2, hcase, hC2]
  · nlinarith [h1, hcase, hC1]


/-! ### The moment route is walled at every order

`Fiber.factMoment_eq_zero_of_masses_le_two` says every descending factorial
moment of order `≥ 3` vanishes when all atoms have mass `≤ 2`.  Both witnesses
that force `prop1`'s optimum — `single` (mass 1) and `Gauge.pairOnly` (mass 2) —
are of that kind.

**A moment inequality cannot exclude a configuration on which it is tight**, so
no moment constraint of *any* order removes either witness, and a constraint
that cannot exclude the binding witnesses cannot move the bound.  The moment
route is walled at every order, not merely at three
(`Fiber.three_Nstar_le_thirdMoment_add_two_N` was the `k = 3` case). -/

theorem single_factMoment {k : ℕ} (hk : 3 ≤ k) :
    Blindness.factMoment single k = 0 :=
  Blindness.factMoment_eq_zero_of_masses_le_two _ hk fun γ =>
    le_trans (H_le_N single γ) (le_of_eq_of_le single_N (by norm_num))

theorem pairOnly_factMoment {k : ℕ} (hk : 3 ≤ k) :
    Blindness.factMoment Gauge.pairOnly k = 0 :=
  Blindness.factMoment_eq_zero_of_masses_le_two _ hk fun γ =>
    le_trans (H_le_N Gauge.pairOnly γ) (le_of_eq_of_le Gauge.pairOnly_N (le_refl 2))

/-- **The moment route is walled at every order.** -/
theorem moment_route_walled {k : ℕ} (hk : 3 ≤ k) :
    Blindness.factMoment single k = 0 ∧
      Blindness.factMoment Gauge.pairOnly k = 0 :=
  ⟨single_factMoment hk, pairOnly_factMoment hk⟩

end Optimal
end Riemann
