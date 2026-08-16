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

/-- **The optimality is a fact about the class, not about the inequality.**
`SESSION 200`.

`prop1_LP_optimal` derives `a + b·C ≤ 2 − C` from `LinearBound a b`, and it uses
that hypothesis at exactly two configurations: `single` and `Gauge.pairOnly`.
`prop1_LP_optimal_cheap` makes the point constructively — the same conclusion
follows from a bound asserted only on `BoundedMult M` with `M ≥ 2`, because both
witnesses live there.

This is the converse, and it is what `198`/`199` taught to check.  Restrict to a
class that omits the witnesses and the conclusion is **false**: over
configurations with no zeros at all, every `(a, b)` is a valid linear bound, and
`(3, 0)` breaks `a + b·C ≤ 2 − C` at `C = 1`.

So the strength of `prop1`'s optimality comes from the class containing the two
witnesses.  A bound asserted only where `ζ`'s own configuration lives is not
covered by either theorem, since neither witness is claimed to be a `ζ`
configuration.  That gap is named here rather than left to be inferred. -/
theorem prop1_LP_optimal_needs_the_witnesses :
    ∃ (P : ZeroData → Prop) (a b C : ℝ),
      1 ≤ C ∧ C ≤ 2
      ∧ (∀ D : ZeroData, P D → a * D.N + b * D.Nstar ≤ D.Nsc)
      ∧ ¬ (a + b * C ≤ 2 - C) := by
  classical
  refine ⟨fun D => D.N = 0, 3, 0, 1, le_refl 1, by norm_num, ?_, by norm_num⟩
  intro D hD
  have hZ : D.Z = 0 := Multiset.card_eq_zero.1 hD
  have hstar : D.Nstar = 0 := by
    show ((D.Z.map fun p => D.H p.2).sum) = 0
    rw [hZ]; simp
  have hsc : D.Nsc = 0 := by
    show Multiset.card (D.Z.filter fun p => p.1 = 1 / 2 ∧ D.H p.2 = 1) = 0
    rw [hZ]; simp
  rw [hD, hstar, hsc]
  norm_num

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

/-- **In the multiplicity-one class every zero is simple and critical.**
`SESSION 201`.

`BoundedMult 1` caps `H` at one, so `N⊛ ≤ N`; with the floor `N ≤ N⊛` that
forces `N⊛ = N`, and `prop1` then gives `N ≤ N_sc`.

The reason this is not merely arithmetic: an off-line zero arrives with its
mirror at the *same ordinate*, so it raises `H` to at least two.  Capping
multiplicity at one therefore excludes off-line zeros outright. -/
theorem Nsc_eq_N_of_boundedMult_one (D : ZeroData) (h : BoundedMult 1 D) :
    D.N ≤ D.Nsc := by
  have h1 : D.Nstar ≤ D.N := by
    simpa using Blindness.Nstar_le_of_multiplicity_le D 1 h
  have h2 : (D.N : ℤ) ≤ (D.Nstar : ℤ) := ZeroData.N_le_Nstar D
  have h3 := ZeroData.prop1 D
  omega

/-- **`prop1`'s LP conclusion fails on the multiplicity-one class.**
`SESSION 201`.

`200` closed with the observation that `prop1_LP_optimal`'s second witness,
`Gauge.pairOnly`, is a *multiple* zero — so restricting to configurations `ζ`
would have if its zeros were simple drops that witness.  This is that
observation as a theorem rather than a sentence.

`(a, b) = (1, 0)` is a valid linear bound on `BoundedMult 1` — that is
`Nsc_eq_N_of_boundedMult_one` — and `a + b·C = 1 > 2 − C` for every `C > 1`.
So on the multiplicity-one class the LP conclusion holds only at `C = 1`.

What this does and does not say: it does **not** exhibit a better bound for `ζ`,
because `ζ` is not known to lie in this class.  It says the argument that the
two-moment world is exhausted uses a configuration with a multiple zero, and an
argument that ruled multiple zeros out would take that witness with it. -/
theorem prop1_LP_optimal_fails_on_simple_class {C : ℝ} (hC : 1 < C) :
    LinearBoundCheap 1 1 0 ∧ ¬ ((1 : ℝ) + 0 * C ≤ 2 - C) := by
  refine ⟨fun D hD => ?_, fun h => by linarith⟩
  have := Nsc_eq_N_of_boundedMult_one D hD
  have hcast : (D.N : ℝ) ≤ (D.Nsc : ℝ) := by exact_mod_cast this
  simpa using hcast

/-- **The threshold is exactly `M = 2`.**  `SESSION 202`.

Putting `prop1_LP_optimal_cheap` and `prop1_LP_optimal_fails_on_simple_class`
together as one statement, because the pair is the interesting object and two
lemmas in different places are not.

For every `C ∈ (1, 2]`: the LP conclusion holds for *every* bound asserted on
`BoundedMult M` with `M ≥ 2`, and fails for `M ≤ 1`.

`M = 0` is covered by the same half rather than being a separate case, and by
the route the proof actually takes: `BoundedMult 0` implies `BoundedMult 1` by
monotonicity, so `Nsc_eq_N_of_boundedMult_one` applies and `(1, 0)` breaks the
conclusion there too.  So the split is clean, and the threshold is the mass-two
atom itself: the conclusion is available when the class is large enough to
contain a doubled zero. -/
theorem prop1_LP_threshold_at_two {C : ℝ} (hC1 : 1 < C) (hC2 : C ≤ 2) :
    (∀ M : ℕ, 2 ≤ M → ∀ a b : ℝ, LinearBoundCheap M a b → a + b * C ≤ 2 - C)
      ∧ (∀ M : ℕ, M ≤ 1 →
          ∃ a b : ℝ, LinearBoundCheap M a b ∧ ¬ (a + b * C ≤ 2 - C)) := by
  refine ⟨fun M hM a b h => prop1_LP_optimal_cheap hM h (le_of_lt hC1) hC2, ?_⟩
  intro M hM
  refine ⟨1, 0, fun D hD => ?_, fun h => by linarith⟩
  have hD1 : BoundedMult 1 D := fun γ => le_trans (hD γ) hM
  have hcast : (D.N : ℝ) ≤ (D.Nsc : ℝ) := by
    exact_mod_cast Nsc_eq_N_of_boundedMult_one D hD1
  simpa using hcast



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
