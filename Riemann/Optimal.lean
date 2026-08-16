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

/-- **The single-atom test at every mass.**  `SESSION 204`.

`ISSUES` `#20` derives `prop1`'s optimality from the LP characterisation *"a
linear bound `a₁ ≥ αN + βN⊛` is valid iff `αm + βm² ≤ [m = 1]` for every
`m ≥ 1`"*, and that quantifier was hand-derived: only `m = 1`
(`linearBound_le_one`) and `m = 2` (`linearBound_mass2`) were machine-checked.

This is the "only if" half at every `m`, tested on the pure on-line atom
`config m 0 a`, where `N = m`, `N⊛ = m²` and `N_sc = [m = 1]`.  The two existing
lemmas are its `m = 1` and `m = 2` instances in content, and are kept because
`prop1_LP_optimal` cites them by name. -/
theorem linearBound_mass (m : ℕ) {a b : ℝ} (h : LinearBound a b) :
    a * m + b * (m * m) ≤ if m = 1 then 1 else 0 := by
  have hm := h (Blindness.config m 0 0)
  rw [Blindness.config_N, Blindness.config_Nstar_pure,
    Blindness.config_Nsc_pure] at hm
  by_cases h1 : m = 1
  · rw [if_pos h1]
    rw [if_pos h1] at hm
    push_cast at hm
    linarith
  · rw [if_neg h1]
    rw [if_neg h1] at hm
    push_cast at hm
    linarith

/-- **The converse: the single-atom criterion is sufficient.**  `SESSION 205`.

`204` supplied the direction from a valid bound to the criterion.  This is the
other one, and with it `ISSUES` `#20`'s LP characterisation is machine-checked
in both directions: `a·m + b·m² ≤ [m = 1]` for every `m ≥ 1` **iff**
`LinearBound a b`.

The proof is the grouping `#20` describes.  `N`, `N⊛` and `N_sc` are all sums
over the atoms — `N_eq_sum_H`, `Nstar_eq_sum_H_sq` and `Nsc_eq_sum_mass_one` —
so the bound holds termwise, at `m = H γ`, and every atom in the support has
`m ≥ 1`. -/
theorem linearBound_of_mass_test {a b : ℝ}
    (h : ∀ m : ℕ, 1 ≤ m → a * m + b * (m * m) ≤ if m = 1 then 1 else 0) :
    LinearBound a b := by
  classical
  intro D
  have hN : (D.N : ℝ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℝ) := by
    rw [Blindness.N_eq_sum_H]; push_cast; rfl
  have hS : (D.Nstar : ℝ) = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℝ) * D.H γ) := by
    rw [Blindness.Nstar_eq_sum_H_sq]; push_cast; rfl
  have hC : (D.Nsc : ℝ)
      = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then (1:ℝ) else 0) := by
    have := Blindness.Nsc_eq_sum_mass_one D
    have h2 : ((D.Nsc : ℤ) : ℝ)
        = ((∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then (1:ℤ) else 0) : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [Int.cast_natCast] at h2
    rw [h2]
    push_cast
    exact Finset.sum_congr rfl fun γ _ => by by_cases hg : D.H γ = 1 <;> simp [hg]
  rw [hN, hS, hC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 1 ≤ D.H γ := by
    have : γ ∈ D.ordinates := Multiset.mem_toFinset.1 hγ
    have hcount : 0 < D.ordinates.count γ := Multiset.count_pos.2 this
    rw [D.H_eq_count γ]
    omega
  have := h (D.H γ) hpos
  by_cases hg : D.H γ = 1 <;> simp only [hg, if_pos, if_neg] at this ⊢ <;>
    [skip; skip] <;> push_cast at this ⊢ <;> linarith

/-! ### Optimality -/


/-- **The feasible set, in three inequalities — and only masses `1` and `2`
bind.**  `SESSION 206`.

With `204` and `205` the criterion is `a·m + b·m² ≤ [m = 1]` at every `m ≥ 1`,
which is infinitely many constraints.  Three of them suffice:

    LinearBound a b  ↔  b ≤ 0  ∧  a + b ≤ 1  ∧  a + 2b ≤ 0

`b ≤ 0` is forced by letting the mass grow: if `b > 0` then `a·m + b·m²` is
eventually positive, and every `m ≥ 2` demands it be `≤ 0`.  Given `b ≤ 0`, the
constraint at mass `m ≥ 2` reads `m·(a + b·m) ≤ 0`, and `b·m ≤ 2b`, so mass `2`
implies all of them.

**This is why `prop1_LP_optimal` needed exactly two witnesses.**  `200`–`203`
established that the optimality is a fact about the class; this says which two
members of the class carry it, and that the rest are redundant rather than
merely unused. -/
theorem linearBound_iff (a b : ℝ) :
    LinearBound a b ↔ (b ≤ 0 ∧ a + b ≤ 1 ∧ a + 2 * b ≤ 0) := by
  constructor
  · intro h
    refine ⟨?_, linearBound_le_one h, linearBound_mass2 h⟩
    by_contra hb
    push_neg at hb
    obtain ⟨n, hn⟩ := exists_nat_gt ((-a) / b)
    set m : ℕ := max n 2 with hm
    have hm2 : 2 ≤ m := le_max_right _ _
    have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left n 2
    have hmpos : (0 : ℝ) < m := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith
    have hgt : (-a) / b < (m : ℝ) := lt_of_lt_of_le hn hmn
    have hkey : -a < b * m := by
      rw [div_lt_iff₀ hb] at hgt
      linarith
    have hne : m ≠ 1 := by omega
    have := linearBound_mass m h
    rw [if_neg hne] at this
    nlinarith [this, hmpos, hkey]
  · rintro ⟨hb, h1, h2⟩
    refine linearBound_of_mass_test fun m hm => ?_
    by_cases hone : m = 1
    · rw [if_pos hone]
      subst hone
      push_cast
      linarith
    · rw [if_neg hone]
      have hm2 : 2 ≤ m := by omega
      have hm2' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have hbm : b * (m : ℝ) ≤ 2 * b := by
        nlinarith [mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 hm2')]
      have habm : a + b * (m : ℝ) ≤ 0 := by linarith
      have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hprod := mul_le_mul_of_nonneg_left habm (le_of_lt hmpos)
      simp only [mul_zero] at hprod
      nlinarith [hprod]

/-- **`prop1` reproduced from the characterisation.**  `SESSION 207`.  `(2, −1)`
satisfies the three inequalities of `linearBound_iff`, so the characterisation
returns the bound the project started from.  `linearBound_prop1` proves the same
thing directly from `ZeroData.prop1`; this is the LP route to it, and having
both is the check that `206`'s three inequalities are the right three. -/
theorem linearBound_prop1_via_iff : LinearBound 2 (-1) :=
  (linearBound_iff 2 (-1)).2 ⟨by norm_num, by norm_num, by norm_num⟩


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

/-- **The LP's value, not merely a bound on it.**  `SESSION 207`.

`prop1_LP_optimal` says every feasible `(a, b)` has `a + b·C ≤ 2 − C`.  With
`206`'s characterisation the other half is available too: `(2, −1)` is feasible
and attains it.  So for `C ∈ [1, 2]` the two-moment LP has value **exactly**
`2 − C`, and `prop1` is an optimal point rather than merely an unbeaten one.

This is what `ISSUES` `#20`'s "`(α, β) = (2, −1)` is optimal at every `C ≤ 2`"
asserts, now as a single machine-checked statement. -/
theorem prop1_LP_value {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    IsGreatest {v : ℝ | ∃ a b : ℝ, LinearBound a b ∧ v = a + b * C} (2 - C) := by
  constructor
  · exact ⟨2, -1, linearBound_prop1_via_iff, by ring⟩
  · rintro v ⟨a, b, hab, rfl⟩
    exact prop1_LP_optimal hab hC1 hC2

/-! ### The three-moment program — `SESSION 208`

`LEADS.md` names `LinearBound3 a b c` over `(N, N⊛, Σm³)` as the extension and
`ISSUES` `#20` calls the third moment the currency that could improve `prop1`.
The object had never been defined.  It is defined here, together with the
question `206` makes askable: does the feasible set again collapse to finitely
many constraints? -/

/-- A linear bound in the three moments, asserted for every configuration. -/
def LinearBound3 (a b c : ℝ) : Prop :=
  ∀ D : ZeroData, a * D.N + b * D.Nstar + c * Blindness.thirdMoment D ≤ D.Nsc

/-- **The single-atom test at every mass, for three moments.**  `SESSION 208`.
The pure on-line atom `config m 0 a` has `N = m`, `N⊛ = m²`, `Σm³ = m³` and
`N_sc = [m = 1]`. -/
theorem linearBound3_mass (m : ℕ) {a b c : ℝ} (h : LinearBound3 a b c) :
    a * m + b * (m * m) + c * (m * m * m) ≤ if m = 1 then 1 else 0 := by
  have hm := h (Blindness.config m 0 0)
  rw [Blindness.config_N, Blindness.config_Nstar_pure,
    Blindness.config_Nsc_pure, Blindness.config_thirdMoment_pure] at hm
  by_cases h1 : m = 1
  · rw [if_pos h1]; rw [if_pos h1] at hm; push_cast at hm; linarith
  · rw [if_neg h1]; rw [if_neg h1] at hm; push_cast at hm; linarith

/-- **The three-moment feasible set does not collapse to masses `1` and `2`.**
`SESSION 208`.

`linearBound_iff` reduces the two-moment criterion to three inequalities,
because with `b ≤ 0` the constraint `m·(a + b·m) ≤ 0` is hardest at `m = 2`.
That argument has no analogue here: with `c ≤ 0` the mass-`m` constraint is
`m·(a + b·m + c·m²) ≤ 0`, and `a + b·m + c·m²` is a **concave** function of `m`,
so its maximum over `m ≥ 2` can sit strictly inside the range.

Witness: `(a, b, c) = (−11, 7, −1)` has `c ≤ 0`, passes the mass-`1` and
mass-`2` tests, and **fails at mass `3`** — `−33 + 63 − 27 = 3 > 0`.

So `(−11, 7, −1)` is not a `LinearBound3`, by `linearBound3_mass` at `m = 3`,
even though the two constraints that settle the two-moment program accept it.
Any characterisation of the three-moment feasible set needs constraints beyond
mass `2`, and how far beyond depends on `b/c`. -/
theorem linearBound3_not_reducible_to_mass_two :
    ((-1 : ℝ) ≤ 0)
      ∧ ((-11 : ℝ) + 7 + (-1) ≤ 1)
      ∧ ((-11 : ℝ) * 2 + 7 * (2 * 2) + (-1) * (2 * 2 * 2) ≤ 0)
      ∧ ¬ ((-11 : ℝ) * 3 + 7 * (3 * 3) + (-1) * (3 * 3 * 3) ≤ 0)
      ∧ ¬ LinearBound3 (-11) 7 (-1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun h => ?_⟩
  have := linearBound3_mass 3 h
  rw [if_neg (by norm_num)] at this
  norm_num at this

/-- **The three-moment route cannot beat `2 − C`.**  `SESSION 209`.

`Blindness.three_Nstar_le_thirdMoment_add_two_N` gives `Σm³ ≥ 3N⊛ − 2N` for
every configuration, so `C₃ ≥ 3C − 2`; its docstring reads off that the optimum
stays at `prop1`'s `2 − C`.  That was prose.  Here it is.

Since a feasible `c` is non-positive, the objective is best at the smallest
admissible `C₃`, namely `3C − 2`.  Write the objective there:

    a + b·C + c·(3C − 2)  =  (a − 2c) + (b + 3c)·C

and put `A = a − 2c`, `B = b + 3c`.  The substitution is chosen because `c`
cancels out of the first two mass constraints:

    mass 1:  a + b + c  =  A + B  ≤ 1
    mass 2:  2a + 4b + 8c ≤ 0  ⟺  A + 2B ≤ 0

which are exactly the two constraints that settle the two-moment program
(`206`).  So the same case split closes it, and no third-moment supplier moves
this route however good its `C₃` — the constraint `C₃ ≥ 3C − 2` is what makes
the substitution land on the two-moment feasible set.

Note what this does **not** need: `208` showed the mass-`1` and mass-`2`
constraints do not settle the three-moment feasible set, and no description of
that set is used here.  Only those two constraints are consumed, and the higher
ones can only shrink the set further. -/
theorem linearBound3_no_gain {a b c C : ℝ} (h : LinearBound3 a b c)
    (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    (a - 2 * c) + (b + 3 * c) * C ≤ 2 - C := by
  have hm1 := linearBound3_mass 1 h
  have hm2 := linearBound3_mass 2 h
  rw [if_pos rfl] at hm1
  rw [if_neg (by norm_num)] at hm2
  push_cast at hm1 hm2
  -- `A + B ≤ 1` and `A + 2B ≤ 0`, with `A = a − 2c`, `B = b + 3c`
  have h1 : (a - 2 * c) + (b + 3 * c) ≤ 1 := by linarith
  have h2 : (a - 2 * c) + 2 * (b + 3 * c) ≤ 0 := by linarith
  rcases le_or_gt (-1 : ℝ) (b + 3 * c) with hcase | hcase
  · nlinarith [h2, hcase, hC2]
  · nlinarith [h1, hcase, hC1]

/-- `prop1` read as a three-moment bound that ignores the third moment.
`SESSION 209`. -/
theorem prop1_as_linearBound3 : LinearBound3 2 (-1) 0 := by
  intro D
  have h := ZeroData.prop1 D
  have hcast : (2 * (D.N : ℝ)) - (D.Nstar : ℝ) ≤ (D.Nsc : ℝ) := by exact_mod_cast h
  simp only [neg_mul, one_mul, zero_mul, add_zero]
  linarith

/-- **The three-moment LP has the same value as the two-moment one.**
`SESSION 209`.

`IsGreatest` at `2 − C`: `linearBound3_no_gain` is the ceiling and
`prop1_as_linearBound3` attains it with `c = 0`.  So the third moment buys
nothing on this route, and that is now a value statement rather than a bound —
the same upgrade `207` made for two moments. -/
theorem linearBound3_LP_value {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    IsGreatest {v : ℝ | ∃ a b c : ℝ, LinearBound3 a b c
        ∧ v = (a - 2 * c) + (b + 3 * c) * C} (2 - C) := by
  constructor
  · exact ⟨2, -1, 0, prop1_as_linearBound3, by ring⟩
  · rintro v ⟨a, b, c, habc, rfl⟩
    exact linearBound3_no_gain habc hC1 hC2

/-! ### Order four — `SESSION 210`

`209` killed the third moment.  The question it leaves is whether the argument
was special to `k = 3`.  It was not, and the reason is visible in how the
minorant is chosen: `Σm³ ≥ 3N⊛ − 2N` comes from the linear-in-`(m², m)` function
agreeing with `m³` **at `m = 1` and `m = 2`**, which is exactly the pair of
constraints that settles the two-moment program.  Order four repeats it with
`Σm⁴ ≥ 7N⊛ − 6N`. -/

/-- A linear bound in `(N, N⊛, Σm⁴)`. -/
def LinearBound4 (a b c : ℝ) : Prop :=
  ∀ D : ZeroData, a * D.N + b * D.Nstar + c * Blindness.fourthMoment D ≤ D.Nsc

/-- The single-atom test at every mass, for order four.  `SESSION 210`. -/
theorem linearBound4_mass (m : ℕ) {a b c : ℝ} (h : LinearBound4 a b c) :
    a * m + b * (m * m) + c * (m * m * m * m) ≤ if m = 1 then 1 else 0 := by
  have hm := h (Blindness.config m 0 0)
  rw [Blindness.config_N, Blindness.config_Nstar_pure,
    Blindness.config_Nsc_pure, Blindness.config_fourthMoment_pure] at hm
  by_cases h1 : m = 1
  · rw [if_pos h1]; rw [if_pos h1] at hm; push_cast at hm; linarith
  · rw [if_neg h1]; rw [if_neg h1] at hm; push_cast at hm; linarith

/-- `prop1` read as an order-four bound that ignores the fourth moment. -/
theorem prop1_as_linearBound4 : LinearBound4 2 (-1) 0 := by
  intro D
  have h := ZeroData.prop1 D
  have hcast : (2 * (D.N : ℝ)) - (D.Nstar : ℝ) ≤ (D.Nsc : ℝ) := by exact_mod_cast h
  simp only [neg_mul, one_mul, zero_mul, add_zero]
  linarith

/-- **The order-four route cannot beat `2 − C` either.**  `SESSION 210`.

`Blindness.seven_Nstar_le_fourthMoment_add_six_N` gives `C₄ ≥ 7C − 6`, and a
feasible `c` is non-positive, so the objective is best at `C₄ = 7C − 6`:

    a + b·C + c·(7C − 6)  =  (a − 6c) + (b + 7c)·C

With `A = a − 6c`, `B = b + 7c` the `c` cancels out of the first two mass
constraints, exactly as at order three:

    mass 1:  a + b + c    = A + B  ≤ 1
    mass 2:  2a + 4b + 16c ≤ 0  ⟺  A + 2B ≤ 0

The cancellation is not a coincidence of the numbers: the minorant is defined to
be tight at `m = 1` and `m = 2`, so subtracting it leaves those two constraints
untouched. -/
theorem linearBound4_no_gain {a b c C : ℝ} (h : LinearBound4 a b c)
    (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    (a - 6 * c) + (b + 7 * c) * C ≤ 2 - C := by
  have hm1 := linearBound4_mass 1 h
  have hm2 := linearBound4_mass 2 h
  rw [if_pos rfl] at hm1
  rw [if_neg (by norm_num)] at hm2
  push_cast at hm1 hm2
  have h1 : (a - 6 * c) + (b + 7 * c) ≤ 1 := by linarith
  have h2 : (a - 6 * c) + 2 * (b + 7 * c) ≤ 0 := by linarith
  rcases le_or_gt (-1 : ℝ) (b + 7 * c) with hcase | hcase
  · nlinarith [h2, hcase, hC2]
  · nlinarith [h1, hcase, hC1]

/-- **The order-four LP has the same value, `2 − C`.**  `SESSION 210`. -/
theorem linearBound4_LP_value {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    IsGreatest {v : ℝ | ∃ a b c : ℝ, LinearBound4 a b c
        ∧ v = (a - 6 * c) + (b + 7 * c) * C} (2 - C) := by
  constructor
  · exact ⟨2, -1, 0, prop1_as_linearBound4, by ring⟩
  · rintro v ⟨a, b, c, habc, rfl⟩
    exact linearBound4_no_gain habc hC1 hC2

/-! ### Every order — `SESSION 211`

`209` and `210` did orders three and four by hand and made the mechanism
visible: the minorant is tight at `m = 1` and `m = 2`, the two masses `206`'s
characterisation constrains, so subtracting it leaves those constraints alone.
`Blindness.moment_minorant` supplies that minorant at every order.  Here is the
LP consequence, once. -/

/-- A linear bound in `(N, N⊛, Σm^k)`. -/
def LinearBoundK (k : ℕ) (a b c : ℝ) : Prop :=
  ∀ D : ZeroData, a * D.N + b * D.Nstar + c * Blindness.momentK D k ≤ D.Nsc

/-- The single-atom test at every mass, for order `k`.  `SESSION 211`. -/
theorem linearBoundK_mass {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {a b c : ℝ}
    (h : LinearBoundK k a b c) :
    a * m + b * (m * m) + c * (m ^ k) ≤ if m = 1 then 1 else 0 := by
  have hm := h (Blindness.config m 0 0)
  rw [Blindness.config_N, Blindness.config_Nstar_pure, Blindness.config_Nsc_pure,
    Blindness.config_momentK_pure m hk] at hm
  by_cases h1 : m = 1
  · rw [if_pos h1]; rw [if_pos h1] at hm; push_cast at hm; linarith
  · rw [if_neg h1]; rw [if_neg h1] at hm; push_cast at hm; linarith

/-- `prop1` read as an order-`k` bound that ignores the `k`-th moment. -/
theorem prop1_as_linearBoundK (k : ℕ) : LinearBoundK k 2 (-1) 0 := by
  intro D
  have h := ZeroData.prop1 D
  have hcast : (2 * (D.N : ℝ)) - (D.Nstar : ℝ) ≤ (D.Nsc : ℝ) := by exact_mod_cast h
  simp only [neg_mul, one_mul, zero_mul, add_zero]
  linarith

/-- **No moment, at any order, beats `2 − C`.**  `SESSION 211`.

With `A + 1 = 2^(k−1)`, `Blindness.moment_obstruction` gives
`C_k ≥ A·C − (A−1)`.  A feasible `c` is non-positive, so the objective is best
there, and

    a + b·C + c·(A·C − (A−1))  =  (a + (A−1)·(−c)) + (b + A·c)·C

Writing `P = a − (A−1)c` and `Q = b + Ac`, the `c` cancels out of the mass-`1`
and mass-`2` constraints for the same reason at every order:

    mass 1:  a + b + c        = P + Q  ≤ 1
    mass 2:  2a + 4b + 2^k·c ≤ 0  ⟺  P + 2Q ≤ 0

because `A + 1 = 2^(k−1)`.  `209` and `210` are the `k = 3` and `k = 4` cases. -/
theorem linearBoundK_no_gain {k A : ℕ} (hk : 2 ≤ k) (hA : A + 1 = 2 ^ (k - 1))
    {a b c C : ℝ} (h : LinearBoundK k a b c) (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    (a - ((A : ℝ) - 1) * c) + (b + (A : ℝ) * c) * C ≤ 2 - C := by
  have hm1 := linearBoundK_mass (by omega) 1 h
  have hm2 := linearBoundK_mass (by omega) 2 h
  rw [if_pos rfl] at hm1
  rw [if_neg (by norm_num)] at hm2
  push_cast at hm1 hm2
  simp only [one_pow, one_mul, mul_one] at hm1
  have hpow : ((2 : ℝ) ^ k) = 2 * (A + 1) := by
    have : ((A : ℕ) + 1 : ℕ) = 2 ^ (k - 1) := hA
    have hk' : k - 1 + 1 = k := by omega
    have : ((2 : ℝ)) ^ (k - 1) = ((A : ℝ) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hA.symm
    calc ((2 : ℝ) ^ k) = 2 ^ (k - 1 + 1) := by rw [hk']
      _ = 2 ^ (k - 1) * 2 := by ring
      _ = 2 * ((A : ℝ) + 1) := by rw [this]; ring
  rw [hpow] at hm2
  have h1 : (a - ((A : ℝ) - 1) * c) + (b + (A : ℝ) * c) ≤ 1 := by nlinarith [hm1]
  have h2 : (a - ((A : ℝ) - 1) * c) + 2 * (b + (A : ℝ) * c) ≤ 0 := by nlinarith [hm2]
  rcases le_or_gt (-1 : ℝ) (b + (A : ℝ) * c) with hcase | hcase
  · nlinarith [h2, hcase, hC2]
  · nlinarith [h1, hcase, hC1]

/-- **The order-`k` LP has value `2 − C`, for every `k ≥ 2`.**  `SESSION 211`. -/
theorem linearBoundK_LP_value {k A : ℕ} (hk : 2 ≤ k) (hA : A + 1 = 2 ^ (k - 1))
    {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C ≤ 2) :
    IsGreatest {v : ℝ | ∃ a b c : ℝ, LinearBoundK k a b c
        ∧ v = (a - ((A : ℝ) - 1) * c) + (b + (A : ℝ) * c) * C} (2 - C) := by
  constructor
  · exact ⟨2, -1, 0, prop1_as_linearBoundK k, by ring⟩
  · rintro v ⟨a, b, c, habc, rfl⟩
    exact linearBoundK_no_gain hk hA habc hC1 hC2

/-- **A feasible `c` is non-positive, for `k ≥ 3`.**  `SESSION 212`.

The mass test at `m ≥ 2` reads `m·(a + b·m + c·m^(k−1)) ≤ 0`.  If `c > 0` the
inner expression is eventually positive, so no such bound is feasible.  `206`
ran the same argument one degree lower.

`k = 2` is excluded on purpose: there `c` merges into `b` and nothing forces its
sign. -/
theorem linearBoundK_c_nonpos {k : ℕ} (hk : 3 ≤ k) {a b c : ℝ}
    (h : LinearBoundK k a b c) : c ≤ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨n, hn⟩ := exists_nat_gt ((|b| + |a| + 1) / c)
  set m : ℕ := max n 2 with hmdef
  have hm2 : 2 ≤ m := le_max_right _ _
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left n 2
  have hm2' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hgt : (|b| + |a| + 1) / c < (m : ℝ) := lt_of_lt_of_le hn hmn
  have hkey : |b| + |a| + 1 < c * m := by
    rw [div_lt_iff₀ hc] at hgt; linarith
  -- the test at mass `m`, with `m^k ≥ m^3` absorbed
  have hmass := linearBoundK_mass (by omega) m h
  rw [if_neg (by omega : ¬ m = 1)] at hmass
  push_cast at hmass
  have hcube : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ k :=
    pow_le_pow_right₀ (by linarith) hk
  have hstep : c * ((m : ℝ) ^ 3) ≤ c * ((m : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hcube (le_of_lt hc)
  have hcubed : a * (m : ℝ) + b * ((m : ℝ) * (m : ℝ)) + c * ((m : ℝ) ^ 3) ≤ 0 := by
    have h' := hmass
    ring_nf at h' ⊢
    linarith [h', hstep]
  -- `c·m³` outgrows what `−a·m − b·m²` can pay for
  have hsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hgrow : (|b| + |a| + 1) * (m : ℝ) ^ 2 < (c * (m : ℝ)) * (m : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hkey hsq
  have hcm : (c * (m : ℝ)) * (m : ℝ) ^ 2 = c * ((m : ℝ) ^ 3) := by ring
  have hnegA : -(a * (m : ℝ)) ≤ |a| * (m : ℝ) := by
    nlinarith [neg_abs_le a, hmpos]
  have hnegB : -(b * ((m : ℝ) * (m : ℝ))) ≤ |b| * (m : ℝ) ^ 2 := by
    nlinarith [neg_abs_le b, hsq]
  have habs : (0 : ℝ) ≤ |a| := abs_nonneg a
  have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm2', hmpos]
  nlinarith [hcubed, hgrow, hcm, hnegA, hnegB, habs, hmm, hsq]

/-- **`W35` is answered: no realizable `(C, C_k)` pair helps.**  `SESSION 212`.

`LEADS.md`'s `W35` left "the realizable region of `(C, C₃)` for integer masses"
as the named next step.  It is not needed.  Whatever a configuration's actual
`C_k` is, `Blindness.moment_obstruction` puts it at or above `A·C − (A−1)`, and
a feasible `c` is non-positive, so moving `C_k` up from that floor can only make
the delivered bound smaller.  The floor already gives `2 − C`.

So the bound delivered at **any** admissible `C_k` is at most `2 − C`, and the
realizable region cannot rescue the route however it turns out. -/
theorem linearBoundK_no_gain_at_any_moment {k A : ℕ} (hk : 3 ≤ k)
    (hA : A + 1 = 2 ^ (k - 1)) {a b c C Ck : ℝ} (h : LinearBoundK k a b c)
    (hC1 : 1 ≤ C) (hC2 : C ≤ 2) (hCk : (A : ℝ) * C - ((A : ℝ) - 1) ≤ Ck) :
    a + b * C + c * Ck ≤ 2 - C := by
  have hc : c ≤ 0 := linearBoundK_c_nonpos hk h
  have hbase := linearBoundK_no_gain (by omega) hA h hC1 hC2
  have hdrop : c * Ck ≤ c * ((A : ℝ) * C - ((A : ℝ) - 1)) :=
    mul_le_mul_of_nonpos_left hCk hc
  nlinarith [hbase, hdrop]


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

/-- **The class the LP conclusion fails on is the `RH`-and-simple class.**
`SESSION 203`.

`BoundedMult 1` is not merely a technical restriction: it **is** `N_sc = N`.

Forward is `201` plus `N_sc ≤ N`.  Backward is `Nsc_eq_N_iff` composed with
`ordinates_simple_iff` and `H_eq_count`: `N_sc = N` says every ordinate is
singly occupied, and an unoccupied ordinate has `H = 0`, so `H ≤ 1` everywhere.
No hypothesis beyond `ZeroData`'s own structure is needed in either direction.

Read with `prop1_LP_threshold_at_two`, this says where the two-moment optimality
lives: it holds on classes admitting a doubled zero and fails on the class of
configurations that already satisfy the ledger's target.  The argument that the
two-moment world is exhausted is an argument about configurations the project is
trying to rule out. -/
theorem boundedMult_one_iff_Nsc_eq_N (D : ZeroData) :
    BoundedMult 1 D ↔ D.Nsc = D.N := by
  constructor
  · intro h
    have h1 := Nsc_eq_N_of_boundedMult_one D h
    have h2 : D.Nsc ≤ D.N := Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  · intro h γ
    rw [ZeroData.H_eq_count]
    by_cases hγ : γ ∈ D.ordinates
    · exact le_of_eq
        ((ZeroData.ordinates_simple_iff D).2 ((ZeroData.Nsc_eq_N_iff D).1 h) γ hγ)
    · simp [Multiset.count_eq_zero_of_notMem hγ]



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

/-- **E11's pincer, sharpened for the multiplicity family.**  `SESSION 243`.

`LEADS.md` files against E11 that *"the 'ceilings from below' jaw works; a
'cheap realizability from above' jaw does not exist"* — no free classical
invariant excludes the ceiling's extremal configuration.  Within the
multiplicity family that is now a theorem rather than an observation.

`Gauge.pairOnly` — one mirror pair, `H = 2` — is the configuration that makes
`prop1` tight.  A cap `BoundedMult M` excludes it only if `M ≤ 1`, and `203`
proved `BoundedMult 1 ↔ N_sc = N`.  So **the cheapest multiplicity hypothesis
that excludes the extremal configuration is the ledger's own target**: the jaw
does not merely fail to be cheap, it costs the whole problem.

This does not settle E11 for every classical invariant, only for caps on
multiplicity.  Named rather than generalised. -/
theorem mult_cap_excluding_pairOnly {M : ℕ} (h : ¬ BoundedMult M Gauge.pairOnly)
    (D : ZeroData) (hD : BoundedMult M D) : D.Nsc = D.N := by
  have hM : M ≤ 1 := by
    by_contra hM
    push_neg at hM
    exact h fun γ => by
      by_cases hγ : γ = 0
      · subst hγ; rw [Gauge.pairOnly_H]; omega
      · have : Gauge.pairOnly.H γ = 0 := by
          rw [ZeroData.H_eq_count]
          show Multiset.count γ (Multiset.map Prod.snd
            (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)) = 0
          simp [hγ]
        omega
  have hD1 : BoundedMult 1 D := fun γ => le_trans (hD γ) hM
  exact (boundedMult_one_iff_Nsc_eq_N D).1 hD1

/-- **The moment route is walled at every order.** -/
theorem moment_route_walled {k : ℕ} (hk : 3 ≤ k) :
    Blindness.factMoment single k = 0 ∧
      Blindness.factMoment Gauge.pairOnly k = 0 :=
  ⟨single_factMoment hk, pairOnly_factMoment hk⟩

end Optimal
end Riemann
