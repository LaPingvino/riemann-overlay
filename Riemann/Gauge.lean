/-
# The gauge boundary (List E, E1/E3; X's soundness half, made sharp)

E3 says `β` is gauge: a coordinate no instrument in the class can measure.
`Basic.lean` proves the soundness half — `N`, `N⊛` and `N_sc` are functionals
of `μ_T` alone, so they cannot see `β`.  This file supplies the other side of
the boundary: an **explicit pair of zero configurations with the same `μ_T`
and different `NscStd`**.

The pair is the haunted ordinate itself: three zeros at one height, either as a
triple on the line, or as a simple on-line zero flanked by a mirror pair.  `μ_T`
records "one atom of mass 3" in both cases and cannot tell them apart —
exactly the degeneracy `Zeta23.ZeroSide.TightMult` proves no certificate of
that class can break.

So the gauge group is not trivial and the boundary is not an artefact of our
proofs: it is realised by two legitimate, reflection-symmetric configurations.
-/
import Riemann.Basic

namespace Riemann
namespace Gauge

open Multiset

/-- Three zeros stacked on the critical line at height `0`. -/
noncomputable def triple : ZeroData where
  Z := Multiset.replicate 3 ((1/2 : ℝ), (0 : ℝ))
  refl_inv := by
    rw [Multiset.map_replicate]
    norm_num [refl]

/-- A simple on-line zero at height `0`, haunted by one mirror pair. -/
noncomputable def haunted : ZeroData where
  Z := {((1/2 : ℝ), (0:ℝ)), ((1/4 : ℝ), (0:ℝ)), ((3/4 : ℝ), (0:ℝ))}
  refl_inv := by
    show Multiset.map refl (((1/2 : ℝ), (0:ℝ)) ::ₘ ((1/4 : ℝ), (0:ℝ)) ::ₘ
      ((3/4 : ℝ), (0:ℝ)) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons]
    norm_num [refl]
    exact Multiset.cons_swap _ _ _

/-- **Same `μ_T`.**  Both configurations are one atom of mass three at `0`. -/
theorem ordinates_eq : triple.ordinates = haunted.ordinates := by
  show Multiset.map Prod.snd (Multiset.replicate 3 ((1/2 : ℝ), (0:ℝ))) = _
  rw [Multiset.map_replicate]
  show Multiset.replicate 3 (0:ℝ) = Multiset.map Prod.snd
    (((1/2 : ℝ), (0:ℝ)) ::ₘ ((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)
  simp [Multiset.replicate_succ]

/-- **`N_sc` cannot tell them apart** — it is a `μ_T`-functional, so the gauge
move is invisible to it.  No computation needed: this is
`Nsc_eq_ordinate_functional` plus `ordinates_eq`. -/
theorem Nsc_gauge_invariant : triple.Nsc = haunted.Nsc := by
  rw [ZeroData.Nsc_eq_ordinate_functional, ZeroData.Nsc_eq_ordinate_functional,
    ordinates_eq]

/-- Three stacked on-line zeros: no zero of multiplicity one, so `NscStd = 0`. -/
theorem NscStd_triple : triple.NscStd = 0 := by
  classical
  unfold ZeroData.NscStd
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro p hp hc
  have hp' : p = ((1/2 : ℝ), (0:ℝ)) := Multiset.eq_of_mem_replicate hp
  have hcount : Multiset.count p triple.Z = 3 := by
    show Multiset.count p (Multiset.replicate 3 ((1/2 : ℝ), (0:ℝ))) = 3
    rw [hp', Multiset.count_replicate_self]
  rw [hcount] at hc
  exact absurd hc.2 (by norm_num)

/-- The haunted configuration: the on-line zero *is* simple, so `NscStd = 1`. -/
theorem NscStd_haunted : haunted.NscStd = 1 := by
  classical
  unfold ZeroData.NscStd
  show Multiset.card (Multiset.filter _ (((1/2 : ℝ), (0:ℝ)) ::ₘ ((1/4 : ℝ), (0:ℝ)) ::ₘ
    ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)) = 1
  rw [Multiset.filter_cons_of_pos, Multiset.filter_cons_of_neg,
    Multiset.filter_cons_of_neg]
  · simp
  · norm_num
  · norm_num
  · refine ⟨rfl, ?_⟩
    show Multiset.count ((1/2 : ℝ), (0:ℝ)) haunted.Z = 1
    show Multiset.count ((1/2 : ℝ), (0:ℝ)) (((1/2 : ℝ), (0:ℝ)) ::ₘ ((1/4 : ℝ), (0:ℝ)) ::ₘ
      ((3/4 : ℝ), (0:ℝ)) ::ₘ 0) = 1
    rw [Multiset.count_cons_self, Multiset.count_cons_of_ne (by norm_num),
      Multiset.count_cons_of_ne (by norm_num)]
    simp

/-- **The gauge boundary, exhibited.**  Two reflection-symmetric configurations
with the *same* `μ_T` and *different* `NscStd`: the literature's notion reads a
coordinate the class cannot see, and `N_sc` does not. -/
theorem NscStd_not_gauge_invariant :
    triple.ordinates = haunted.ordinates ∧ triple.NscStd ≠ haunted.NscStd := by
  refine ⟨ordinates_eq, ?_⟩
  rw [NscStd_triple, NscStd_haunted]
  norm_num

/-! ### R16 audit: is `N + N_off ≤ N⊛` (`offline_le`) tight?

The directive says a termwise-proved bound should be regrouped over atoms before
its constant is believed. `N_add_Noff_le_Nstar` charges each off-line zero once;
off-line zeros come in pairs, so a `/2` looks plausible. **It is not there:**
the lone mirror pair saturates the bound. -/

/-- One mirror pair at a single ordinate — nothing else. -/
noncomputable def pairOnly : ZeroData where
  Z := {((1/4 : ℝ), (0:ℝ)), ((3/4 : ℝ), (0:ℝ))}
  refl_inv := by
    show Multiset.map refl (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_cons]
    norm_num [refl]
    exact Multiset.cons_swap _ _ _

@[simp] lemma pairOnly_N : pairOnly.N = 2 := by
  show Multiset.card (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0) = 2
  simp

lemma pairOnly_H : pairOnly.H 0 = 2 := by
  classical
  show Multiset.card (Multiset.filter _ (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)) = 2
  norm_num [Multiset.filter_cons, Multiset.filter_singleton]

lemma pairOnly_Noff : pairOnly.Noff = 2 := by
  classical
  show Multiset.card (Multiset.filter _ (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)) = 2
  norm_num [Multiset.filter_cons, Multiset.filter_singleton]

lemma pairOnly_Nstar : pairOnly.Nstar = 4 := by
  show ((((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0).map fun p => pairOnly.H p.2).sum = 4
  rw [Multiset.map_cons, Multiset.map_cons]
  simp [pairOnly_H]

/-- **`offline_le` is tight — the `/2` is not there.**  `N + N_off = N⊛` for a
single mirror pair, so no constant better than `1` holds in
`N + N_off ≤ N⊛`, and the `(C−1)` in `Family.offline_le` cannot be improved to
`(C−1)/2`.

**Optimality is no longer a docstring claim:** see `Riemann/Optimal.lean`,
`prop1_LP_optimal` — and it holds with *no* sign hypothesis on `β`.

R16 calibration: regrouping over atoms pays only when the termwise charge
*under*-counts. Here a lone pair's own two terms already saturate the
inequality, so there is nothing for grouping to collect. -/
theorem offline_le_tight : pairOnly.N + pairOnly.Noff = pairOnly.Nstar := by
  rw [pairOnly_N, pairOnly_Noff, pairOnly_Nstar]

lemma pairOnly_Nsc : pairOnly.Nsc = 0 := by
  classical
  show Multiset.card (Multiset.filter _ (((1/4 : ℝ), (0:ℝ)) ::ₘ ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)) = 0
  norm_num [Multiset.filter_cons, Multiset.filter_singleton]

/-- **`prop1` is tight** — and per the R16 audit it is also LP-optimal in the two
moments `(N, N⊛)`: no linear bound `Nsc ≥ αN + βN⊛` beats `(α,β) = (2,−1)`
anywhere in the useful regime `C ≤ 2`, and equality is attained by every
configuration built from atoms of mass `1` and `2`.

Consequence: **improving Proposition 1 itself requires data beyond the two
moments** — a third moment `Σ m³` — which is exactly [OPEN D]'s currency. The
reduction and the ceiling want the same missing input. -/
theorem prop1_tight : (2 * pairOnly.N : ℤ) - pairOnly.Nstar = pairOnly.Nsc := by
  rw [pairOnly_N, pairOnly_Nstar, pairOnly_Nsc]
  norm_num

end Gauge
end Riemann
