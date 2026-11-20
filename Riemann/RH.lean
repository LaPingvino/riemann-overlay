/-
# What the Riemann Hypothesis buys this ledger — as a hypothesis

`SESSION 445`.  On 2026-11-20 Levent Alpöge released a Lean development whose top
level is `theorem riemannHypothesis : RiemannHypothesis`, stated with Mathlib's
own definition.  It has not been independently checked here (`COMPARISON.md`).
`Assumptions.lean`'s house rule puts open problems in `Gaps.lean` as hypotheses
rather than in the axiom list, so `RiemannHypothesis` enters this file as the
explicit hypothesis `h` of each theorem below, and the axiom cone of each is the
kernel's three standard axioms (`audit/PrintAxioms.lean`).

What it buys, in this project's vocabulary:

* `zetaZeroData_Noff_eq_zero` — every window's off-line count is `0`;
* `noHaunted_zeta_of_RH` — hence `NoHaunted zetaFamily`, through the existing
  `Blindness.noHaunted_of_Noff_zero`;
* `Nsc_eq_NscStd_of_RH` — the two ledger rows count the same zeros in every window;
* `proportion_of_RH_zeta` — so the `Nsc` row reads the `NscStd` row's `0.6725`,
  through the existing `proportion_of_noHaunted_zeta`.

What it does not buy is the subject of the might-mean in `SESSION 445`: `h` says
where the zeros are and nothing about their multiplicity, so `NscStd`'s `0.6725`
is not moved by it, and per window `N_off = 0` admits `N⊛ > C·N` for every `C`
(`Blindness.noHaunted_no_starBound`), so no `StarBound` follows from it.
-/
import Riemann.Proportion

namespace Riemann

/-- **Under `h`, a zero in a zeta-23 window is on the line.**

`Zeta23.zerosIn` asks for `0 < Re ρ < 1`, which excludes both side conditions of
Mathlib's `RiemannHypothesis` — the trivial zeros `-2(n+1)` have negative real
part and the pole `1` has real part `1`. -/
theorem re_eq_half_of_mem_zerosIn (h : RiemannHypothesis) {T₁ T₂ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ Zeta23.zerosIn T₁ T₂) : ρ.re = 1 / 2 := by
  obtain ⟨⟨hz, h0, h1⟩, -, -⟩ := hρ
  refine h ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    linarith
  · rintro rfl
    simp at h1

/-- **Under `h`, no window of `zetaZeroData` has off-line mass.** -/
theorem zetaZeroData_Noff_eq_zero (h : RiemannHypothesis) :
    ∀ T, (zetaZeroData T).Noff = 0 := by
  intro T
  classical
  rw [ZeroData.Noff, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro p hp
  have hc : 0 < (zetaZeroData T).Z.count p := Multiset.count_pos.2 hp
  rw [zetaZeroData, ZeroData.ofMult_count] at hc
  split_ifs at hc with hs
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hs
    exact not_not.2 (re_eq_half_of_mem_zerosIn h ((Set.Finite.mem_toFinset _).1 hρ))
  · exact absurd hc (lt_irrefl 0)

/-- **Under `h`, `ζ` has no haunted ordinate**, by `zetaZeroData_Noff_eq_zero` and
`Blindness.noHaunted_of_Noff_zero`. -/
theorem noHaunted_zeta_of_RH (h : RiemannHypothesis) : NoHaunted zetaFamily :=
  fun T γ => Blindness.noHaunted_of_Noff_zero (zetaZeroData T)
    (zetaZeroData_Noff_eq_zero h T) γ

/-- **Under `h`, the two rows count the same zeros in every window**, by
`Blindness.Nsc_eq_NscStd_of_noHaunted`. -/
theorem Nsc_eq_NscStd_of_RH (h : RiemannHypothesis) (T : ℝ) :
    (zetaZeroData T).Nsc = (zetaZeroData T).NscStd :=
  Blindness.Nsc_eq_NscStd_of_noHaunted (zetaZeroData T)
    (Blindness.noHaunted_of_Noff_zero (zetaZeroData T) (zetaZeroData_Noff_eq_zero h T))

/-- **Under `h`, the `Nsc` row is `0.6725`**, against the `0.50875` that
`certified_nsc_unconditional` carries without it.  The composite of
`noHaunted_zeta_of_RH` and `proportion_of_noHaunted_zeta`; the input
`0.6725` is the `NscStd` row, `certified_std`, and `h` leaves it where it is. -/
theorem proportion_of_RH_zeta (h : RiemannHypothesis) :
    zetaFamily.toCounts.Proportion 0.6725 :=
  proportion_of_noHaunted_zeta (noHaunted_zeta_of_RH h)

end Riemann
