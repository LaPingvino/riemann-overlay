/-
# The proportion metric

The single optimisation target: the best proportion of zeta zeros certified
to be simple and on the critical line by lemmas whose dependency cone
contains **no `sorry`** (axioms of `Assumptions.lean` permitted, and counted).

Two numbers, always together:

* `certified` — proved here, from closed lemmas;
* `conjectural` — what the number becomes if every currently open problem
  closes with its stated target constant.

Only `certified` is the score.  A `sorry`ed lemma contributes its worst case
(for `C`: the value `2`, i.e. nothing), never its hoped-for constant, so the
metric is monotone in proof progress.

`PROPORTION.log` is generated from this file by `tools/proportion.go`; the
**binding constraint** field there names the single lemma that caps the
number, and is the pointer for where to work next.
-/
import Riemann.Program

namespace Riemann

open Filter

/-! ### Certified -/

/-- The certified proportion: what this development proves today about the
zeros of `ζ`.

It is `0.6725`, and it comes entirely from the external baseline
`baseline_zeta23` — i.e. from an **axiom**, not from anything this project
proves.  The program's own routes contribute nothing yet: no route has an
unconditional `(★)`.  That is the honest state of play, and the
anti-Goodhart rule says to display it rather than to hide it behind the
number. -/
theorem certified_std : zetaFamily.ProportionStd 0.6725 := baseline_zeta23

/-! > ⚠️ **SUPERSEDED (SESSION 084), and the correction belongs here.**  The
> reasoning below is sound but its enumeration of routes was not exhaustive: it
> assumed every bridge from `NscStd` to `Nsc` passes through `(★)`.  One does
> not.  `Gaps.proportion_of_proportionStd` is unconditional, and
> `certified_nsc_unconditional` below gives the row **`0.50875`**.  `Proportion 0`
> is kept as a true statement and as the record of what was believed. -/

/-- **The project's own row, formerly believed empty.**  `Proportion 0` is
trivially true.  The docstring that stood here claimed it was all that could be
certified, on the grounds that no unconditional `(★)` exists at any constant so
neither Proposition 1 (`2 - C`) nor the baseline route (`0.6725 - (C-1)/2`)
can be evaluated.  Both of those remain true; they were simply not the only
routes.  See `certified_nsc_unconditional`. -/
theorem certified_nsc : zetaFamily.toCounts.Proportion 0 := by
  intro ε hε
  filter_upwards [zetaFamily.toCounts.pos] with T hpos
  have h0 : 0 ≤ zetaFamily.toCounts.Nsc T := by
    show (0:ℝ) ≤ zetaFamily.Nsc T
    unfold Family.Nsc; positivity
  have : 0 ≤ zetaFamily.toCounts.Nsc T / zetaFamily.toCounts.Nz T :=
    div_nonneg h0 hpos.le
  linarith

/-- **The project's own row, and it is NOT empty: `0.50875`.**

`Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc` is `3·NscStd ≤ N + 2·Nsc`,
axiom-free and unconditional: a *haunted* atom — on-line part `1`, mass `≠ 1` —
has even nonzero off-line part, hence mass at least `3`, so it consumes three
zeros of `N` while contributing one to `NscStd`.  Transported by
`Gaps.proportion_of_proportionStd`, the baseline `ProportionStd 0.6725` becomes
`Proportion (3·0.6725 − 1)/2 = 0.50875` with **no star bound and no new axiom**.

The axiom tier is unchanged: this consumes exactly `baseline_zeta23` (and
`zetaNonempty`, via the family's nonemptiness), the same two the `NscStd` row
already consumed. -/
theorem certified_nsc_unconditional : zetaFamily.toCounts.Proportion 0.50875 := by
  have h := proportion_of_proportionStd certified_std
  have e : (3 * (0.6725 : ℝ) - 1) / 2 = 0.50875 := by norm_num
  rwa [e] at h

/-- What the project itself proves without any axiom about `ζ`: for *any*
zero family, `(★)` transfers to a proportion, and the off-line count is
capped.  These are the load-bearing, axiom-free results. -/
theorem certified_axiomFree (F : Family) (C : ℝ) (h : F.toCounts.StarBound C) :
    F.toCounts.Proportion (2 - C) ∧
      ∀ ε > 0, ∀ᶠ T in atTop, F.Noff T ≤ (C - 1 + ε) * F.Nz T :=
  ⟨Counts.proportion_of_starBound h, Family.offline_le F h⟩

/-! ### Conjectural

The targets, each as a hypothesis.  Nothing below is asserted. -/

/-- **Conjectural, Route I.**  If [OPEN 0] closes with `c₀ ≤ 0.33`, the
record falls: the proportion exceeds `0.6725`. -/
theorem conjectural_routeI (c₀ : ℝ) (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 0.33)
    (h : EffectiveFujii zetaFamily.toCounts c₀) :
    ∃ κ, 0.6725 < κ ∧ zetaFamily.toCounts.Proportion κ :=
  beats_record_of_le hc0 hc h

/-- **Conjectural, Route III / the second-moment floor.**  `2/3`.  Note the
BGST bridge is a *hypothesis*, not an axiom — ISSUES.md #8. -/
theorem conjectural_routeIII (hbg : BGSTNarrowBox zetaFamily)
    (h : ∀ b > 0, NarrowBox zetaFamily b) :
    ∀ ε > 0, zetaFamily.toCounts.Proportion (2/3 - ε) := by
  intro ε hε
  have hs := routeIII_with_narrowBox zetaFamily hbg h ε hε
  have := Counts.proportion_of_starBound hs
  intro ε' hε'
  filter_upwards [this ε' hε'] with T hT
  linarith [hT]

/-- **Conjectural, [OPEN D].**  `100%` — the Tentative Theorem. -/
theorem conjectural_full (h : ExtendedSupport zetaFamily) :
    ∀ ε > 0, zetaFamily.toCounts.Proportion (1 - ε) :=
  tentativeTheorem zetaFamily h

/-! ### The two-row ledger (ISSUES #13)

The literature's row (`NscStd`) and the project's row (`Nsc`) are linked by a
theorem, and the link costs `(C-1)/2`.  Ghosts are charged double because the
functional equation forces them into pairs (`three_le_H_of_haunted`). -/

/-- **The baseline route.**  A lower bound on the *standard* count transfers to
the project's stronger count at a cost of `(C-1)/2`.

Note what this buys: `Prop 1` alone gives `Nsc ≥ (2-C)N`, useful only for
`C < 2`.  This route gives `Nsc ≥ (κ - (C-1)/6)N`, which for the zeta-23
baseline `κ = 0.6725` is useful for **`C < 5.035`** — and beats Prop 1 for
every `C > 1.393`.  (The `/6` is the haunted-ordinate census, W6: a haunted
ordinate costs six in `N⊛ - N`, not two.)  The two rows are not redundant: past `C = 1.655` the
imported number is the better instrument. -/
theorem nsc_of_nscStd (F : Family) {C κ : ℝ} (hstar : F.toCounts.StarBound C)
    (hbase : F.ProportionStd κ) :
    ∀ ε > 0, ∀ᶠ T in atTop, (κ - (C - 1) / 6 - ε) * F.Nz T ≤ F.Nsc T := by
  intro ε hε
  filter_upwards [hbase (ε/2) (by linarith), F.nscStd_le_nsc_add hstar (ε/2) (by linarith),
    F.toCounts.pos] with T h1 h2 hpos
  have hz : (0:ℝ) < F.Nz T := hpos
  nlinarith [h1, h2, hz]

/-- **What opened the (formerly) empty row.**  ⚠️ SESSION 084: the row is open
at `0.50875` with no `(★)` at all.  A star bound now *improves* the row only for
`C < 1.49125` (Proposition 1) or `C < 1.9825` (the `/6` bridge).  The statement
below remains correct arithmetic about opening a row that is no longer closed.

Any unconditional `(★)` with `C < 2.345`
turns the zeta-23 baseline into a positive bound on the `H = 1` count. -/
theorem nsc_row_opens {C : ℝ} (hstar : zetaFamily.toCounts.StarBound C)
    (hC : C < 5.035) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (0.6725 - (C - 1) / 6 - ε) * zetaFamily.Nz T ≤ zetaFamily.Nsc T :=
  nsc_of_nscStd zetaFamily hstar baseline_zeta23

/-! ### The binding constraint

Today the binding constraint is `Assumptions.baseline_zeta23`: the number is
an axiom, not an import.  Wiring `zeta-23-lean` in as a real dependency
(toolchain `v4.33.0-rc2`) removes one axiom and leaves the number unchanged —
which is exactly the kind of "progress that does not move the score" the
metric is designed to make visible.

The first *mathematical* binding constraint after that is
`Fujii.c0_lower_bound`'s counterpart from above: an effective `c₀ ≤ 0.33`. -/

end Riemann
