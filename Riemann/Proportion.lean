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

/-- **`baseline_przz` is redundant.**  `ProportionStd` is monotone in its
constant (`Family.ProportionStd.mono`), and `0.4162 ≤ 0.6725`, so the
Pratt–Robles–Zaharescu–Zeindler baseline is a *theorem* given the zeta-23
baseline — not an independent assumption.

The two are recorded as separate axioms because they are separate results in the
literature, but the trusted base does not need both: `baseline_przz` can be
replaced by this proof wherever it is consumed (today: nowhere).

**Ruling for Joop**, not taken unilaterally: whether to delete the axiom and keep
this theorem, or keep the axiom as a record of an independent literature result.
Deleting shrinks the declared axiom surface from 9 to 8; keeping documents that
PRZZ is independently established, which matters if the zeta-23 baseline is ever
retracted. -/
theorem przz_of_zeta23 : zetaFamily.ProportionStd 0.4162 :=
  Family.ProportionStd.mono (by norm_num) baseline_zeta23

/-- **A third certified row: the off-line zeros.**  At most `32.75%` of the
zeros of `ζ` lie off the critical line, at the baseline's own axiom tier and
with no star bound — the standard-simple zeros are on the line and the off-line
ones are not, so `ProportionStd 0.6725` caps the off-line count directly.

This is the statement the program has been trying to buy from Route III's narrow
box and from `offline_le`'s star bound.  A weak form of it was available from the
baseline the whole time. -/
theorem certified_offline : OffLineImport zetaFamily 0.3275 := by
  have h := offLineImport_of_proportionStd certified_std
  have e : (1 : ℝ) - 0.6725 = 0.3275 := by norm_num
  rwa [e] at h

/-- **The `Nsc` row, by a second and independent route** — and it lands on the
same number.  `certified_nsc_unconditional` goes through the per-atom bound
`3·NscStd ≤ N + 2·Nsc`; this one goes through the off-line density row
`certified_offline` and the exchange rate `proportion_of_offLineImport`.

`0.6725 − 0.3275/2 = 0.50875`.  Two routes, no shared step past the baseline,
one answer — which is the `R17` witness for `084`. -/
theorem certified_nsc_via_offline : zetaFamily.toCounts.Proportion 0.50875 := by
  have h := proportion_of_offLineImport certified_std certified_offline
  have e : (0.6725 : ℝ) - 0.3275 / 2 = 0.50875 := by norm_num
  rwa [e] at h

/-- **`(★)` follows from "no zero has multiplicity ≥ 3".**

`starBound_of_multiplicity_and_proportion` at `M = 2` and the certified row
`κ = 0.50875` gives `C ≤ 1 + 2·(1 − 0.50875) = 1.9825 < 2`.

This is the first sufficient condition for `(★)` in the registers that does not
assume the conclusion: a multiplicity-`≤ 2` hypothesis is strictly weaker than
simplicity, and it is carried as a hypothesis here, never as an axiom.

**Candour about what it is worth.** Through `prop1` it yields
`Proportion (2 − 1.9825) = 0.0175`, which is **far worse** than the `0.50875`
already certified unconditionally.

⚠️ **Superseded at this location (SESSION 097).**  The constant `1.9825` is
loose: at `M = 2` the star constant is *exact*, `C = 2 − Nsc/N`, and
`Nsc = NscStd` so the standard baseline applies — giving `C ≤ 1.3275` and
`Proportion 0.6725`.  See `starBound_of_mult_le_two_zeta` and
`proportion_of_mult_le_two`.  The "far worse" verdict below was true of the loose
constant and is false of the sharp one. The value is not the proportion — it is that
`(★)` itself, which Routes I and III exist to obtain, drops out of a hypothesis
about multiplicities alone. `(★)` feeds `offline_le` and the narrow box, and
those are not reachable from the `Nsc` row directly. -/
theorem starBound_of_multiplicity_two
    (hM : ∀ T γ, (zetaFamily.D T).H γ ≤ 2) :
    zetaFamily.toCounts.StarBound 1.9825 := by
  have h := starBound_of_multiplicity_and_proportion hM certified_nsc_unconditional
  have e : (1 : ℝ) + ((2 : ℕ) : ℝ) * (1 - 0.50875) = 1.9825 := by norm_num
  rwa [e] at h

/-- **Multiplicity `≤ 2` gives `(★)` at `C ≤ 1.3275` — and the full `0.6725` row.**

`096` obtained `C ≤ 1.9825` from the same hypothesis by charging every crowded
atom `M·H`.  At `M = 2` no estimate is needed: `N⊛ + Nsc = 2N` exactly, and
`Nsc = NscStd`, so the *standard* baseline transfers whole.

`C ≤ 2 − 0.6725 = 1.3275`, which is **below Route III's `4/3` threshold**, and
`prop1` returns `Proportion (2 − 1.3275) = 0.6725` — the literature's row
delivered intact on the project's stronger notion. -/
theorem starBound_of_mult_le_two_zeta
    (hM : ∀ T γ, (zetaFamily.D T).H γ ≤ 2) :
    zetaFamily.toCounts.StarBound 1.3275 := by
  have h := starBound_of_mult_le_two hM certified_std
  have e : (2 : ℝ) - 0.6725 = 1.3275 := by norm_num
  rwa [e] at h

/-- …and therefore the whole baseline, on the project's own row. -/
theorem proportion_of_mult_le_two
    (hM : ∀ T γ, (zetaFamily.D T).H γ ≤ 2) :
    zetaFamily.toCounts.Proportion 0.6725 := by
  have h := Counts.proportion_of_starBound (starBound_of_mult_le_two_zeta hM)
  have e : (2 : ℝ) - 1.3275 = 0.6725 := by norm_num
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
