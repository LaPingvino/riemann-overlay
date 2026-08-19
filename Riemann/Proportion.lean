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

/-- **The PRZZ baseline, as a theorem.**  `ProportionStd` is monotone in its
constant (`Family.ProportionStd.mono`), and `0.4162 ≤ 0.6725`, so the
Pratt–Robles–Zaharescu–Zeindler record follows from the zeta-23 one.

**`SESSION 233`: the axiom it replaces is gone.**  `baseline_przz` was deleted
from `Assumptions.lean` on Joop's ruling; declared axioms `9 → 8`, base
`v2/cd7a22e688df → v3/c3b240548ad8`.  The paragraph this docstring used to carry
— a ruling request weighing deletion against keeping the axiom as a record of an
independent literature result — is answered and removed.

What the deletion does **not** do: PRZZ remains a real and independent result in
the literature, and this theorem does not re-prove it.  It says only that *given*
zeta-23's `0.6725`, this project need not additionally assume `0.4162`.  If the
zeta-23 baseline were ever retracted, this theorem would go with it and PRZZ
would have to come back as an axiom. -/
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
those are not reachable from the `Nsc` row directly.

**Dominated twice over, `SESSION 264`, and kept only as a record.**  This
declaration asks `H ≤ 2` and returns `1.9825`.

* `starBound_of_mult_le_two_zeta` asks the *same* hypothesis and returns
  `1.3275`, because it routes through `starBound_of_mult_le_two`'s exact
  constant rather than `starBound_of_multiplicity_and_proportion`'s, which
  `starBound_of_mult_le`'s docstring already records as loose by exactly `1 − κ`.
* `starBound_of_mult_le_three` asks the *weaker* `H ≤ 3` and returns the same
  `1.9825`.  The composite
  `starBound_of_mult_le_three (fun T γ => le_trans (hM T γ) (by norm_num))`
  typechecks against this signature, which is the whole proof that nothing is
  lost by never citing this row again.

`256` graded the shared conclusion `StarBound 1.9825` as two deliberate routes.
That grading was too generous: they are not two routes to one number, they are
one route and a strictly worse instance of it. -/
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

/-- **Multiplicity `≤ 3` already gives `(★)`, unconditionally otherwise.**

The sharp criterion is `C ≤ M − (M−1)·κ`, which is `< 2` exactly when
`κ > 1 − 1/(M−1)`.  The certified `κ = 0.50875` clears the threshold at `M = 3`
(`1 − 1/2 = 0.5 < 0.50875`), giving `C ≤ 3 − 2(0.50875) = 1.9825`.

So the sufficient hypothesis is **"no zero of `ζ` has multiplicity four or
more"** — weaker than `097`'s, though it returns a much worse constant.  The two
are complementary: `M ≤ 2` gives `C ≤ 1.3275` and the whole `0.6725` row;
`M ≤ 3` gives only `C ≤ 1.9825`, but asks for less.

Note the margin at `M = 3` is `0.00875` and comes entirely from `084`: with the
old `Nsc` row of `0` the threshold would fail at every `M ≥ 2`. -/
theorem starBound_of_mult_le_three
    (hM : ∀ T γ, (zetaFamily.D T).H γ ≤ 3) :
    zetaFamily.toCounts.StarBound 1.9825 := by
  have h := starBound_of_mult_le (by norm_num) hM certified_nsc_unconditional
  have e : ((3 : ℕ) : ℝ) - (((3 : ℕ) : ℝ) - 1) * 0.50875 = 1.9825 := by norm_num
  rwa [e] at h

/-! ### Is the multiplicity hypothesis a dial too?  No — it is a single point.

`SESSION 152`.  `151` found the *haunted* ladder improves with its parameter
(`m = 5 → 7 → ∞` buys `+8.188 → +10.917 → +16.375`).  The multiplicity ladder
looks like a second dial — `starBound_of_mult_le` is parameterised in `M`, and
this file states it at `M = 2` and `M = 3` — so the same question is owed.

**The answer is no, and it is the opposite shape.** Stating it generally makes it
one line of arithmetic: feeding `Proportion κ` through
`starBound_of_mult_le` and back through `proportion_of_starBound` returns

> `2 − (M − (M−1)·κ)  =  (M−1)·(κ − 1) + 1`

which for `κ < 1` is **strictly decreasing in `M`**, equals `κ` at `M = 2`, and
loses from there. So the multiplicity ladder has exactly one live rung, and the
`M = 3` statement below is valuable for its **star bound**, not for any
proportion it returns. -/

/-- **The multiplicity ladder at ζ, every rung at once.** -/
theorem proportion_of_mult_le_zeta {M : ℕ} (hM1 : 1 ≤ M)
    (hM : ∀ T γ, (zetaFamily.D T).H γ ≤ M) :
    zetaFamily.toCounts.Proportion
      (2 - ((M : ℝ) - ((M : ℝ) - 1) * 0.50875)) :=
  Counts.proportion_of_starBound
    (starBound_of_mult_le hM1 hM certified_nsc_unconditional)

/-- **The ladder's identity: the returned proportion is `(M−1)(κ−1) + 1`.** -/
theorem mult_ladder_value (M κ : ℝ) :
    2 - (M - (M - 1) * κ) = (M - 1) * (κ - 1) + 1 := by ring

/-- **And so it peaks at `M = 2` and strictly loses above it.**  With the
certified `κ = 0.50875`, every rung `M ≥ 3` returns *less* than the row it was
fed.  This is the exact opposite of `certified_nsc_ladder`, whose rungs climb —
and it is why nobody had stated the general form: there was nothing up there. -/
theorem mult_ladder_no_gain {M : ℕ} (hM : 3 ≤ M) :
    2 - ((M : ℝ) - ((M : ℝ) - 1) * 0.50875) < 0.50875 := by
  have h3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  nlinarith [h3]

/-- **The whole baseline, from a hypothesis about one pattern.**  If no ordinate
of `ζ` carries a lone critical zero shadowed by off-line pairs, the literature's
`0.6725` transfers to the project's stronger notion intact.

Strictly weaker than `097`'s multiplicity-`≤ 2` hypothesis, which additionally
forbids unhaunted crowding — and which buys the star bound `C ≤ 1.3275` that this
does not. -/
theorem proportion_of_noHaunted_zeta (hh : NoHaunted zetaFamily) :
    zetaFamily.toCounts.Proportion 0.6725 :=
  proportion_of_noHaunted hh certified_std

/-- **The baseline cap, at the level where `Proportion` is defined.**

`Fiber.row_essentially_optimal` gives a `ZeroData`; `Proportion` is a predicate
on *families*, so the witness only bites once placed in one.  `constFamily` does
that, and the result is a family satisfying `ProportionStd 0.6725` while failing
`Proportion 0.50944`.

**No theorem of the form "`ProportionStd 0.6725` ⟹ `Proportion κ`" holds with
`κ ≥ 0.50944`.**  The ledger certifies `0.50875`; the gap is `0.00069` and it is
the discretisation of the witness, not slack in the method. -/
theorem baseline_cap_witness :
    ∃ (F : Family), F.ProportionStd 0.6725
      ∧ ¬ F.toCounts.Proportion 0.50944 := by
  obtain ⟨D, hpos, hstd, hsc⟩ := Blindness.row_essentially_optimal
    (a := (0 : ℝ)) (by norm_num)
  exact ⟨constFamily D hpos, baseline_cap hpos hstd hsc⟩

/-- **The `Nsc` row by a third route: through the haunted density.**

`certified_offline` gives `β = 0.3275`; `hauntedDensity_of_offLineImport` halves
it to `δ = 0.16375`; `proportion_of_hauntedDensity` subtracts it from the
baseline.  `0.6725 − 0.16375 = 0.50875`.

Three derivations now agree exactly: the per-atom bound
(`certified_nsc_unconditional`), the off-line exchange rate
(`certified_nsc_via_offline`), and this one. -/
theorem certified_nsc_via_haunted : zetaFamily.toCounts.Proportion 0.50875 := by
  have h := proportion_of_hauntedDensity
    (hauntedDensity_of_offLineImport certified_offline) certified_std
  have e : (0.6725 : ℝ) - 0.3275 / 2 = 0.50875 := by norm_num
  rwa [e] at h

/-- **A certified statement about the haunted ordinates of `ζ`.**

The `084`–`128` arc identified `hauntedCount` as the quantity the `Nsc` row is a
subtraction of, and named it — an ordinate carrying one critical zero shadowed by
off-line pairs.  This is the first certified bound on it:

> **`hauntedCount ≤ (0.16375 + o(1))·N`** — at most `16.375%` as many haunted
> ordinates as zeros.

Same axiom tier as the rest (`baseline_zeta23`, `zetaNonempty`), and it is
`certified_offline` halved: a haunted ordinate carries at least two off-line
zeros, so the off-line density row caps the haunted density at half its value.

Not added to `tools/metric.json`, for the same reason as `certified_offline`:
the ledger maximises over rows, and an *upper* bound on a defect is not
commensurate with a *lower* bound on simple zeros. -/
theorem certified_haunted : HauntedDensity zetaFamily 0.16375 := by
  have h := hauntedDensity_of_offLineImport certified_offline
  have e : (0.3275 : ℝ) / 2 = 0.16375 := by norm_num
  rwa [e] at h

/-- **Two more certified statements about `ζ`, from the same baseline.**

Both were general theorems with no `ζ` instance — `129`'s gap exactly: a quantity
used as a step and never stated as a result.

* **at least `67.25%` as many odd-mass ordinates as zeros**, since every
  standard-simple ordinate has odd mass;
* hence **at least `67.25%` as many distinct ordinates as zeros**, so the **mean
  vertical multiplicity is at most `1/0.6725 ≈ 1.487`**.

⚠️ **Corrected `SESSION 131`:** `130` presented these as two findings. They are
not independent — `Fiber.oddAtoms_le_atomCount` says the odd ordinates are a
subset of the ordinates, so the **first implies the second**. The odd-mass
statement is the result; the multiplicity bound is its corollary, and the
mean-multiplicity reading understates what is proved: at least `67.25%` of the
ordinate-count is *odd*, not merely distinct.

Same axiom tier as every other row. -/
theorem certified_atomCount :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (0.6725 - ε) * zetaFamily.Nz T ≤ zetaFamily.atomCount T :=
  atomCount_ge_of_proportionStd certified_std

theorem certified_oddAtoms :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (0.6725 - ε) * zetaFamily.Nz T ≤ zetaFamily.oddAtoms T :=
  oddAtoms_ge_of_proportionStd certified_std

/-- **The project already holds an unconditional distinct-zeros proportion, and
it reproduces the haunted bound exactly.**

`certified_atomCount` is `N_d(T) ≥ (0.6725 − o(1))·N(T)` — a **distinct-zeros
proportion at the baseline tier**, which is the quantity the haunting literature
would have to supply. Converting it at the deficit's rate one-half gives
`δ = (1 − 0.6725)/2 = 0.16375`: the same bound as `certified_haunted`, by a route
through a quantity the literature names.

So the distinct-zeros shelf and the off-line shelf pay the *same* price here, and
`111` caps both. -/
theorem certified_haunted_via_distinctZeros : HauntedDensity zetaFamily 0.16375 := by
  have h := hauntedDensity_of_distinctZeros
    (F := zetaFamily) (c := 0.6725) certified_atomCount
  have e : ((1 : ℝ) - 0.6725) / 2 = 0.16375 := by norm_num
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

/-- **The `m = 5` ladder rung at the ζ level: `0.590625`, `+8.2` points.**

`PRICES.md` has carried this route at `8.2 points` since `105`, and — exactly as
with Route II before `147` — it existed only as arithmetic.  `SESSION 150` states
it.

`(5·0.6725 − 1)/4 = 0.590625`.

**The hypothesis is combinatorial, not analytic.**  `NoSmallHaunted zetaFamily 5`
says no standard-simple ordinate is crowded to mass exactly `3` — off-line pairs
are permitted anywhere *except* shadowing a lone critical zero at the cheapest
haunted mass.  It is not RH-conditional, so `provenance_lint`'s Rule 4 does not
touch it, and unlike `NoHaunted` it is not vacuous under any hypothesis the
project holds. -/
theorem certified_nsc_via_noSmallHaunted
    (hh : NoSmallHaunted zetaFamily 5) :
    zetaFamily.toCounts.Proportion 0.590625 := by
  have h := proportion_of_noSmallHaunted (m := 5) (by norm_num) hh certified_std
  have e : (((5 : ℕ) : ℝ) * 0.6725 - 1) / (((5 : ℕ) : ℝ) - 1) = 0.590625 := by
    norm_num
  rwa [e] at h

/-- **The whole ladder at the ζ level, every rung at once.**

`SESSION 151`.  `150` stated the `m = 5` rung because `PRICES.md` called it "the
cheap one"; the register's own table also lists `m = 7`, and nothing had been
said about it.  One line gives every rung, and the corollaries below read values
off it. -/
theorem certified_nsc_ladder {m : ℕ} (hm : 2 ≤ m)
    (hh : NoSmallHaunted zetaFamily m) :
    zetaFamily.toCounts.Proportion (((m : ℝ) * 0.6725 - 1) / ((m : ℝ) - 1)) :=
  proportion_of_noSmallHaunted hm hh certified_std

/-- The exact `m = 7` rung value.  `SESSION 299`: this and the shortfall below
were prose from `153` until now, and the prose had the shortfall wrong by a
factor of ten.  Rungs `3` and `5` were never at risk — their arithmetic is
already inline in `certified_nsc_unconditional` and
`certified_nsc_via_noSmallHaunted`, which is why only `7` slipped. -/
theorem ladder_seven_exact_value :
    ((7 : ℝ) * 0.6725 - 1) / ((7 : ℝ) - 1) = 7415 / 12000 := by norm_num

/-- Recorded numeral plus shortfall is the exact value: the additive form of the
docstring's claim, re-checked by `norm_num` on every build. -/
theorem ladder_seven_shortfall :
    (0.6179166 : ℝ) + 1 / 15000000 = 7415 / 12000 := by norm_num

/-! #### Where the ladder crosses the rest of the board — `SESSION 341`

`Gaps.ladder_beats_iff` gives the threshold for any target `c < κ` as
`m > (1 − c)/(κ − c)`.  With `κ = 0.6725` the two competing rows on the board have
thresholds that fall between rungs, so the first rung to overtake each is the next
*odd* one — odd because `Gaps.noSmallHaunted_even_iff` makes an even rung the same
hypothesis as its successor, so the ladder's genuine steps are the odd `m`.

Each crossing ships as a pair: the rung that beats the target and the previous odd
rung that does not.

**Kill condition, filed first:** *if either threshold lands below rung `3` — the
rung `Gaps.noSmallHaunted_three` proves for free — then the row it belongs to was
never a competitor and the crossing is not news.*  It did not fire: the thresholds
are `400/7 ≈ 57.14` and `39831/7081 ≈ 5.63`. -/

/-- **Route II's threshold: `39831/7081`, between `5` and `6`.**  The decimal
`5.625` is *not* this number — `0.07081 × 5.625 = 0.39830625` against `0.39831` —
and writing it as a decimal is how the first draft of this section got it wrong. -/
theorem ladder_routeII_crossing_exact :
    ((1 : ℝ) - 0.60169) / ((0.6725 : ℝ) - 0.60169) = 39831 / 7081
      ∧ (5 : ℝ) < 39831 / 7081 ∧ (39831 : ℝ) / 7081 < 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Rung `7` is the first to beat Route II, and rung `5` does not.**  This is the
witness for the domination `340` measured: `0.6179166…` against `0.60169`, and
since `337` at no axiom cost against Route II's two. -/
theorem ladder_beats_routeII_first_at_seven :
    (0.60169 : ℝ) < ((7 : ℝ) * 0.6725 - 1) / ((7 : ℝ) - 1)
      ∧ ¬ ((0.60169 : ℝ) < ((5 : ℝ) * 0.6725 - 1) / ((5 : ℝ) - 1)) := by
  norm_num

/-- **Route III's threshold: exactly `400/7`.**  `κ − 2/3 = 7/1200` and
`1 − 2/3 = 1/3`. -/
theorem ladder_routeIII_crossing_exact :
    ((1 : ℝ) - 2 / 3) / ((0.6725 : ℝ) - 2 / 3) = 400 / 7 := by norm_num

/-- **Rung `59` is the first to beat Route III's `2/3 − ε` target, and rung `57`
does not.**  `0.666853…` against `0.666652…`, either side of `2/3`.  Both rows cost
no axioms since `337`, so at rung `59` the ladder dominates the narrow box in the
only currency left — the hypothesis itself. -/
theorem ladder_beats_routeIII_first_at_fiftynine :
    (2 / 3 : ℝ) < ((59 : ℝ) * 0.6725 - 1) / ((59 : ℝ) - 1)
      ∧ ¬ ((2 / 3 : ℝ) < ((57 : ℝ) * 0.6725 - 1) / ((57 : ℝ) - 1)) := by
  norm_num

/-! **Route I and `[OPEN D]` need no new theorem here.**  `Gaps.ladder_lt_kappa`
(`240`) puts every rung strictly below `κ` and
`Gaps.currencies_saturate_at_kappa` (`240`) already says a row promising more than
`κ` is buying a third thing.  `341` wrote an instance of the first at
`κ = 0.6725` before finding it and deleted it; the ceiling is `certified_std`'s
constant, so it moves only if that constant does. -/

/-- **The `m = 7` rung: `0.617917`, `+10.917` points — and it dominates the ξ′
route in both currencies.**

`(7·0.6725 − 1)/6 = 0.6179166…`.

*Precision, stated (`SESSION 153`; figure corrected `SESSION 299`):* the exact
ladder value is `7415/12000`, a repeating decimal, and the constant asserted here
is the terminating `0.6179166` — **`1/15000000` below it**.  `153` wrote
`1/1500000`, ten times too large; the slip was in the conservative direction, so
"very slightly weaker" understated how slight.  Both figures are now theorems
(`ladder_seven_exact_value`, `ladder_seven_shortfall`) rather than prose.
The theorem is therefore very slightly weaker than
`certified_nsc_ladder` at `m = 7`, deliberately, so the statement carries a
readable numeral.  Anything needing the exact value should use the ladder
directly.  The `+10.917` quoted in `PRICES.md` is the same to three decimals
either way.

Against `certified_nsc_via_xiPrime`'s
`0.60169` at **four** axioms, this is *more* proportion at **two**. **`340`:
measured with `board.py --cones`, those counts are `2` and `0` — the discharge at
`337` removed `baseline_zeta23` and `zetaNonempty` from both cones, so the trade is
now more proportion at *no* axioms against less at two.
`ladder_beats_routeII_first_at_seven` is the arithmetic half of it, with rung `5`
as the converse witness.  `150`
compared ξ′ against the `m = 5` rung and read the trade-off as "1.106 points for
two axioms"; at `m = 7` there is no trade-off left in either currency, and the
only axis on which ξ′ can still win is **hypothesis strength** — which is a real
axis, and the one a ruling should turn on. -/
theorem certified_nsc_via_noSmallHaunted_seven
    (hh : NoSmallHaunted zetaFamily 7) :
    zetaFamily.toCounts.Proportion 0.6179166 := by
  have h := certified_nsc_ladder (m := 7) (by norm_num) hh
  intro ε hε
  filter_upwards [h ε hε] with T hT
  have e : (((7 : ℕ) : ℝ) * 0.6725 - 1) / (((7 : ℕ) : ℝ) - 1) = 3.7075 / 6 := by
    norm_num
  rw [e] at hT
  have hnum : (0.6179166 : ℝ) ≤ 3.7075 / 6 := by norm_num
  linarith

/-! ### Route II at the ζ level, conditional and axiom-free in its own step

`Gaps.offLineImport_of_derivative` is general; `Assumptions.zeta23_xiPrime`
supplies `κ' = 0.85838` for `ξ'`.  Until now the two were never composed at the
ζ level, so the `+9.29`-point route existed as a **docstring arithmetic** and
not as a theorem.  `SESSION 147` closes that gap.

**The two hypotheses stay hypotheses.**  `OffTransfer` needs Riemann–von
Mangoldt (`log T = o(N(T))`), which is not in the registers; `NzComparable`
needs a relation between `xiPrimeFamily` and `zetaFamily`, and `xiPrimeFamily`
is an *opaque* axiom with no stated connection to `zetaFamily`.  Both are
Conrey 1983, unread.  Discharging either by axiom would raise the certified
proportion **by assumption**, which is what `Assumptions.lean` exists to forbid.

So the ledger does **not** move: `tools/metric.json` points no row here.  What
changes is that the mathematics is now done, and the parked ruling is reduced to
a pure doctrine question — *may these two be assumed?* — with no derivation left
inside it. -/

/-- **Route II's mathematics is axiom-free; the axioms only say `ξ′` is such a
family.**  `SESSION 388`.

`offLineImport_of_derivative` is general in both families, so nothing in the
exchange needs `xiPrimeFamily` to exist or `zeta23_xiPrime` to hold — those two
axioms enter only when the general family is *instantiated* at `ξ′`.

Measured with `#print axioms`: this theorem's cone is `[propext,
Classical.choice, Quot.sound]`, while `certified_nsc_via_xiPrime`'s adds
`xiPrimeFamily` and `zeta23_xiPrime`.  So the board's *"Route II costs two
axioms"* prices the **identification** of `ξ′`, not the argument.

**`389`: this is Route I's convention, not a new one.** `Program.lean`'s
`routeI_closePairs` is general and axiom-free, `routeI_closePairs_zeta` is its
one-line instantiation carrying `closePairsZeta` and
`fujii_closePair_bookkeeping`, and `conjectural_routeI` is axiom-free. `388`
brought Route II up to that standard rather than discovering it. -/
theorem offline_via_derivative_family {F' : Family}
    (hp : F'.toCounts.Proportion 0.85838)
    (htr : OffTransfer zetaFamily F') (hcmp : NzComparable zetaFamily F') :
    OffLineImport zetaFamily 0.14162 := by
  have h := offLineImport_of_derivative (κ' := (0.85838 : ℝ))
    (by norm_num) (by norm_num) hp htr hcmp
  have e : (1 : ℝ) - 0.85838 = 0.14162 := by norm_num
  rwa [e] at h

/-- `388`/`389`: Route II's row with the family general.  Cone measured empty. -/
theorem certified_nsc_via_derivative_family {F' : Family}
    (hp : F'.toCounts.Proportion 0.85838)
    (htr : OffTransfer zetaFamily F') (hcmp : NzComparable zetaFamily F') :
    zetaFamily.toCounts.Proportion 0.60169 := by
  have h := proportion_of_offLineImport certified_std
    (offline_via_derivative_family hp htr hcmp)
  have e : (0.6725 : ℝ) - 0.14162 / 2 = 0.60169 := by norm_num
  rwa [e] at h

/-- **Route II on the inputs the source actually proves, with `ISSUES #7`'s gap
as a visible hypothesis.**  `SESSION 391`.

`certified_nsc_via_derivative_family` takes `Proportion 0.85838` — the count
`#7` objects to, since `arXiv:2608.13637` Remark 7.1 proves the statement for
`N0simple`, our `NscStd`.  This version takes what the source proves and carries
the difference explicitly: `NoHaunted F'`, which is the content `283` named.

**`#7` is not closed by this.** The gap is still open and still unsupplied; what
changes is that it is now a hypothesis a reader can see rather than a reading
baked into the statement.  Nothing here asserts `NoHaunted` for `ξ′`. -/
theorem certified_nsc_via_derivative_std {F' : Family}
    (hstd : F'.ProportionStd 0.85838) (hnh : NoHaunted F')
    (htr : OffTransfer zetaFamily F') (hcmp : NzComparable zetaFamily F') :
    zetaFamily.toCounts.Proportion 0.60169 :=
  certified_nsc_via_derivative_family (proportion_of_noHaunted hnh hstd) htr hcmp

/-- **The `ξ'` off-line import, conditional on the two transfer hypotheses.**
`1 − 0.85838 = 0.14162`. -/
theorem offline_via_xiPrime
    (htr : OffTransfer zetaFamily xiPrimeFamily)
    (hcmp : NzComparable zetaFamily xiPrimeFamily) :
    OffLineImport zetaFamily 0.14162 :=
  -- `389`: the instantiation at `ξ′`, completing what `388` began.  The axioms
  -- enter here and nowhere in `offline_via_derivative_family`.
  offline_via_derivative_family zeta23_xiPrime htr hcmp

/-- **Route II priced, as a theorem rather than a docstring: `0.60169`.**

`0.6725 − 0.14162/2 = 0.60169`, i.e. **`+9.294` points** on the `Nsc` row over
the unconditional `0.50875` — the largest single movement available on the
board.

**What it costs, stated exactly** (`#print axioms`, `SESSION 147`): the two
hypotheses in the signature **and two more axioms than the certified row**.  The
cone here is `baseline_zeta23, xiPrimeFamily, zeta23_xiPrime, zetaNonempty`;
`certified_nsc_unconditional`'s is `baseline_zeta23, zetaNonempty`.  So the route
is deeper in the trusted base as well as conditional, and a ruling to adopt it
would raise the ledger's axiom count from 2 to 4 — not merely discharge two
`Prop`s.  That is a materially bigger ask than the registers had recorded.

Compare `certified_nsc_via_offline`, which is the same exchange rate
(`proportion_of_offLineImport`) fed the *unconditional* import `0.3275` and
lands on `0.50875`.  The entire gain is the difference between importing
off-line mass from the baseline itself and importing it from `ξ'`. -/
theorem certified_nsc_via_xiPrime
    (htr : OffTransfer zetaFamily xiPrimeFamily)
    (hcmp : NzComparable zetaFamily xiPrimeFamily) :
    zetaFamily.toCounts.Proportion 0.60169 :=
  -- `388`: the instantiation of `certified_nsc_via_derivative_family` at `ξ′`.
  -- The two axioms enter *here*, and nowhere in the argument above.
  certified_nsc_via_derivative_family zeta23_xiPrime htr hcmp

/-! ### The binding constraint

**`337`: this is no longer true and the paragraph below is kept as the record.**
`baseline_zeta23` is a theorem; the dependency is wired in.  The number did not
move, which is exactly what the paragraph predicted.

*Until `337`:* the binding constraint was `Assumptions.baseline_zeta23` — the
number was an axiom, not an import.  Wiring `zeta-23-lean` in as a real
dependency (toolchain `v4.33.0-rc2`) removes one axiom and leaves the number
unchanged — which is exactly the kind of "progress that does not move the score"
the metric is designed to make visible.

The first *mathematical* binding constraint after that is
`Fujii.c0_lower_bound`'s counterpart from above: an effective `c₀ ≤ 0.33`. -/

/-! **`baseline_zeta23` reduces to zeta-23's cumulative `ThmD` row, and nothing
else.**  `SESSION 280`.

> **`337`: the reduction was taken, and both theorems moved.** `baseline_zeta23`
> is a theorem in `Riemann/Assumptions.lean` and so is the bridge below —
> `baseline_of_cumulative` — because every consumer of the name (`certified_std`
> at the top of this file among them) sits earlier than this line. What remains
> here is the record of the pricing.

The `zetaNonempty` treatment (`270`–`272`), applied to the binding axiom. Given
the cumulative statement zeta-23 proves — `(c − ε)·Ncount 0 T ≤ N0simple 0 T`
eventually — and any `c ≥ 0.6725`, this axiom follows.

Both count bridges are already on disk and cost no build: `270`'s
`zetaZeroData_N` identifies our `N` with their `Ncount 0 T`, and `274`'s
`zetaZeroData_NscStd` identifies our `NscStd` with their `N0simple 0 T`.

**What the import would buy is one theorem.**
`Zeta23.ThmD.Mult.thmD₀_simple_mult_cumulative` has exactly the hypothesis
shape above with `c = HD 1`, and `279`'s `baseline_decimal_le_exact` supplies
`0.6725 ≤ HD 1` once `HD 1` is unfolded to `3/2 − cot(1/√2)/√2`. The price is
`ThmD.Final`'s `44,441` lines (`268`), and that is now the whole of it.

**Not axiom-free, and the reason is structural** — *superseded at `337`, and
the sentence below was right about the order.*  `#print axioms` used to report
`zetaNonempty` here, because the *statement* names `zetaFamily`, which was built
from that axiom.  Every theorem about `zetaFamily` carried it; discharging
`zetaNonempty` clears this one too, which is one more reason the two bridges
were worth taking in that order — and at `337` both were taken in it. -/

/-- **`ISSUES` `#7`'s split, made explicit.**  `SESSION 283`.

`#7` has stood since `SESSION 003` as *"bin 1, fixed in the docstring; still an
over-strong axiom"*: `zeta23_xiPrime` asserts `Proportion 0.85838`, which is a
statement about `N_sc` (`H = 1`), while `Zeta23.XiPrime.xiDeriv_simple_on_line`
proves `0.85838` for `N0simple` — on-line zeros of multiplicity one, the
`NscStd` quantity.  `#7` records that the conversion between them *"is not a
theorem"* for `ξ′` and *"should be split into (i) the cited zeta-23 statement
and (ii) the conversion lemma"*.

This is that split, and the conversion lemma already existed —
`proportion_of_noHaunted`.  So the exact content the axiom absorbs is
`NoHaunted xiPrimeFamily`, and `Blindness.Nsc_eq_NscStd_iff_noHaunted` says
that is not a technicality but the difference between the two counts.

**This does not weaken the axiom**; `Assumptions.lean` still asserts the strong
form and the trusted base is unchanged.  What it does is name the gap in a
machine-checked way, so that replacing the axiom by its honest half is a
one-line edit whenever that is ruled on. -/
theorem xiPrime_proportion_of_std_and_noHaunted
    (hstd : xiPrimeFamily.ProportionStd 0.85838)
    (hh : NoHaunted xiPrimeFamily) :
    xiPrimeFamily.toCounts.Proportion 0.85838 :=
  proportion_of_noHaunted hh hstd



/-! ### The distinct-zeros route, priced and closed — `SESSION 338` -/

/-- **`GD lam = (1 + HD lam)/2`**, straight from the vendored definitions
`Zeta23.ThmD.GD` and `Zeta23.ThmD.HD`.  Reachable only since `337`.  This is why
the distinct-zeros constant and the `NscStd` constant are not independent
numbers: `0.83625 = (1 + 0.6725)/2`. -/
theorem zeta23_GD_eq_of_HD (lam : ℝ) :
    Zeta23.ThmD.GD lam = (1 + Zeta23.ThmD.HD lam) / 2 := by
  simp only [Zeta23.ThmD.GD, Zeta23.ThmD.HD]
  ring

/-- **The route through the point count is dominated.**  Feeding zeta-23's
`0.83625` distinct-zeros constant through the only dictionary on disk, together
with `certified_offline`'s `0.3275`, yields `0.50875` for `atomCount` — below the
`0.6725` that `certified_atomCount` already has.

**The hypotheses are hypotheses, deliberately.**  No bridge from our
`distinctZeros` to `Zeta23.Ndist` is proved anywhere, and this theorem does not
assume one: it takes a point-count proportion as an input and prices it. -/
theorem distinctZeros_route_dominated (D : ZeroData)
    (hd : (0.83625 : ℝ) * (D.N : ℝ) ≤ (Blindness.distinctZeros D : ℝ))
    (hoff : (D.Noff : ℝ) ≤ 0.3275 * (D.N : ℝ)) :
    (0.50875 : ℝ) * (D.N : ℝ) ≤ (Blindness.atomCount D : ℝ) := by
  have h := Blindness.atomCount_of_distinctZeros_and_Noff D hd hoff
  have e : (0.83625 : ℝ) - 0.3275 = 0.50875 := by norm_num
  rwa [e] at h

/-- **…and it is dominated for every constant, not just that one.**  Even a
point-count proportion of `1` — every zero distinct, the strongest such statement
there is — converts to exactly `0.6725`, tying `certified_atomCount` rather than
beating it.  So the missing bridge is not worth building for this purpose at any
input constant. -/
theorem distinctZeros_route_ties_at_one (D : ZeroData)
    (hd : (1 : ℝ) * (D.N : ℝ) ≤ (Blindness.distinctZeros D : ℝ))
    (hoff : (D.Noff : ℝ) ≤ 0.3275 * (D.N : ℝ)) :
    (0.6725 : ℝ) * (D.N : ℝ) ≤ (Blindness.atomCount D : ℝ) := by
  have h := Blindness.atomCount_of_distinctZeros_and_Noff D hd hoff
  have e : (1 : ℝ) - 0.3275 = 0.6725 := by norm_num
  rwa [e] at h



end Riemann
