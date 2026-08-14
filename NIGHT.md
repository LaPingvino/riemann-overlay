# NIGHT — overnight run of 2026-08-14/15

Read top to bottom; shortest section first. Repo is live and private at
`github.com/LaPingvino/riemann-overlay`; every cycle commits and pushes, so the
morning diff is the night's work.

## Needs a ruling

Two items were escalated during the day and are **parked unresolved** rather
than decided overnight, per the escalation discipline. Neither blocks the queue.

* **ISSUES #28(a) — the build's trusted input.** `lakefile.toml` carries
  `rev = "main"` while `lake-manifest.json` pins `3635e74…` at
  `github.com/anthropics/zeta-23-lean`, and there is **no vendored copy**. If
  that repository moves, every axiom-free claim becomes uncheckable by a third
  party, and `rev = "main"` invites a `lake update` that silently retargets the
  pin. Cheap fix: pin the lakefile to the manifest rev. Durable fix: vendor or
  mirror. **Not touched overnight** — it is a trusted input, and the whole point
  of the repo going public is that its build is reproducible without us.
* **The W34a doctrine rule.** Proposed for `LOOP.md`: *a rung is not a blindness
  result; a rung is a blindness result **plus** a closure certificate for its
  class.* Rung 1 now has both. Doctrine edits are operator-ruled, so it waits.

## Parked

* **Whether the phase channel is necessary** — open, and family 2 does not
  decide it (SESSION 036). No family built from configurations at any number of
  heights forces phase, because the targets are ordinate-blind in the relevant
  sense. Parked with its price: deciding it needs a target that reads ordinates,
  which we do not have.
* **The GRH tier is empty** (0/11). Recruitment criterion, not a gap. The CGdL
  68.45 machinery run is the cheapest tier-3 census source and is queued, not
  overdue.

## Landed

### Night cycle 5 — rung 0 certified over the continuum; the regress stopped

`Riemann/Capacity.lean` gains a `Continuum` section (axiom-free, sorry-free).
**Kill condition** (an integral side-condition that is itself the disputed
content) **did not fire** — only `MeasurableSet A` and integrability are needed.
For any measurable `A`, `[0,1]` included: the guaranteed value is exactly the
pinned integral, and **two multipliers agreeing on `A` guarantee the same value
however they differ outside**. The class now matches the one `#10` names, which
was the ladder audit's objection to the `Finset` version.

**Stopped the regress on purpose.** The remaining piece — the modelling map from
a bandwidth-one certificate to this program — is *not a new debt*; it is the
project's existing boundary, the same species as the nine constants in
`Assumptions.lean`. Filing it as a rung item would mean nothing is ever
certified. **Rung 0 is ours, at the same standard as the rest of the certified
row.**

Snag (bin 1): `Mathlib.MeasureTheory.Integral.SetIntegral` does not exist at
this rev — the lemmas live in `...Integral.Bochner.Set`. Another instance of
#28(a)'s theme: pinned to a rev whose module layout we do not control.

### Night cycle 4 — the rung-0 debt, paid down to its skeleton

`Riemann/Capacity.lean`: 7 declarations, sorry-free, axiom-free, mentioning
neither `ζ` nor pair correlation. **Kill condition** (that the statement would
need the LP duality it is meant to establish) **did not fire** — and no duality
theorem is used at all. The register's "Lemma 1 + LP duality" was heavier than
the fact: the infimum is computed directly by exhibiting the adversary's move.

Extension past the known range is **worthless** when the multiplier is
nonnegative outside (`value_eq_pinned`, `no_gain_past_known`) and **fatal** when
it is not (`unbounded_below_of_neg_outside`). Never profitable.

**Then last cycle's criterion came back for me.** The class certified is a
`Finset` program; the class `#10` names is an integral over `[0,1]`. Different
classes, so rung 0 goes from *uncertified* to **partial**, not certified —
`SURPRISES` S20. The instrument was turned on the output of the cycle that built
it, one cycle later, and it bit.

Remaining step is measure-theoretic bookkeeping, now a well-posed Lean task.

### Night cycle 3 — the ladder audited; rung 0 is borrowed

W34d run with a **mechanical** criterion (a rung needs a machine-checked
"no member of class `C` decides the target"). **4 of 11 certified**: `#4`,
`#7`, `#8` at rung 1 (`μ_T`-invariant, built this week) and `#6` at rung 0
(bandwidth-one, `Zeta23.PairCeiling.ceiling_law256`, verified axiom-free
tonight — and **imported**, not ours).

Registered prediction **confirmed in direction**: all certified rungs are
`crystal`, none is `cascade`. No p-value — sample of 10 and half the
classification was judgement.

**Unpredicted, and the reason this cycle mattered:** `#10`'s rung 0 — the one
the ladder brief called *owned* — is **prose**, with no Lean statement behind
it. Filed as `SURPRISES` S19. Next rung-0 item is cheap and needs no arithmetic:
the LP collapse is a capacity claim about a convex program.

Snag (bin 2): `ceiling_law256` is cited across four registers as our ceiling and
is **not reachable from `import Riemann`**. Nothing false was published; a reader
following our root simply cannot get to it. Fix is cheap but changes the root's
import surface, so it waits.

### Off-cycle — `SURPRISES.md`, the calibration meter (Joop's ask)

Every case where the record went against a **stated** expectation, back-filled
from sessions 013–038: **18 entries**, tallied mechanically by
`forensics/surprises.py` so nobody can quote a number the table does not carry.

The breakdown, which is the part that means anything:

| corrected by | | class | |
|---|---|---|---|
| tooling | 6 | calibration | 11 |
| self | 6 | process | 4 |
| Fable | 3 | design | 3 |
| source | 2 | | |
| c.ai | 1 | | |

**67% of my confident errors were found by something that is not me.** Exactly
one is marked *self, late* — `S2`, the unsound `c`-table — and late is the only
expensive kind.

Anti-Goodhart clause is stated **above** the table, not in a footnote: a rising
count is neither virtue nor vice, and if the file is ever cited it must be cited
by breakdown.

Standing observation, and it is the argument for the whole apparatus: **not one
entry was found by re-reading my own prose.** Every correction came from an
instrument, another instance, a source, or from building the thing and watching
it fail.

### Night cycle 2 — the guard learns depth; three decades, one verdict

Guard generalised: hypothesis depth is a **partial order** (`RH` 1, `GRH` 2),
not a bit. **Kill condition** — that the T3(b) answer move off 3/11 — **did not
fire**: changers `[9,10,11]`, tiers **8 / 3 / 0**. R17 witness: `quarry.py`'s
local table and the guard's new `depth()` agreed exactly *before* the swap, and
that agreement is what licensed deleting the local one.

The field's progress axis is now a node family — `Mikawa_third`, `BBMZ_theta`,
`MRT_8_33`, all `log-power`. Against `GM_bridge` they give **three identical
QUALITY verdicts**. The guard now prints what quarry experiment A computes: the
axis the field advances on is not the axis the bridge bills.

Suite green: `lemma1_guard` self-test, `lake build` (3745), `proportion.go`,
base hash unmoved.

### Night cycle 1 — the audits catch up; W16 becomes a price

Two safe post-freeze items closed: the existence audit now covers 26 names from
`Blindness.lean`/`Fiber.lean` (and the axiom audit six), and ISSUES #28(b) is
fixed — `grep '^axiom' Riemann/Assumptions.lean` returns **9**, matching the
tool. R17 witness: the base hash did *not* move across the comment-only edit,
which is what proves the fingerprinter reads statements and not prose.

**W16 re-priced** (`forensics/w16_price.py`). In the coordinate `x = T^c` with
`δ = 1/log T`, the per-pair excess is `2x^{1/2}(cosh c − 1)` — a fixed fraction
of the chorus, **scale-free in `T`**. The unphased aggregate margin crosses 1 at
`c ≈ 1.39` for `T = 10^12`, `κ = 0.01`, so the affordable-but-unpaid window
`c ∈ (1, ≈1.39]` is **nonempty at heights where zeros are known**. Kill
condition (window empty at feasible heights) did not fire.

Conclusion: **the binding constraint is the phase, not the magnitude** — the
Landau route's whole remaining bill is one phase-removal. And the asymptotics
mislead in the opposite direction from `#27`: there the exponent was crueller
than the numerics, here it is kinder, and both times only the computed
crossover was honest.

Leaning on one **[RECALL, UNVERIFIED]** input: that "paid" means `c ≤ 1` via the
support-parameter dictionary. If it is `c ≤ 2` the window is empty. Cheapest
high-value verification on the board — flagged, not assumed.

---

# NIGHT — overnight run of 2026-08-13/14 (previous night, kept)

Read top to bottom; shortest section first.

## Needs a ruling

*(cleared — the zetaFamily swap was approved and applied; see SESSION 012)*

## Parked

* **W6's equidistribution half is circular** and stays parked: bounding
  ordinate-coincidences unconditionally needs to know the zeros are distinct,
  which is the thing being counted. The kill condition fired exactly as
  predicted. Its *census* half paid instead — see below.

## Landed

### Cycle 6 — W12: depth-shaped information is unspendable; re-mining pass

`N⊛` is depth-blind, so zero-free regions and classical density theorems have
price **exactly** zero in container currency — a stronger statement than
ISSUES #10. Exchange rate: any horizontal input must be uniform down to
`δ = 0`. Re-mining sessions 001–005 with X in hand yielded one directive worth
keeping: **when a bound is proved termwise over zeros, redo it grouped over
atoms before believing its constant** — which is what both constant
improvements tonight and yesterday actually were.

### Cycle 5 — the zeta family, constructed (see "Needs a ruling")

### Cycle 4 — W7 dead (the cheap-constraint genre is empty); `ofMult_N` landed

The ceiling's extremal configurations use multiplicities `m ≤ 3`; Jensen's free
bound permits `~27` at `γ = 10¹²`. Vacuous. Realizability splits into cheap
constraints (all satisfied with room to spare) and the Euler product (the
problem itself) — so no free classical invariant will tighten `C`. Autopsy in
`LEADS.md`.

Also landed: **`ofMult_N`** (`N = Σ m`), the to-do dropped on time-box in
session 005 — the `zetaFamily` socket now carries its counting lemma.

### Cycle 3 — W11: the ceiling is class capacity, not an input property

Window optimum against GUE input = Montgomery–Taylor exactly (`N=400`:
`0.6725026` vs `0.6725007`). On that same fixed input, certificates span
`0.5 → ≤0.6818287` — **18.18pp of pure instrument**. Remaining bandlimited
headroom: **0.28pp** (CGdL already took 0.65pp), correcting the "0.93pp"
quoted in an earlier dispatch. Details in `E.md` under E17.

### Cycle 2 — E9m: the audibility threshold, and why our ear is the right one

Single-zero audibility in `ψ(x) − x` is **δ-graded**: `log x ≳ log γ/δ`
unfiltered, `log x ≳ 1/δ` with a matched filter. At `δ ~ 1/log γ` that is
`x ~ γ^{log γ}` versus **`x ~ γ`** — so zero-verification (Turing/`Z(t)`) is
the optimal ear and reaches exactly as far as it has looked, while the
unfiltered prime side is deaf by a factor of `log γ` in the exponent. Details
and table in `E.md`. Kill condition did not fire; heuristic, not certified.

### Cycle 1 — the haunted ordinate costs **six**, not two

The row gap's price drops threefold. Proved, axiom-free, in `Riemann/Basic.lean`:

* `six_mul_card_le_Nstar_sub_N` — an ordinate of mass `m` contributes `m(m−1)`
  to `N⊛ − N`, and a haunted ordinate has `m ≥ 3`, so it pays `≥ 6`. Proved by
  grouping the sum over *distinct* ordinates
  (`Finset.sum_multiset_map_count`) rather than termwise over zeros — which is
  exactly what the old proof could not do.
* `NscStd_eq_Nsc_add_haunted` — the row gap **is** the haunted count.
* `hauntedSet_nodup` — haunted zeros have multiplicity one, so the set is
  duplicate-free and injects into its ordinates.
* `six_mul_NscStd_le : 6·NscStd + N ≤ 6·Nsc + N⊛`.

Propagated: `Family.nscStd_le_nsc_add` and `nsc_of_nscStd` now carry `(C−1)/6`.

**What it moves.**

| | before | after |
|---|---|---|
| transfer cost, direction (ii) | `(C−1)/2` | **`(C−1)/6`** |
| threshold for the `Nsc` row to open | `C < 2.345` | **`C < 5.035`** |
| where the baseline beats Prop 1 | `C > 1.655` | **`C > 1.393`** |
| [OPEN 0] target for the first `Nsc` number | `c₀ ≲ 1.17` | **`c₀ ≲ 4.5`** |

The last row is the point: the cheapest route to the empty row now asks for an
effective Fujii constant **four times weaker** than it did yesterday. Nothing
about `ζ` changed; the accounting got sharper.

Ledger unchanged (`NscStd 67.25% / Nsc 0.00%`) — this improves a *conjectural*
threshold, not a certified row, so no `PROPORTION.log` line moved.
