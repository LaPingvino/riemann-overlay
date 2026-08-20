# RULING — the one decision the ledger waits on

**For Joop. Verified `SESSION 186`, re-verified `SESSION 213`; every number
below is reproduced in exact rationals and every cone by `#print axioms`.**

> **Still current as of `213`.** `forensics/board.py` re-run this cycle: every
> route declaration unchanged, `30/30` cones as recorded, `9` axioms declared,
> ledger `NscStd 67.25% / Nsc 50.88%`. **No row below moved in `193`–`212`.**
> Two things changed *around* the board, and both belong in a decision you are
> being asked to make:
>
> **1. Moments are not a currency.** `ISSUES` `#20` had said a third moment was
> the input that could improve the reduction, which left a standing hope that
> some higher-moment supplier might appear. `211` closes that at **every** order
> `k ≥ 2` (`Optimal.linearBoundK_LP_value`, value `2 − C`), and `212` closes it
> at any admissible `C_k`, not merely the extreme
> (`linearBoundK_no_gain_at_any_moment`). `W35` is dead and its named next step
> — mapping the realizable `(C, C₃)` region — is not work worth doing. So the
> three currencies below are the three, with no fourth waiting.
>
> **2. Rung 0 is not on this board, and it got worse.** The ladder brief's
> rung 0 (`#10`'s LP-duality collapse) was believed one instantiation short of
> certified. `198` and `199` show the capacity theorems bound a bandwidth-one
> program **from below** rather than computing it — a bandwidth class is a
> *subclass*, an infimum over a smaller class can be larger, and `#10`'s no-gain
> conclusion does not transfer to a subclass. The debt is now blocked on a named
> analytic input the repo does not have (Fourier support, a pair-correlation
> form factor). This changes no row here; it is flagged so the ladder's picture
> and this board's are not read as one thing.

This file exists because the decision has been parked since `147` and its
materials are spread across `PRICES.md`, `CLAIMS.md` and twenty session entries.
Nothing here is new. It is one page instead of twenty.

---

## The state

> ### ⚠️ `340`: the axiom column of this whole page is out of date, in one direction
>
> `337` discharged `baseline_zeta23` and `zetaNonempty` on your standing ruling —
> both are theorems now, proved through the vendored `zeta-23` tree. `340` re-ran
> `forensics/board.py --cones`, which asks the kernel rather than the register:
> **ten of thirty-two recorded cones moved, every one of them downward.**
>
> | | recorded before `337` | measured at `340` |
> |---|---|---|
> | `certified_nsc_unconditional` | 2 | **0** |
> | `certified_nsc_via_noSmallHaunted` (`0.590625`) | 2 | **0** |
> | `certified_nsc_via_noSmallHaunted_seven` (`0.6179166`) | 2 | **0** |
> | `starBound_of_multiplicity_two`, `starBound_of_mult_le_two_zeta` | 2 | **0** |
> | `conjectural_routeIII`, `conjectural_routeI`, `conjectural_full` | 1 | **0** |
> | `certified_nsc_via_xiPrime` (Route II) | 4 | **2** |
> | `offline_via_xiPrime` | 3 | **2** |
>
> **Every row on the board is axiom-free except Route II.** The `axioms` column
> in the table below reads `2`, `1`, `1`, `1`; the measured values are `0`, `0`,
> `0`, `0`. `CONE_EXPECTED` in `board.py` now records the measured sets and
> `32/32` pass.
>
> **What this does and does not change.** The board's *ordering* is unchanged —
> Route II was already dominated (`0.60169` against the ladder's `0.6179166` at
> strictly more axioms), and it still is. What changed is the stakes: the project
> now holds a **fully unconditional** `50.88%`, and adopting any row trades that
> property away rather than adding to a base that already assumed two things.
> Going `0 → 1` is a different act from going `2 → 3`. That is the decision you
> have, restated in the currency it is now in.
>
> The rest of this page is left as written, per the rule that corrections go at
> the location of the stale text rather than by rewriting the record.

| | |
|---|---|
| certified `NscStd` | **67.25%** (`baseline_zeta23` — **`337`: a theorem, not an axiom**) |
| certified `Nsc` | **50.88%** (`certified_nsc_unconditional`) |
| axioms in the certified cone | **2** — **`337`: `0`** |
| axioms declared | **8** (`SESSION 233`: `baseline_przz` deleted on ruling 3) — **`337`: `6`** |
| sorries | 0 |
| build | green, 3757 jobs — **`337`: 8862, the vendored tree is in it** |

**The `Nsc` row cannot move from what the project already holds.** `111`/`112`
prove it is within `0.00069` of the best obtainable from the baseline alone;
`169` and `175` prove both exchange constants optimal and attained; `178`–`180`
prove every route bound tight at every size. There is no derivation left to
sharpen. **Every remaining gain requires assuming something.**

## The board

Gains are on the `Nsc` row over the certified `0.50875`.

**One conditional row is displayed, per Joop's ruling 2 of the slate of `228`.**

| route | `Nsc` | gain | axioms | hypothesis |
|---|---|---|---|---|
| **`NoHaunted`** | `0.672500` | `+16.375` | 2 → **0** (`340`) | no haunted ordinate at all |
| **Route III** | `2/3 − ε` | `+15.792` | **1** → **0** (`340`) | narrow box (BGST) |
| **Route I** | `> 0.6725` | `> +16.375` | **1** → **0** (`340`) | effective Fujii `c₀ ≤ 0.33` |
| **[OPEN D]** | `1 − ε` | `+49.125` | **1** → **0** (`340`) | extended support |

> **`362`: a row from outside, priced and placed.** `arXiv:2608.13637` §7.3 gives
> `liminf N₀ˢ/N ≥ 13/18 = 0.7222…` under `HL*(k₀)`, Hardy–Littlewood on prime pairs.
> `Riemann.HL_row_on_the_board` puts it above Route III's `2/3` and above the certified
> `0.6725`, below `[OPEN D]`; `ladder_cannot_reach_HL_row` and
> `offLine_currency_cannot_reach_HL_row` show **neither currency this project owns
> reaches it**, at any `m` or `β`. **It is not on the board and should not be:** `HL*` is
> an open conjecture, and `R5` forbids assuming one. What it changes is the shape of the
> third currency — *statistics* now has a number attached, and the number is an
> improvement on ours.

**`340`: the `axioms` column above is superseded by the measurement at the top of
this page.** Every entry in it is `0`. The hypothesis column is unchanged and is
now the whole cost of every row.

### The same board, priced in off-line control (`SESSION 239`)

`proportion_of_offLineImport` pays `κ − β/2`, so any target `T` reachable
*through off-line control* costs `β = 2(κ − T)` and nothing about `T` matters
beyond that (`Gaps.offLineImport_inverse`). Since `β ≥ 0` is a proportion bound,
the currency's entire range is `[0.50875, 0.6725]` (`Gaps.offLineImport_range`).

| target | `β` it would cost | against the free `β = 0.3275` |
|---|---|---|
| `0.50875` — the certified row | `0.3275` | free |
| `0.60169` — `ξ'` | `0.14162` | `2.3×` better |
| `2/3` — Route III's payout | `7/600 ≈ 0.01167` | `28×` better |
| `0.6725` — `NoHaunted`'s payout | **`0`** | no off-line zeros at all |

The last row is why `NoHaunted` is bought as a *multiplicity* hypothesis and not
an off-line one: reaching its number through this currency is exactly as
expensive as ruling out off-line zeros outright. Prices checked in
`Gaps.offLineImport_board_prices`.

### The multiplicity ladder, generated rather than listed

Every rung is `Optimal`-free arithmetic on one theorem,
`Proportion.certified_nsc_ladder`: assuming `NoSmallHaunted m`,

    Nsc  ≥  (m·κ − 1) / (m − 1),      κ = 0.6725 the certified `NscStd` row.

| `m` | hypothesis | `Nsc`, exact | decimal |
|---|---|---|---|
| 3 | **none — see below** | `407/800` | `0.5087500` |
| 5 | no haunted ordinate of mass `3` | `189/320` | `0.5906250` |
| 7 | none of mass `3` or `5` | `1483/2400` | `0.6179167` |
| 9 | none of mass `3`, `5` or `7` | `2021/3200` | `0.6315625` |
| ⋯ | ⋯ | ⋯ | ⋯ |
| `→ ∞` | `NoHaunted` | — | `0.6725000` |

**A multiplicity cap jumps straight to the bottom row (`SESSION 261`).**
`Gaps.noHaunted_of_boundedMult_of_noSmallHaunted`: with `H ≤ M` in hand, rung
`m > M` *is* `NoHaunted`, because a haunted ordinate would need `m ≤ H ≤ M`. The
cheapest instance is `M = 3` with rung `5`
(`Gaps.noHaunted_of_mult_three_rung_five`), and the arithmetic of that pairing is
worth reading: the cap alone carries `7/400 = 0.0175` on this row (`259`'s
re-verified table), the rung alone `0.590625`, and the two together `0.6725`.
Neither is close to the sum. The cap's value on the `Nsc` row is almost entirely
what it does to the ladder, not what it proves directly.

**And the off-line currency sharpens along the same ladder (`SESSION 262`).**
`Gaps.hauntedDensity_of_offLineImport_at_rung`: under rung `m` a haunted ordinate
costs `m − 1` off-line zeros rather than `2`, so an import at `β` is a haunted
density at `β/(m − 1)`. At the certified `β = 1 − κ` this returns the rungs above
to the digit — `131/800`, `131/1600`, `131/2400`, `131/3200` — so no number on
this board moves. What moves is the hypothesis: this route charges the rung
against `N_off` and needs no `ProportionStd` to state the density, where
`Gaps.hauntedDensity_of_noSmallHaunted` charges it against `N` and does. The two
part company as soon as `β < 1 − κ`: at `β = 1/4` and `m = 5` the off-line route
gives `0.61` against the ladder's `0.590625`.

**What a rung buys, in closed form (`SESSION 236`).** The distance from rung `m`
to `NoHaunted` is `(1 − κ)/(m − 1)` (`Gaps.ladder_gap`), and climbing two rungs
buys `2(1 − κ)/(m² − 1)` (`Gaps.ladder_step`). At the certified `κ` the
numerator `1 − κ` is `131/400 = 0.3275`, the project's own off-line bound, so the
gap at the free first rung is `131/800 = 0.16375` — the haunted-density constant,
here as the `m = 3` case of the general formula. The rungs crowd: rung `3` leaves
`0.16375` unbought, rung `7` leaves `0.0546`, rung `11` leaves `0.0328`.

**Odd `m` only, and that is a theorem as of `SESSION 235`.** A haunted ordinate
carries an odd number of zeros, so `NoSmallHaunted m` for even `m` is the same
hypothesis as for `m + 1` (`Gaps.noSmallHaunted_even_iff`). Since the value
`(m·κ − 1)/(m − 1)` is strictly increasing in `m`, reading an even rung off the
ladder **understates what the hypothesis buys** — at `m = 4` it returns
`0.5633…` where the identical demand, read at `m = 5`, returns `0.590625`.

**The first rung is free, and that is a theorem as of `SESSION 234`.**
`Gaps.noSmallHaunted_three` proves `NoSmallHaunted F 3` outright: a haunted
ordinate carries at least three zeros, because the functional equation pairs its
off-line ghosts. So `m = 3` demands nothing, and the ladder's first rung returns
`407/800 = 0.50875` — which is `certified_nsc_unconditional`. **The certified row
is the ladder's bottom rung**, not a separate result that happens to agree.

`NoHaunted` is displayed because it is the ladder's limit and the genre's
weakest member: every rung is implied by it (`NoSmallHaunted.mono`), and it is
the row a buyer of this currency should price. The rungs between are for someone
who can prove less than `NoHaunted` and more than nothing.

**Two rows are struck on the mathematics, not on taste:**

* **`H ≤ 2`** is dominated by `NoHaunted` — strictly stronger hypothesis
  (`noHaunted_not_mult_le_two`), identical payout. *(`255`: this is now a term
  at the level the board works at — `Family.noHaunted_of_boundedMult_two`. Until
  then the domination was stated here and witnessed only one `ZeroData` at a
  time.)* *(`257`: and the strictness is not idle — `H ≤ 2` also buys the
  star bound, which `NoHaunted` does not: `noHaunted_no_starBound` exhibits an
  unhaunted configuration of star ratio `m` for every `m`. The two hypotheses
  agree on the `Nsc` row and part company on the star row, so striking the row
  is right and dropping the hypothesis from the discussion would not be.)*
* **ξ′** is dominated by the `m = 7` rung — fewer points *and* two more axioms.

### Where the two currencies stop (`SESSION 240`)

Both saturate at `κ = 0.6725`, the certified `NscStd` row:

* off-line control buys at most `κ`, and only at `β = 0` (`239`);
* the multiplicity ladder buys **strictly** less than `κ` at every finite rung
  (`Gaps.ladder_lt_kappa` — the `m` cancels and it reduces to `κ < 1`), with
  `NoHaunted` the limit that reaches it.

`Gaps.currencies_saturate_at_kappa` states the pair. So **any row promising more
than `κ` on the `Nsc` line — Route I, `[OPEN D]` — is buying a third thing**, and
that is a fact about the two exchanges rather than a gap in the search.

**And the third thing is the star bound, whose ceiling is `1` (`SESSION 241`).**
`proportion_of_starBound` pays `2 − C` and `one_le_of_starBound` floors `C` at
`1`, so that currency buys at most `1`, exactly at `C = 1`
(`Counts.starBound_ceiling`). The three currencies therefore split cleanly:

| currency | ceiling | rows |
|---|---|---|
| off-line control | `κ = 0.6725`, at `β = 0` | the certified row, `ξ'`, Route III |
| multiplicity ladder | `κ`, in the `NoHaunted` limit | the ladder, `NoHaunted` |
| star bound `(★)` | **`1`**, at `C = 1` | Route I, `[OPEN D]` |

Two of the three cannot pass the number the project was handed. The one that can
is the one whose rows carry a single axiom and an unsupplied analytic input.

## What the decision actually is

Not "how many points". **Which currency of assumption, and how much of it.**

* **multiplicity** — the ladder (`m = 5, 7, → ∞`). A certified strictly
  increasing chain with `NoHaunted` as its limit (`156`–`158`), every rung
  compatible with off-line mass, none secretly RH.
* **location** — Route III's narrow box. Its cone is `zetaNonempty` alone — as are
  Route I's and [OPEN D]'s; the three one-axiom rows all reach the ledger
  through `StarBound` or `(★)` rather than through the baseline.
* **arithmetic input** — Route I and [OPEN D]. Both want inputs the project has
  not supplied in 186 sessions; `Riemann.fujii_ineffective` records why Route I's
  is not extractable.

## What I am not asking for

Nothing on this board is asserted, and I am not proposing to assert any of it.
Adopting a row means moving a hypothesis into `Assumptions.lean`, which raises
the trusted base — `R5` calls an axiom garbage height, since clearing it is not
something a later cycle can do.

**`340`: `R5`'s "clearing it is not something a later cycle can do" now has a
counterexample, and it is worth being precise about why it is not a refutation.**
`233` cleared `baseline_przz` and `337` cleared two more, so axioms *have* been
cleared by later cycles. But none of the three was cleared by *proving the
mathematics* — `baseline_przz` was derivable from a stronger axiom already
present, and the other two were placeholders for an import that existed all
along. `R5` is right about the case that matters: an axiom standing in for
something nobody has proved does not come back down. The three that came down
were bookkeeping, not results.
**Declining every row is a coherent answer** and leaves the project exactly where
it is, which is a fully certified `50.88%` with all its derivations proved tight.

## The other two parked items

* ~~**`baseline_przz` is redundant**~~ — **DONE, `SESSION 233`, ruling 3.**
  Deleted with the ceremony the metric requires: the base statement hash moved
  `cd7a22e688df → c3b240548ad8`, `tools/proportion.go` escalated and refused to
  write a log line until `base.version` was bumped `2 → 3`, and the note records
  why. Declared axioms `9 → 8`; the certified cone is still `2`; no number
  moved. `przz_of_zeta23` keeps the literature record as a theorem.
* **The cron prompt's `STATE`/`QUEUE` lines** are stale on the ledger, the
  binding constraint, and queue items 1–4. `LOOP.md`'s `⚠️ READ FIRST` banner
  corrects them on disk — and since `195` that banner is itself machine-checked
  (`forensics/banner_check.py`, six rows against the disk, one reported
  `UNCHECKED` rather than counted green). The prompt text itself is yours to
  edit.

  `294` adds queue item 3 — *"is the profile minimal? look for a coarser
  sufficient statistic or an argument that none exists"* — to the stale list.
  `profile_not_minimal`, `profile_minimal_among_local` (with its own kill
  condition, which did not fire), `mass_only_not_sufficient`,
  `off_only_not_sufficient` and `distinctZeros_not_profile_functional` were all
  on disk before the item was written. That is `S33`'s shape a fourth time;
  `R26`'s statement-index query surfaced it in one command, before any Lean was
  written, which is the intended cost.

  `295` adds items 1 and 2. Item 1 asks for a triage of *"claims_gate's six
  `CLAIMS.md` flags"* and a true-positive rate: the gate reports **four** flags
  on `CLAIMS.md` today, and `149` already reported the rate — `1` true positive
  in `14`, recorded at `S52` along with why the count did not move when the true
  positive was fixed. Item 2's `W32` has been run; its table is in
  `FAILURES.md` with the kill condition recorded, which `S33` noted at `078`.
  **Four of the five queue items are now discharged.** Item 5 is the
  consolidation fallback, so item 4 is the only live one, and the prompt itself
  says item 4 cannot carry a conclusion alone.

## `409` — roster `forensics/register_citations.py`, or leave it a report?

It follows declaration names cited in the registers, the surface
`forensics/citation_check.py` does not cover. First run: `3` true positives in
`33` examined on the live registers, all fixed.

**For rostering:** the defect class is real and nothing else catches it; `406`
and `407` both shipped stale register rows.

**Against:** `373` established that a guard nobody has seen fail is a tally, and
this one has failed exactly once — on its own first run, which is not the same as
catching a regression. Rostering also means the `30` currently-unverified live
flags must be driven to zero or allowlisted first, which is a hygiene sweep, not
a cycle.

**`410` changes one side of this.** The live surface is now triaged to `0`
dangling, not merely counted: every citation resolves or sits in a bucket with a
reason. So the objection *"rostering means first driving 30 unverified flags to
zero"* is discharged — that sweep happened — and a red from this screen would
now mean a regression rather than a backlog. The `373` objection stands: it has
still never caught a regression, because there has not been one since it existed.

**`442` drills it, and halves the question.** Injecting
`Blindness.no_such_lemma_at_all` into `CLAIMS.md` made the screen name it and the
count go `0 → 1` — **and the exit code stayed `0`.** Rostered as written it would
have reported green on that injection, `373`'s category exactly. Added `--gate`,
which exits `1` on live dangling; drilled both ways, `1` with the injection and
`0` without. So the `373` objection is now about **whether you want a
seventeenth roster entry**, not about whether the thing can fail. Live dangling
has been `0` for thirty cycles of heavy register editing.

**Not taken.** Runs as a report until Joop rules.
