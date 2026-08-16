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

| | |
|---|---|
| certified `NscStd` | **67.25%** (`baseline_zeta23`) |
| certified `Nsc` | **50.88%** (`certified_nsc_unconditional`) |
| axioms in the certified cone | **2** |
| axioms declared | **8** (`SESSION 233`: `baseline_przz` deleted on ruling 3) |
| sorries | 0 |
| build | green, 3757 jobs |

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
| **`NoHaunted`** | `0.672500` | `+16.375` | 2 | no haunted ordinate at all |
| **Route III** | `2/3 − ε` | `+15.792` | **1** | narrow box (BGST) |
| **Route I** | `> 0.6725` | `> +16.375` | **1** | effective Fujii `c₀ ≤ 0.33` |
| **[OPEN D]** | `1 − ε` | `+49.125` | **1** | extended support |

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
  (`noHaunted_not_mult_le_two`), identical payout.
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
