# RULING — the one decision the ledger waits on

**For Joop. Verified `SESSION 186`; every number below is reproduced in exact
rationals and every cone by `#print axioms`.**

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
| axioms declared | 9 |
| sorries | 0 |
| build | green, 3757 jobs |

**The `Nsc` row cannot move from what the project already holds.** `111`/`112`
prove it is within `0.00069` of the best obtainable from the baseline alone;
`169` and `175` prove both exchange constants optimal and attained; `178`–`180`
prove every route bound tight at every size. There is no derivation left to
sharpen. **Every remaining gain requires assuming something.**

## The board

Gains are on the `Nsc` row over the certified `0.50875`.

| route | `Nsc` | gain | axioms | hypothesis |
|---|---|---|---|---|
| `m = 5` rung | `0.590625` | `+8.188` | 2 | no haunted ordinate of mass `3` |
| ~~ξ′~~ | `0.601690` | `+9.294` | **4** | two analytic `Prop`s, Conrey 1983, unread |
| `m = 7` rung | `0.617917` | `+10.917` | 2 | none of mass `3` or `5` |
| **Route III** | `2/3 − ε` | `+15.792` | **1** | narrow box (BGST) |
| `NoHaunted` | `0.672500` | `+16.375` | 2 | no haunted ordinate at all |
| ~~`H ≤ 2`~~ | `0.672500` | `+16.375` | 2 | multiplicity `≤ 2` |
| **Route I** | `> 0.6725` | `> +16.375` | **1** | effective Fujii `c₀ ≤ 0.33` |
| **[OPEN D]** | `1 − ε` | `+49.125` | **1** | extended support |

**Two rows are struck on the mathematics, not on taste:**

* **`H ≤ 2`** is dominated by `NoHaunted` — strictly stronger hypothesis
  (`noHaunted_not_mult_le_two`), identical payout.
* **ξ′** is dominated by the `m = 7` rung — fewer points *and* two more axioms.

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

* **`baseline_przz` is redundant** — `przz_of_zeta23` derives it from
  `baseline_zeta23` via `ProportionStd.mono`. Deleting it drops the declared
  surface `9 → 8` and changes no number. Your call.
* **The cron prompt's `STATE`/`QUEUE` lines** are stale on the ledger, the
  binding constraint, and queue items 1–4. `LOOP.md`'s `⚠️ READ FIRST` banner
  corrects them on disk; the prompt text itself is yours to edit.
