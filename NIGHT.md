# NIGHT — overnight run of 2026-08-13/14

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
