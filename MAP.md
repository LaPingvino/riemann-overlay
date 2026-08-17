# MAP — what this project has established, in one page

**Written `SESSION 359`. For Joop, and for the next compacted instance.**

Every claim below names a declaration or a register location. Nothing here is new:
if a sentence is not backed by a name, it does not belong on this page, and
`359`'s wildcard was to check that every name resolves.

The registers this compresses are `CLAIMS.md` (graded claims with witnesses),
`SESSION.md` (the cycle-by-cycle record), `PRICES.md` (what each route costs),
`RULING.md` (the decision), `SURPRISES.md` (where beliefs were wrong).

---

## 1. The ledger, and what it rests on

| | |
|---|---|
| certified `NscStd` | **67.25%** — `Riemann.certified_std` |
| certified `Nsc` | **50.88%** — `Riemann.certified_nsc_unconditional` |
| axioms in the certified cone | **0** — measured by `audit/PrintAxioms.lean` via `tools/proportion.go` |
| axioms declared | **6** — `Riemann/Assumptions.lean`, none in the certified cone |
| sorries | 0 |
| base | `v4/3508643365fd` |

`67.25%` is not an axiom. `SESSION 337` discharged `Riemann.baseline_zeta23` and
`Riemann.zetaNonempty` into theorems, proved through the vendored dependency, and
the ceremony is `tools/metric.json`'s **base.version** bump with
`tools/proportion.go` refusing to log until it happened.

**`50.88%` follows from `67.25%` with no extra input.**
`Riemann.Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc` gives
`(3κ − 1)/2` from `ProportionStd κ`, and `111`/`112` show the result is within
`0.00069` of the best the baseline alone permits.

## 2. Where the numbers come from, and who published them

`arXiv:2608.13637` (Alpöge–Furman, 13 Aug 2026) is the paper of the artifact this
repo vendors. Its Lean repository is `github.com/anthropics/zeta-23-lean`; our pin
`3635e74…` is the tip of that repo's tag **v1.0**, which is the tag the paper cites
(`vendor/PROVENANCE.md`, `SESSION 357`). `forensics/vendor_check.py` verifies the
local copy is byte-identical to the pin on every cycle.

The `0.6725` is the paper's Montgomery–Taylor window constant `2 − c_MT⁻¹`, which
`Riemann.baseline_decimal_le_exact` bounds below by the decimal we report; the
paper calls it *"optimal among windows"* and puts the ceiling over all
bandwidth-one certificates at *"approximately 0.682"*. The `2/3` in the paper's
title is the weaker indicator window. Details and quotes: `LEADS.md`, `SESSION 356`.

**One numerical debt, and it is the paper's own.** `EnclOK` — the interval-arithmetic
enclosures behind `Zeta23.PairCeiling.ceiling_law256` — is, in the paper's words,
*"certified by interval arithmetic and not checked by the Lean kernel"* at tag **v1.0**.
Our certified rows do not consume it (`forensics/board.py --cones` reports them
axiom-free); it bounds the *wall*, not the row. `PRICES.md`'s rung-0 section.

## 3. X — what a certificate of this kind cannot see

This is the project's own contribution, and it is the largest part of the Lean.

**The reported row is invisible to the ordinates.**
`Riemann.Blindness.NscStd_not_ordinate_functional`: no function of the ordinate
multiset computes `NscStd`. `Riemann.Blindness.no_muInvariant_theory_computes_NscStd`
is the necessity form.

**The profile is what suffices**, where the profile is the multiset of
`(mass, off-line mass)` pairs: `Riemann.Blindness.N_from_profile`,
`Nstar_from_profile`, `Nsc_from_onProfile`, `NscStd_from_onProfile`,
`Noff_from_profile`. It is **not minimal** (`Riemann.Blindness.profile_not_minimal`)
and it **is** minimal among local coarsenings
(`Riemann.Blindness.profile_minimal_among_local`).

**Off-line zeros are invisible to the reported row, at any size.**
`Riemann.Blindness.NscStd_insensitive_to_offLine`: superposing a configuration with
no on-line zeros leaves `NscStd` unchanged. The project's stronger row does move —
`Riemann.Blindness.Nsc_sensitive_to_offLine` — and the difference is
`hauntedCount`, which `Riemann.Blindness.hauntedCount_eq_NscStd_sub_Nsc` names.
This is the count-level form of the paper's own §1.4.

**And reaching the row constrains nothing about location.**
`Riemann.proportionStd_admits_positive_offline_density`: a constant family on one
haunted ordinate among four simple ones satisfies `ProportionStd 0.6725` while `2/7`
of its zeros are off the line, a share that does not decay. That is the second clause
of the paper's §1.4 in this vocabulary.

**Heights carry nothing.** `Riemann.Blindness.ledger_relabel_invariant`.

## 4. The five-class decomposition and the moment arc

Every ordinate is exactly one of five classes —
`Riemann.Blindness.atomCount_decomposition` — and the chain
`N_sc ≤ NscStd ≤ oddAtoms ≤ onLineOrdinates ≤ atomCount` has all four gaps named.

**What the moment family sees.** `Riemann.Blindness.momentK_ordinate_functional`
makes every moment a functional of the ordinates, so by §3 none of the four gaps is
moment-computable (`Riemann.Blindness.hauntedCount_not_momentK_computable` and its
three siblings). Positively:
`Riemann.Optimal.massCount_determined_by_all_moments` — the moments determine every
mass count; and `Riemann.Blindness.NscStd_not_determined_by_all_moments` — they do
not determine the reported row, witnessed by a haunted ordinate against a pure
triple.

**Swapping the weight fixes it.** `Riemann.Optimal.NscStd_determined_by_on_moments`:
the moments of the *on-line* count determine `NscStd`, with no hypothesis. And
`Riemann.Blindness.Nsc_not_determined_by_on_moments` shows that family misses the
other row — so each family sees one row and misses the other.

**Both together determine the whole ledger and still not the profile.**
`Riemann.Optimal.ledger_determined_by_both_moment_families` and
`Riemann.Blindness.profile_not_determined_by_both_families`.

**A multiplicity cap computes the row rather than bounding it.**
`Riemann.Blindness.capWitness_eq` at every bound, `Nsc_from_moments` for the moment
form, and `two_mul_Nsc_eq_iff` for the cap-`3` identity with its `iff`.

## 5. The board, and why it has not moved

Both currencies the project owns saturate at `κ`:
`Riemann.currencies_saturate_at_kappa`. The multiplicity ladder's rungs are
`(mκ − 1)/(m − 1)`, strictly below `κ` at every finite rung
(`Riemann.ladder_lt_kappa`) and approaching it
(`Riemann.ladder_approaches_kappa`). `Riemann.ladder_beats_iff` gives each competing
row's threshold rung; `Riemann.ladder_beats_routeII_first_at_seven` and
`Riemann.ladder_beats_routeIII_first_at_fiftynine` locate two of them.

Since `337` **every board row is axiom-free except Route II** — measured, not
assumed, by `forensics/board.py --cones` (`SESSION 340`). So adopting any row now
costs `0 → 1` axioms rather than `2 → 3`. `RULING.md` carries the re-priced board.

**What is dominated, and why.** The distinct-zeros route pays nothing at any input
constant: `Riemann.distinctZeros_route_ties_at_one`. The moment route is walled at
every order: `Riemann.Optimal.moment_route_walled`,
`Riemann.Optimal.linearBoundK_no_gain`.

## 6. The instruments

Seventeen scripts in `forensics/`, sixteen of them in `forensics/session_gate.py`'s
roster, which is the call before every commit. Three are ratchets rather than
checks: `forensics/warning_floor.py` (54), `forensics/duplication_floor.py` (26), `forensics/overclaim_floor.py` (203).
Each was controlled by being made to fail on purpose, and the entries say when.

The ones that have caught live defects, with the cycle: `forensics/citation_check.py` (`301`,
`334`, `343`), `forensics/duplication_floor.py` (`303`, `316`, `339`), `forensics/warning_floor.py` (`329`),
`forensics/session_gate.py` (`334`, `353`), `board --cones` (`340`), `forensics/overclaim_floor.py` (`344`,
`345`, `347`, `353`), `forensics/statement_index.py` (`326`, `341`).

## 7. What is open

* **The literature asks in `PRICES.md`** — an eventual `oddAtoms ≥ c·N` with
  `c > 0.6725`, and any improvement to the distinct-zeros proportion. Both would
  need sources outside the registers.
* **The `Acta Arith.` 214 narrow-box statement and its `61.7%`** — still
  `[RECALL, UNVERIFIED]`; `355` names the three searches that did not reach it.
* **`forensics/absence_queue.py`'s one live entry** — `T3`, the solved-problem control, needing
  FLT and an open control.
* **The rung-0 certificate file** — `cert_N256_blk_b128m.json`, absent from the
  repository at the pinned tag; the paper names the law's location and `p₀ ≤ 0.6818287`
  but the form factor's provenance is the interval-arithmetic run.
* **The paper's proof** — unread. `356` read §1, §1.4, the constant definitions and
  Appendix A, and every register note says so.
