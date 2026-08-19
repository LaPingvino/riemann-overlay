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

**The chain splits by family, and one side alternates.**
`Riemann.Optimal.chain_upper_four_determined_by_on_moments`: the on-line moments determine
`NscStd`, `oddAtoms`, `onLineOrdinates` and `atomCount`, and
`Riemann.Blindness.Nsc_not_determined_by_on_moments` shows they stop below `N_sc` — an
interval. The `H`-moments do **not** form one: they have `N_sc`
(`Riemann.Optimal.massCount_determined_by_all_moments`), miss `NscStd`
(`Riemann.Blindness.NscStd_not_determined_by_all_moments`), have `oddAtoms`
(`Riemann.Optimal.oddAtoms_determined_by_all_moments`, since `Riemann.Blindness.even_offAt`
makes it a mass functional), miss `onLineOrdinates`
(`Riemann.Blindness.onLineOrdinates_not_determined_by_all_moments`), and have `atomCount`.

**The ledger costs five scalars, not two families.**
`Riemann.Blindness.ledger_determined_by_five_scalars`: `momentK 1`, `momentK 2`,
`massCount 1`, `onMoment 1` and `onCount 1` determine `N`, `N⊛`, `Nsc`, `NscStd` and
`N_off`. All five are necessary (`370`), so no proper subset determines the ledger:
`Riemann.Blindness.onCount_one_cannot_be_dropped`,
`Riemann.Blindness.momentK_one_cannot_be_dropped`,
`Riemann.Blindness.momentK_two_cannot_be_dropped`,
`Riemann.Blindness.massCount_one_cannot_be_dropped` and
`Riemann.Fiber.Noff_not_determined_by_ledger`. That is minimality under inclusion, not a
claim that five is the smallest count — and unrestricted there is no such claim to make, since
`Riemann.Blindness.ledgerCode_eq_iff` packs the whole ledger into one natural number. A
minimality statement here is always relative to a declared class of statistics. `Riemann.Fiber.profile_not_minimal` (`075`/`077`) is
the older, weaker negative.

**Each family's reach is exactly its own count family.**
`Riemann.Optimal.moment_blind_iff_massCount` and
`Riemann.Optimal.on_moment_blind_iff_onCount` are equivalences, not implications — the
converses being the weighted fiberwise sums `Riemann.Blindness.momentK_eq_sum_massCount` and
`Riemann.Blindness.onMoment_eq_sum_onCount`. So "determined by the moments" and "a functional
of the counts" are one predicate per family, and the chain's order does not enter.

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

**One analogy, tested and dropped.** `361` noticed that the paper's *bandwidth-one
certificate* data resembles the profile; `363` refuted the naive reading —
`Riemann.Blindness.NscStd_not_determined_by_two_moments_and_split` shows three global
numbers do not fix `NscStd`, so the paper's class is strictly richer. The `≈0.682` ceiling
is over that richer class.

**And what would pass the wall, named by the source.** `arXiv:2608.13637` §7.2 puts the
ceiling of its own method at `≈0.682` and says passing it needs *"pair-correlation
information beyond Fourier support 1"*; §7.3 prices two conditional rows —
`HL*(k₀)` gives `13/18 = 0.7222…`, above this project's row, and every support gives
`100%`. Neither is adoptable: both are open conjectures. `PRICES.md`, `SESSION 361`.

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
* **`T3`, the solved-problem control** — **blocked at `364`, with the blocker named.**
  Its content is a chronology, and the register's own rule is that date verification is a
  prerequisite; none of the sandbox's four allowlisted hosts was a bibliographic database (**`377`: zbMATH Open is now the fifth allowlisted host, ruled by Joop**),
  and writing the chain from memory is what `S27` forbids. One allowlist entry would
  unblock it. `forensics/absence_queue.py` now reports **`0`** live obligations.
* **The rung-0 certificate file** — `cert_N256_blk_b128m.json`, absent from the
  repository at the pinned tag; the paper names the law's location and `p₀ ≤ 0.6818287`
  but the form factor's provenance is the interval-arithmetic run.
* **The paper's proof** — unread. `356` read §1, §1.4, the constant definitions and
  Appendix A; `361` added §7.2, §7.3 and Remark 7.1. Every register note says so.
* **`Riemann.zeta23_xiPrime`** — still an axiom, and `361` establishes that the reason is
  not the constant. Remark 7.1 states `0.85838` unconditionally; the blockers are that
  `Riemann.xiPrimeFamily` is itself an axiom with no construction, and `ISSUES` `#7`'s
  `Proportion`-versus-`ProportionStd` gap, whose content `283` names as
  `NoHaunted xiPrimeFamily`.

## The exchange arithmetic — where the numbers live

**`S171`: seven cycles between `374` and `383` re-derived results already here**, among them
`Riemann.starBound_delta_beats_baseline` and `Riemann.starBound_exchange_crossover`. The cause
is that these are theorems about *real inequalities*, so a search for a declaration **name** does
not reach them. Search the conclusion.

**The `HauntedDensity` hub.** Every supplier below feeds
`Riemann.proportion_of_hauntedDensity`, which turns `HauntedDensity F δ` and `ProportionStd κ`
into `Proportion (κ − δ)`.

| supplier | rate | with `NoSmallHaunted m` |
|---|---|---|
| off-line control | `Riemann.hauntedDensity_of_offLineImport`, `β/2` | `..._at_rung`, `β/(m−1)` |
| the ladder itself | `Riemann.hauntedDensity_of_noSmallHaunted`, `(1−κ)/(m−1)` | — |
| star bound | `Riemann.hauntedDensity_of_starBound`, `(C−1)/6` | `..._at_rung` (`383`), `(C−1)/(m(m−1))` |
| distinct zeros | `Riemann.hauntedDensity_of_distinctZeros`, `(1−c)/2` | `..._at_rung` (`384`), `(1−c)/(m−1)` |

**All three non-ladder suppliers compose with the ladder** (`384`), and **both rung
coefficients are exact** — `Riemann.Blindness.rung_coefficients_attained` (`385`) makes the
mass-`m` haunted atom an equality in each, so neither can be improved by sharpening the same
argument.

**The three rung currencies and where they bite** (`401`–`405`). Underneath the suppliers sit
three charges, one per counting coordinate. Each has a general-`G` bound, a termwise cost
identity, and — since `405` — a converse saying exactly when the summed bound is an equality.

| currency | charge | general-`G` bound | converse |
|---|---|---|---|
| `N − atomCount` | `m − 1` | `Blindness.mass_card_le_N_sub_atomCount` (`405`) | `Blindness.mass_card_eq_N_sub_atomCount_iff` |
| `N⊛ − N` | `m(m−1)` | `Blindness.mass_card_le_Nstar_sub_N` (`382`) | `Blindness.mass_card_eq_Nstar_sub_N_iff` |
| `momentK k − N` | `m^k − m` | `Blindness.mass_card_le_momentK_sub_N` (`386`) | `Blindness.mass_card_eq_momentK_iff` (`404`) |

The star row is the moment row at `k = 2`: `Blindness.momentK_two` says `N⊛ = momentK 2` and
`m(m−1) = m² − m`. **All three converses have the same right-hand side** —
`Blindness.rung_currencies_agree` (`405`) — so the currencies differ in what they charge, not in
where they bite.

**The crossovers, and the pairs that repeat one fact.** `Riemann.starBound_delta_beats_baseline`
and `Riemann.starBound_exchange_crossover` are the canonical forms; the right-hand column names
what re-derived each.

| fact | canonical | re-derived at |
|---|---|---|
| `(C−1)/6 < 0.16375 ↔ C < 1.9825` | `Riemann.starBound_delta_beats_baseline` (`304`) | `Blindness.star_route_beats_iff` (`374`) |
| `0.6725 − (C−1)/6 ≤ 2 − C ↔ C ≤ 1.393` | `Riemann.starBound_exchange_crossover` (`191`) | `Blindness.star_currency_crossover` (`377`) |

Other exchange biconditionals on disk: `Riemann.ladder_beats_iff`,
`Riemann.offLineImport_inverse`, `Riemann.offline_roundtrip_eq_iff`,
`Riemann.oddAtoms_input_beats_certified_row_iff`, `Riemann.onLineOrdinates_route_threshold`,
`Counts.starBound_ceiling_iff`, `Blindness.star_rung_threshold`.

