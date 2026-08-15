# CLAIMS — every class-impossibility assertion, graded

This project's most valuable statements are of the form *"no member of class `C`
can do `X`"*. They are also the easiest kind to leave in a docstring, because
they feel settled once the argument is understood. Two were found living as
prose in three cycles (`FAILURES.md` `#10`'s rung 0, and `Gauge.lean`'s
LP-optimality), and both turned out to be true — so the risk was never that we
believed false things, but that a reader could not tell which beliefs they were
entitled to check.

This file is the inventory. **Anything cited as a bound must appear here with
grade A.**

## The three grades

* **A — certified.** A machine-checked statement quantified over the named
  class. Cite freely.
* **B — certifiable, but prose.** The class is well defined and a theorem could
  be stated; none exists yet. **This is the disease.** Cite only with the word
  "unformalised" attached.
* **C — class undefined.** The claim quantifies over something informal ("cheap
  invariants", "classical invariant"). Defining the class is the *prerequisite*
  for promotion — and per S23 that can be cheap, so C is **not** a life
  sentence. It is **not a bound** in the meantime; do not cite one as such.
* **N — class defined, evidence numerical.** The class is precise and the claim
  is checkable in principle, but what supports it is a computation, not a proof.
  Cite only with the word "numerically" attached. **Never as a bound.** A grade-N
  entry whose *code is not in the repo* is worse than unproved — it is
  unreproducible, and must say so.

## The inventory

| claim | class | certificate | grade |
|---|---|---|---|
| `μ_T` cannot see `β`; `NscStd` is not an ordinate functional | `μ_T`-invariant hypotheses (closed under deduction) | `Blindness.no_muInvariant_theory_computes_NscStd`, `NscStd_not_ordinate_functional` | **A** |
| `N⊛` is depth-blind; depth-shaped input has price zero | same | `Blindness.no_muInvariant_bundle_computes_Noff`, `Fiber.blind_at_every_crowded_mass` | **A** |
| Vertical blurring cannot separate a zero from its twin (A2) | smoothing at any radius `r ≥ 0` | `Blindness.two_le_Hr_of_off_line`, `Basic.on_line_of_Hr_eq_one` | **A** |
| The blindness is supported exactly on crowded atoms; mass one is sighted | same | `Fiber.Noff_eq_zero_of_simple` + `blind_at_every_crowded_mass` | **A** |
| No functional of `μ_T` discriminates the fiber coordinate; the Landau weight does | functionals factoring through `μ_T` | `Fiber.not_discriminates_of_factors`, `landau_discriminates` | **A** |
| `NscStd` reads the **on-line counts** and nothing else; `Nsc` reads the total mass | pointwise, over all `ZeroData` | `Fiber.NscStd_eq_onAt_functional`, `Nsc_reads_total`, `H_eq_onAt_add_offAt` | **A** |
| **`(μ_T, offAt)` determines the *entire ledger*** — `N`, `N⊛`, `Nsc`, `NscStd`, `N_off`. **Sufficient, not minimal** | all `ZeroData`, global | `Fiber.ledger_determined`; non-minimality by `Fiber.offAt_not_minimal` | **A** |
| **The profile determines the ledger** — all five quantities are functionals of the multiset of `(mass, off-line mass)` pairs, heights discarded. *Sufficient; minimality not claimed* | all `ZeroData` | `Fiber.N_from_profile`, `Nstar_from_profile`, `Nsc_from_profile`, `NscStd_from_profile`, `Noff_from_profile` | **A** |
| The ledger is invariant under any injective **relabelling of ordinates** — their names carry no information | all `ZeroData`, all injective `σ` | `Fiber.ledger_relabel_invariant` | **A** |
| The real Landau weight **cannot** recover `offAt` — it agrees on the swap pair at every `x` | functionals of `Σ_ρ x^β` alone | `Fiber.landau_cannot_determine_offAt` | **A** |
| `prop1` is optimal among linear bounds in `(N, N⊛)` | `LinearBound a b` | `Optimal.prop1_LP_optimal` | **A** |
| Extension past the known range is useless, and fatal if the multiplier dips negative | `{F pinned on A, F ≥ 0 off A}`, `A` measurable | `Capacity.no_gain_past_known_integral`, `unbounded_below_of_neg_outside_integral` | **A** |
| `offline_le`'s `(C−1)` cannot be improved to `(C−1)/2` | the inequality itself | `Gauge.offline_le_tight` (saturating witness) | **A** |
| Route I cannot do better than `c₀ ≈ 0.16` | any effective Fujii constant | `Fujii.c0_lower_bound` | **A** |
| The bandwidth-one ceiling is `≤ 0.6818287` | bandwidth-one certificates | `Zeta23.PairCeiling.ceiling_law256` — **imported**, and *not reachable from `import Riemann`* | **A**, with a caveat parked for Joop |
| "Multiplicity bounds cannot tighten `C`" (W7, precise part) | `BoundedMult M` — `H γ ≤ M`, pure counting, no Euler product | `Optimal.prop1_LP_optimal_cheap` | **A** |
| "No free classical invariant *of any kind* will tighten `C`" (W7, general) | *"classical invariant"* — still informal | — | **C** |
| "Post-1974 extremal technology cannot buy anything through the `v` slot" | the `v` slot of the rank–trace container at `λ = 1` — **well defined** | a quadrature optimisation (`N = 160` midpoint, `0.6725126` vs M–T's `0.6725007`), reproducible via `forensics/window_opt.py` | **N** |
| E20's plane: the cleavage is the one thing no single-natured instrument can certify | *"single-natured instrument"* — informal | — | **C**, and already marked statistically unsupported in `FAILURES.md` |

## The sweep's verdict (night cycle 8)

**Kill condition, stated first:** *if the sweep finds no further uncertified
class-impossibility claims beyond the two already fixed, the "pattern" was two
coincidences and must not be generalised into doctrine.*

**It fired, in the informative direction.** Every Lean docstring's impossibility
claim is backed — `c0_lower_bound` and `offline_le_tight` are real theorems, not
prose, and I expected at least one of them not to be. **Grade B is now empty.**

The two remaining uncertified claims are **grade C, not grade B**: their classes
are informal, so they are not theorems-in-waiting but statements of a different
species. Promoting them would require *defining* "cheap invariant" and
"post-1974 technology" first, which is a research question rather than a
formalisation task.

**So the pattern does not generalise into doctrine.** What survives is narrower
and more useful: a standing inventory, and the rule that a claim cited as a
bound must be grade A. The disease was real, finite, and is now cured; what
remains is a category that could not be cured by formalisation **as the classes
then stood**.

> ⚠️ **Corrected one cycle later (S23), and the correction belongs here rather
> than sixty lines below.** "Never curable by formalisation" was wrong: W7's
> grade-C entry was promoted in a single cycle once its class was defined
> (`BoundedMult`, `Optimal.prop1_LP_optimal_cheap`). Grade C means *not yet
> defined*, not *undefinable*.


## Amendment (night cycle 9) — grade C is not a life sentence

`CLAIMS.md` asserted, one cycle ago, that promoting a grade-C claim "would
require *defining* the class first, which is a research question rather than a
formalisation task". **For W7 that took one cycle.**

Every constraint in the cheap family has the same shape — an upper bound on
horizontal multiplicity — and that shape is pure counting with no multiplicative
input. `BoundedMult M D := ∀ γ, D.H γ ≤ M` is the class, and
`Optimal.prop1_LP_optimal_cheap` proves that assuming *any* such bound
(`M ≥ 2`) leaves the two-moment optimum at `2 − C`. The binding configurations
have `H ≤ 2`, so the cheap invariants are satisfied by construction and cannot
bind — which is exactly what the autopsy said, now as a theorem.

**Scope, stated plainly:** this certifies the vacuity of *multiplicity bounds*
for *this* extremal problem. The wider claim — that no classical invariant of
any kind tightens `C` — quantifies over a class still undefined and stays C.

**Revised guidance:** grade C means *the class has not been defined yet*, not
*the class cannot be defined*. When a C entry's claims all share one shape, that
shape is usually the definition. Filed as `SURPRISES` S23.


## Amendment (night cycle 10) — a fourth grade, and an unreproducible table

**Kill condition, stated first:** *if "post-1974 extremal technology" collapses
into the bandwidth-one class already certified by `ceiling_law256`, the entry is
a duplicate of an existing grade-A row rather than a new class.* **It did not
fire.** The registers are explicit that the two are different: the `0.28pp` gap
up to the bandwidth-one ceiling "does not live in window shape; it must live in
the richer certificate class their ceiling theorem quantifies over". The `v`
slot is a strict subclass.

**So the class is definable — and the grading scheme was missing a bin.** The
claim's support is neither a proof (grade A) nor prose (B) nor an undefined
class (C). It is a **numerical optimisation**: `N = 160` midpoint quadrature
over windows at `λ = 1`, giving `0.6725126` against Montgomery–Taylor's
`3/2 − ϑ cot ϑ`. Hence grade **N**.

**Verified tonight:** `3/2 − (1/√2)cot(1/√2) = 0.6725007036794116`, matching the
register's `0.6725007` exactly. The quoted optimiser sits `1.19 × 10⁻⁵` above
it, consistent with the stated quadrature error — so the *identification* is
sound as a numerical statement.

**And the snag that matters more than the grade:** the optimisation's **code is
not in this repo.** `forensics/` holds `lemma1_guard.py`, `provenance_lint.py`,
`quarry.py`, `w16_price.py` and `surprises.py` — no window optimiser. The table
in `LEADS.md` and the `18.18pp` instrument claim in `E.md` rest on a computation
that a reader cannot re-run and that we cannot re-run either.

That is a **reproducibility defect, not a mathematical one**, and it is the
first found in this repo. It was filed as `ISSUES` #29 rather than repaired
that night — **and #29 has since been resolved: the specification was in
`LEADS.md` all along and `forensics/window_opt.py` reproduces every digit
(S27).** The reasoning below stands as stated at the time: reconstructing the variational problem from memory would produce a
script that computes *something*, and passing that off as the original
computation is exactly the failure mode this project exists to avoid.

## Quantitative audit (night cycle 11)

**Kill condition, stated first:** *if `#29` is the only unreproducible number,
the defect is isolated and the sweep says so rather than inflating it.*
**It fired for its stated scope** — `#29` is the sole *missing-computation*
defect. The sweep then found a different species, recorded below.

Every computed figure in the registers, traced:

| figure | provenance | status |
|---|---|---|
| `0.6818287` bandlimited ceiling | `Zeta23.PairCeiling.ceiling_law256` | Lean ✓ (imported; unreachable from our root — parked) |
| `0.6725007` Montgomery–Taylor | closed form `3/2 − (1/√2)cot(1/√2)` | verified exactly, night 10 ✓ |
| `5.035` row-opening threshold | `1 + 6 × 0.6725`, and `Proportion.nsc_row_opens` carries `C < 5.035` | Lean ✓, arithmetic transparent |
| `2.345` (the `/2` route's threshold) | `1 + 2 × 0.6725` | exact ✓ |
| `19/27 = 0.703704` (CGG98) | exact rational | ✓ |
| `1.3275` (record-beating `Cbound`) | `Fujii.Cbound_lt_record` | Lean ✓ |
| `0.85838` (`ξ'` proportion) | axiom `zeta23_xiPrime`, declared | trusted base ✓ |
| `0.80869`, `0.809` | **retracted** (`ISSUES` #27), marked | ✓ |
| `7.995`, `9.532`, `3.667`, `1.4283`, `0.8126`, `10.824` | **retracted** (`ISSUES` #24/#25) | ✓ *but see the ordering defect* |
| `0.6725126` and the whole `λ`-sweep (`0.795…0.899`) | a quadrature optimisation | **`ISSUES` #29 — code not in repo** |
| `1.3208` (CMR), `0.679`/`0.6792` (CGdL) | literature | `[RECALL]`, and CMR is a lint node |

**The new defect: retraction ordering.** `PRICES.md` carried its retracted
`c`-table at lines 165–176 with the retraction banner at line 183 — *below* the
numbers. A reader scanning the tables would meet `c ≤ 7.995` before meeting the
sentence that voids it. Nothing false was written; it was **badly ordered**,
which for a register meant to be quoted from is the same hazard by a different
route. **Fixed this cycle:** a warning now sits immediately above the tables.

**Standing rule added:** a retraction must appear *above* the material it
retracts, not merely somewhere in the same file.


## Ordering sweep (night cycle 12)

**Kill condition, stated first:** *if `PRICES.md` was the only misordering, the
defect is isolated and the sweep says so rather than manufacturing more.*
**It did not fire — a second instance exists**, of the same species but a
different shape: not a retracted table, a **stale figure still stated as
current**.

`LEADS.md` said, at lines 72 and 125, that L9's payoff window is `+0.93pp`. The
correction — that `0.93pp` is the *total* gap to the ceiling, of which CGdL 2020
already took `0.65pp`, leaving **`0.28pp`** — lived at line 284 and in `E.md`,
i.e. **two hundred lines below the framing it corrects**. Both quoted figures
are arithmetically true; the *framing* was stale, and a reader looking for "what
is left to win" met the wrong number first. Fixed: the correction is now carried
up to both points of use.

**And the sweep found the pattern done right, which is worth naming as the
template.** `LEADS.md`'s W4 entry heads with *"RESURRECTED. The autopsy below
reached the wrong verdict; read the correction first"*, puts the correction
immediately under it, and keeps the superseded autopsy below, labelled
*"verdict superseded"*. That is the shape every correction in these registers
should take: **verdict in the heading, correction next, superseded material last
and marked.** `E.md`'s E20m does the same for the withdrawn statistics.

**Tally: two instances of the defect, both now fixed; one model example.** The
ordering rule stands, with W4 as its worked example.

## Triage of the gate's own flags (2026-08-15, first live measurement)

**Kill condition, stated first:** *if the true-positive rate is zero, the gate is
noise on live registers and its wordlist needs narrowing before the instrument
can be cited at all.* **It did not fire — the rate was 3/6.**

`claims_gate.py` flagged six sentences in this file. Triaged one by one:

| # | sentence | verdict |
|---|---|---|
| 1 | grade C "cannot be promoted without first defining the class" | **true** — the residue of the claim `S23` falsified; W7's C entry was promoted in one cycle |
| 2 | "Never cite as one." | false — a directive, not a claim |
| 3 | "**Never as a bound.**" | false — same |
| 4 | "a category that was **never curable by formalisation**" | **true** — falsified by `S23` outright |
| 5 | "grade C means not yet defined, **not** *that the class cannot be defined*" | false — the trigger sits inside a phrase being denied |
| 6 | "filed as `ISSUES` #29 rather than repaired tonight" | **true** — stale; #29 has since been resolved (`S27`) |

**All three true positives were stale text whose correction already existed
elsewhere in the file.** The gate rediscovered ordering violations from a
completely different direction than the ordering sweep did — a wordlist scan and
a retraction audit converging on the same defect is the closest thing to
independent confirmation this project has produced about its own prose.

All three are now fixed **at their locations**, and `CLAIMS.md` reports **zero**
unwitnessed flags.

**And the three false positives were two mechanical shapes**, both now excluded
without touching the wordlist: *directives* ("Never cite as one") and *denied
quotations* ("not *that the class cannot be defined*"). The calibration cases
`S26` and `S27` are still caught after the narrowing.

**Remaining, and explicitly untriaged:** `LEADS.md` 25, `E.md` 10. Those counts
are a queue, not a defect rate — the same caution that applied before the
triage still applies to them.
