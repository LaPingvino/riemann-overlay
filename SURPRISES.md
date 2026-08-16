# SURPRISES — the calibration meter

Every time the record went **against my stated expectation**. Not every error:
an error I never had a view on is just a fact I learned. This register counts
the cases where I had a position and the world disagreed.

**Schema:** `id | session | I expected | what happened | corrected by | class`

`corrected by`: `kernel` (Lean said no) · `tooling` (a guard, the lint, the
ledger, a script) · `c.ai` (the framing instance) · `Fable` (the advisor) ·
`self` (I caught it, and *when* matters) · `source` (the literature).

`class`: `calibration` (I was confidently wrong about a fact) ·
`design` (the thing I built did not do what I built it for) ·
`process` (the discipline failed, not the mathematics).

## The anti-Goodhart clause, stated before the table

**This counter must never be a target, in either direction.** A rising count is
not virtue (it is easy to manufacture by predicting carelessly) and not vice
(a project that never surprises itself has stopped making predictions). The
number that carries information is the **denominator-relative rate** and, above
all, the **`corrected by` breakdown**:

* corrections arriving from **tooling** mean the instruments are ahead of the
  operator — the system working as designed;
* corrections arriving from **self, late** mean the instruments were behind and
  something got published in the interval;
* corrections arriving from **c.ai** mean the seam earned its cost that cycle.

If this file is ever cited as evidence of anything, cite the breakdown, not the
total.

## The table

| # | session | I expected | what happened | corrected by | class |
|---|---|---|---|---|---|
| S1 | 013 | the build ran; three theorems existed | `rc=0` came from an **unchanged tree**; the three theorems did not exist, and I had already filed them in `A.md` | tooling (`#print axioms`) | process |
| S2 | 024 | my `c`-table was sound | **unsound twice over** — scale mismatch *and* circularity; the alarm had been right both times | self, late | calibration |
| S3 | 026 | my published thresholds were merely hard to reach | Lemma 1 made them **RH-impossible**, i.e. vacuous | source | calibration |
| S4 | 027–028 | the fuel chain closes at `0.809` | the gate **fails**; `0.80869` retracted to Montgomery's `2/3` | self (shape check) | calibration |
| S5 | 029 | the census's `11/11` alignment supported E20 | blind re-classification gave **6/10 against chance 5/10**; E20's statistical support died | Fable (blind run) | calibration |
| S6 | 031 | T3(b) answer is **2** (sealed) | mechanical answer is **3**; the extra was `#27`, the entry I was most confident about | tooling (`provenance_lint`) | calibration |
| S7 | 031 | my first lint run's `5/11` was right | wrong — I had modelled `F_on_[0,1]` as RH-dependent; it is BGST's unconditional `𝓕`. Fixing the node gave 3 | self, same cycle | calibration |
| S8 | 032 | the blind trichotomy was clean | **three exposure channels** — my own schema-learning `grep` had rendered rows 1–2 with the plane column, and the compaction summary carried cause-language | self, pre-dispatch | process |
| S9 | 032 | my coupling axis would broadly agree with the prior reads | only `{4,7,8}` and `{6,10}` survived all three readers; every other pair was broken by someone | tooling (co-classification) | calibration |
| S10 | 033 | "useful iff non-`μ_T`-invariant" | **false** — an effective Fujii constant is μ-invariant and would move both rows. The specification is narrower than I wrote it | Fable | calibration |
| S11 | 033 | β-information is bought, never manufactured | β-*inequalities* are manufactured routinely (`on_line_of_H_eq_one`, `odd_Hr_inhabited`, `prop1`); only β-*identities* are not | Fable | calibration |
| S12 | 035 | `#5` (W4) was a kill | **container-local** — resurrected as CGdL 2018. Kill conditions do not travel | source | design |
| S13 | 036 | the two-height family forces the phase channel | it does **not**; no family built this way can, and whether phase is necessary is still open | self (by building it) | design |
| S14 | 036 | the swap family is a sharper test | it is a **symmetry** — agrees on every target count, so discriminating it is not a virtue | self (by building it) | design |
| S15 | 037 | the asymptotics would be crueller than the numerics, as in `#27` | **kinder** — the exponent promises `c<2`, the feasible crossover at `T=10^12` is `1.39` | tooling (crossover calc) | calibration |
| S16 | 038 | five string assertions would match the guard file | the fourth failed on whitespace; the guard was left untouched, which was luck of construction rather than design | tooling (assertion) | process |
| S17 | 032 | the env would be inherited by the tool run | `proportion.go` exited **4 with an empty body** — no `lake` on `PATH`; the audit worked, the operator did not | tooling (exit 4) | process |
| S18 | 036 | the boundary is β-*equality* vs β-*inequality* | wrong boundary — `on_line_of_H_eq_one` **is** a β-equality from ordinate data. The real boundary is **solitude**: computable on the simple locus, blind on crowded atoms | c.ai | calibration |
| S19 | 039 | rung 0 was **owned** — I relayed the ladder brief's claim that `{F on [0,1], F ≥ 0}` independence was already held | it is **prose, uncertified**; the only runnable capacity certificate (`ceiling_law256`) is imported from zeta-23, not ours | tooling (the audit's own criterion) | process |
| S20 | 040 | formalising the LP collapse would discharge the rung-0 debt | it discharges the **skeleton** — the class certified is a `Finset` program, the class `#10` names is an integral over `[0,1]`. By the audit's own criterion the rung is `partial` | self (the audit's criterion, applied to my own output) | process |
| S21 | 043 | `β ≤ 0` would be needed as a precondition for prop1's LP-optimality | **not needed** — the optimality holds for every `(α, β)` in the class, so the certified statement is strictly stronger than the docstring it replaces | tooling (the unused-variable linter) | calibration |
| S22 | 044 | the docstring disease would have more instances — at least one more Lean impossibility claim would turn out to be prose | **none did.** `c0_lower_bound` and `offline_le_tight` are real theorems; grade B is empty. The two remaining uncertified claims are grade **C** (class informal), a different species that formalisation cannot cure | tooling (the sweep) | calibration |
| S23 | 045 | promoting a grade-C claim would be a research question, not a formalisation task | W7's took **one cycle** — the cheap invariants all share one shape (`H γ ≤ M`), which *is* the class definition, and it needs no Euler product | self (by attempting it) | calibration |
| S24 | 046 | the last grade-C entry would either promote to A or stay C | **neither** — its class is well defined but its support is a *numerical optimisation*, so the grading scheme was missing a bin. Grade **N** added. And the optimisation's code is not in the repo at all | self (by attempting the promotion) | design |
| S25 | 047 | the unreproducible-number sweep would find more `#29`-class defects (missing code) | `#29` is the **only** one — every other computed figure traces to a Lean theorem, an exact closed form, a declared axiom, or a marked retraction. What it found instead was a **different species**: a retraction banner sitting *below* the numbers it retracts | self (by sweeping) | design |
| S26 | 052 | `(μ_T, offAt)` is the **exact** residue — "nothing else at all" (stated in SESSION 051 and LEADS) | it is **sufficient but not minimal**. `offAt_not_minimal`: the swap pair has the *same ledger* and *different* `offAt`, so some coarsening would also suffice and the minimal residue is unidentified | self (by asking the next question) | calibration |
| S27 | 054 | `#29`'s repair would need the source paper — the window computation was lost | **it was never lost.** The full specification (functional, `N = 160` midpoint, the linear solve `M v = a`) sits in `LEADS.md` three lines above the table. `forensics/window_opt.py` reproduces all seven digits. I searched for a *script*, found none, and filed the gap as external without checking for a *specification* | c.ai (its dispatch asked me to name the source, which made me look) | process |
| S28 | 057 | the loop was armed and would fire at ~10:46 (asserted in a closing line) | **it was not.** I never called `ScheduleWakeup` in that turn, so the loop died at 10:50 and ~4h passed with no cycles. The assertion was a green-light claim about live state with **no witness** — R17, applied to builds all night and not to my own scheduler | Joop ("check the time ;)") | process |
| S29 | 060 | the three-moment LP would price W35 cleanly — improve on `2 − C` or not | **neither.** It is *unbounded*: claude.ai's family (verified exactly) certifies `7/4` of the zeros simple at `C = 3/2`, which is impossible. The defect is the input region — `C₃ ≥ C²` is necessary and far from sufficient over integer masses — so the question was not well-posed | self (by running it) | design |
| S30 | 071 | the `/6` census bound and the third-moment obstruction are two readings of one polynomial, and the shared `6` is not a coincidence | **both wrong.** `six_mul_card_le_Nstar_sub_N` runs on `sum m(m-1)`, the obstruction on `sum m(m-1)(m-2)`; they agree at `m = 3` and nowhere else (`2` vs `0` at `m = 2`, `12` vs `24` at `m = 4`). The shared `6` is exactly the coincidence I declared it not to be. What survives: both activate at `m = 3`, so the *threshold* is shared, not the polynomial | self (re-reading the register two cycles later) | calibration |
| S31 | 075 | a failure mode, once filed, stops recurring — the env-export omission before `proportion.go` was recorded after the last compaction and I expected the record to do the work | it recurred this cycle, one command after I had exported the same variables in the previous block. Shell state does not persist between tool calls and the register does not run the command for me. Self-caught in seconds because the escalation message is loud (`a claimed name does not exist` — a *misleading* message, since nothing was missing), so the cost was one re-run | self (immediate) | process |
| S32 | 076 | the overclaim gate's defect would be **over**-flagging — that triage would find false positives and the fix would be narrower wordlists | the more serious defect was **under**-flagging: the converse-witness pattern `Namespace.name` also matches `FAILURES.md`, `LEADS.md`, `S.md`, `Gauge.lean`, so three of the four *passing* sentences on CLAIMS.md passed on a filename alone. A guard against unwitnessed claims had been exempting any sentence that mentioned a file. And the two fixes are `−6` and `+6` on the corpus, so the headline count would have shown nothing | self (hand-triage of all seven flags, which the flag count alone would never have prompted) | calibration |
| S33 | 078 | the heartbeat prompt's queue is a reliable list of open work | three of its five items were already discharged — W32 has been run and its table sits in `FAILURES.md` (kill condition recorded, tally M=2/S=1/neither=8), and the minimality question it forbids claiming was settled in both directions two cycles earlier. The prompt is a fixed text fired by cron; it ages while the disk moves. Checking the register before starting cost one `grep` and saved a duplicated cycle | self (S27's discipline — check the registers before reconstructing — applied to the queue itself rather than to a computation) | process |
| S34 | 084 | the `Nsc` row was **honestly** zero — I had read `certified_nsc`'s docstring many times and accepted its reasoning: no unconditional `(★)` exists, so neither Prop 1 nor the `(C−1)/2` baseline route can be evaluated | both premises are true and the conclusion did not follow. The docstring **enumerated the routes and the enumeration was not exhaustive** — it assumed every bridge from `NscStd` to `Nsc` passes through `(★)`. One does not: `3·NscStd ≤ N + 2·Nsc` is axiom-free, because a haunted atom's off-line part is even and nonzero so its mass is `≥ 3`. The row is **50.875%**, at the same two axioms the `NscStd` row already consumed | self (asking what seven cycles of blindness theorems bought the *ledger*, which is the question I had not asked) | calibration |
| S35 | 086 | the gate on Lean docstrings would find nothing — the registers are where prose defects live, and code comments are written closer to the mathematics | it found `Program.lean`'s *"this is the only arrow that survives"*, contradicted as written by the next two theorems in the same file. The intended scope ("with no hypothesis beyond `DensityNearLine`") was true and unstated. 1 true positive in 14 on the load-bearing files — a low rate that nonetheless caught the exact defect class the sweep was hunting | self (running an existing instrument on a surface it had never been pointed at, which `S34` is what suggested) | process |
| S36 | 089 | `S26` was discharged — I retracted the "exact residue" claim one cycle after making it and thought that closed it | the retraction was filed at `offAt_not_minimal`, 150 lines below the two docstrings that make the claim, and **both stale superlatives were still standing twelve cycles later**. I had been reading past them the whole time, including while writing five theorems in the same file. A retraction that is not at the location of the stale text is not a retraction, it is a second opinion filed elsewhere | self (triaging the gate's flags on my own prose, which I had deferred four times as "my writing, low yield") | calibration |
| S37 | 095 | the gate catches overclaims, so a sentence that survives it is safe | `094`'s might-mean — *"every positive proportion theorem is structurally incapable"* — sailed through the gate and was still **one quantifier wider than the theorem under it**, which fixed the proportion at `3/4` and says nothing about a hypothesis at `99%`. The gate reads wordlists, not quantifiers, and there is no instrument in the project that compares a sentence's scope to its witness's scope | self (re-reading the previous cycle's own summary, not any guard) | calibration |
| S38 | 112 | having logged `S37` about quantifier drift, I would not commit it again — least of all in a cycle whose subject was converting an assertion into a theorem | `111` proved a `ZeroData` witness and concluded a `Family`-level cap. Two cycles after `S37`, in the cycle *about* this exact failure. The gate does not read quantifiers, and neither, apparently, do I when the sentence sounds like the theorem. What caught it was re-reading the previous cycle's own summary before starting — the same thing that caught `S37` | self (re-reading, again; no instrument) | calibration |
| S39 | 113 | the S37/S38 defect has a mechanical signature — universal prose citing an existential theorem — so it is lintable | **0 of 2 on calibration.** Both offending sentences drift by *dropping the citation*: they generalise away from the theorem and stop naming it. The signature I designed for is the one shape the defect never has, and I only saw it after building the gate and testing it. The single live flag was a false positive (an attainment claim, correctly called "attained") | self (running the calibration I had committed to run first) | process |
| S40 | 142 | the ledger tool's `ESCALATION: a claimed name does not exist` meant what it said, and `audit/Declarations.lean` had broken | **the audit never ran.** `lake` was not on `PATH` — my own omission — and the branch reported the *verdict* of a check it had been unable to perform, on every failure mode indiscriminately. I spent the opening of the cycle reading a 250-line declaration list hunting a defect that did not exist. An instrument that cannot distinguish "the check failed" from "the check ran and found something" manufactures false bad news, and R17's "no witness, no belief" had only ever been applied to good news. **`S17` is this same event, 110 sessions earlier** — same `PATH`, same exit 4, same empty body — filed `process` ("the audit worked, the operator did not"), which located the fault in me and left the tool untouched, so it recurred verbatim. Classing an instrument's misreport as operator error is how a fixable defect buys immunity | self (the audit file compiling cleanly under `lake env lean` while the tool insisted it did not — two instruments disagreeing, which is the only reason I looked) | design |
| S41 | 142 | the `Nsc 0.00%` staleness lived in the four documents I had already listed by grep | the sweep found a **fifth**: `VERIFYING.md` §5, the field-by-field *instruction* for reading a ledger line, teaching off a line whose `Nsc` figure had expired 58 sessions earlier. The four I found by searching for the number; the fifth I found by searching for the *role*. A stale figure inside a worked example is worse than a stale figure in a claim, because the reader is being taught to trust the format | self (running the wildcard sweep instead of stopping at the grep hits, which is the only reason the kill condition had anything to fail against) | process |
| S42 | 143 | `∫S²/L` would reproduce the variance `140`/`141` measured, since both are "the second moment of `S`" | **they differ by a factor of 3.2** — `0.17916` against `0.05644`. `140`/`141` sampled `S` at gap MIDPOINTS; a moment theorem integrates. The gap is the sawtooth's own contribution `E[d³]/12 ≈ 0.126`, deterministic spacing geometry with no Selberg content, verified to `3%`. I had been treating "the variance of `S`" as one quantity for three cycles, and the one Fujii's moments are about is the one I had not computed | self (by needing the other functional for a different purpose, not by re-reading — the discrepancy appeared as a 31% miss on a pre-registered prediction) | calibration |
| S43 | 143 | if the deterministic and fluctuating parts of `∫S²` were comparable at this height, that would be a fact about this height | **the sawtooth term never becomes negligible.** It is height-independent at `0.126`; Selberg's term reaches only `0.215` at `T = 10³⁰`. At `T = 7.5×10⁴` the two agree to `0.2%` — a coincidence sitting exactly where the data is, so anyone checking `∫S²/L ≈ log log T/2π²` on Odlyzko's table gets confirmation of a formula that accounts for half the quantity | self (by tabulating the two terms against height instead of quoting the one number) | calibration |
| S44 | 144 | the want-ad `143` wrote (an S-moment identity with error `o(T)`) would turn out not to exist, since the register's habit is that the needed object is missing | **it exists and is 39 years old** — Goldston 1987, displayed as (1.8) in arXiv:2006.08503, error exactly `o(T)`. The route dies anyway, for a reason I had not considered: it is conditional on RH, and RH forces `hauntedCount = 0` via a theorem already in this repo (`Fiber.noHaunted_of_Noff_zero`). I had priced the *precision* of the supply and never asked what its *hypothesis* does to the target | source (the displayed formulas; the fetch `143` committed to making) | calibration |
| S45 | 145 | `S44` was a fresh miss — the RH-empties-the-target trap had not been seen before | **`LEADS.md` line 1787 states it outright** — "haunting only exists in the *unconditional* world. Under RH it is vacuous" — written by c.ai and sitting on disk while `143` wrote a want-ad and `144` spent a fetch confirming it. And `S3` (session **026**) is the same genus: a hypothesis emptying the point of the exercise. Rules 1–3 of `provenance_lint` ask CIRCULAR / SCALE / QUALITY and none of them asks whether an input's own hypothesis trivialises its target, so an input can pass all three and still be worthless | self (looking for a rule to add, and finding the fact already written) | process |
| S46 | 145 | "the pre-existing output is byte-identical" — I wrote it into the session entry as a witness for the guard change being safe | **it is not.** Every pre-existing *verdict* is identical, but `lint()`'s header line now prints the target, so the text differs on three lines. I asserted the strongest available form of the check without running it, in the same entry whose subject is a rule that exists because inputs get trusted unexamined. Running the diff took one command | self (R17 applied to my own sentence — "no witness, no belief", including about a diff I had not taken) | process |

## Standing observation

**Not one entry on this table was found by re-reading my own prose.** Every
correction came from an instrument, another instance, a source, or from
*building the thing and watching it fail* — never from thinking harder about a
claim I had already written down. That is the argument for the whole apparatus
in one line, and it is also why `S13` and `S14` are the most valuable rows:
they are the two cases where the correction cost nothing but the construction.


## Correlated misses — the quantity `FRAMING`'s seam claim actually lives on

claude.ai's audit of `SESSION 069` makes a distinction the measurement lacked:

> **Proposal convergence is not the failure mode the seam exists to prevent.**
> Two instances handed identical inputs and converging on the obviously-right
> next move is **replication**, which is a confirmation signal, not a dead
> check. The seam's claim was never *"we will propose different things"* — it is
> ***"we will not miss the same things."***

**So the killer quantity is correlated error: claims both instances endorsed,
caught only by a third party.** On that metric the record is worse than
`SESSION 069`'s table, and the two entries were already on file:

| # | the shared miss | why correlated | who actually caught it |
|---|---|---|---|
| **S5** | E20's `11/11` alignment supported the plane | claude.ai supplied the plane framing; I classified with the hypothesis in hand — **shared priming** | **Fable**, blind, no hypothesis |
| **S6** | T3(b)'s answer is `2` | I disclosed the sealed predictions (`S8`); claude.ai endorsed after reading them — **anchoring on disclosure** | **`provenance_lint`**, mechanical |

**Correlated misses: 2. Rescued by the seam: 0.** Both were caught by
*mechanical or blind* third parties. `SESSION 069` counted the flows that
happened rather than the stops that did not, and undercounted the problem.

### Protocol, pre-registered from here

Every new entry gains two fields:

* **endorsed-by** — `VPS` / `c.ai` / **`both`** / `neither-saw-it`
* **caught-by class** — `kernel` / `tooling` / `blind` / `human` / `source` /
  `self`

**Kill condition, stated first:** *if after twenty more entries the `both` rate
exceeds the single-instance rate — if the two instances miss together more often
than alone — the seam is negative-value as a check, its budget reallocates to
more heterogeneous layers (a third model family, more blind passes, more
mechanical gates), and `FRAMING.md` records that the design's founding intuition
was wrong.*

If the `both` rate stays low while proposal-convergence stays high, the seam is
what the `depthPair`/`pairOnly` coincidence suggests: **a replication engine
with a weak-but-real checking side-effect** — worth keeping, priced honestly.

**Historical backfill is partial and marked as such.** For most entries the
question does not arise: claude.ai never saw the claim, so `endorsed-by` is
`VPS` and the entry is silent on the seam. The two above are the determinable
`both` cases. No historical rate is quoted.
