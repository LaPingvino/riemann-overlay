# METHOD — how this project is run

This file documents the *process*, so that an outside reader can tell what kind
of object each claim in this repository is, and reproduce the discipline that
produced it. The mathematics is in `Riemann/*.lean`; the record is in the
markdown registers; the rules are in `LOOP.md`, and this file summarises them
without replacing them. **Where this file and `LOOP.md` disagree, `LOOP.md`
wins** — it is the primary document and it is append-heavy by design.

For *reproduction instructions* (build, audit, guards, how to check the
headline claims) see `VERIFYING.md`.

---

## 1. What kind of project this is

A Lean 4 + Mathlib formalization of the **reduction structure** of a program
for pushing the proportion of zeta zeros known to be simple and on the critical
line. It is deliberately *not* a proof about `ζ`. The deliverable is the
**labeled interface map**: which piece of information composes with which
other piece, at what cost, machine-checked.

The project is run as a standing autonomous **loop**: one cycle = one session,
each session appended to `SESSION.md` under a number (currently 001–033).
Registers are markdown files that accumulate rather than get rewritten.

| register | what it holds |
|---|---|
| `LOOP.md` | the rules (R1–R19), the cycle, the escalation list, the cadence doctrine |
| `SESSION.md` | numbered, append-only session log |
| `ISSUES.md` | the friction — disputes, seams, open governance items |
| `LEADS.md` | the hold queue: W-items (wildcards) |
| `E.md` | E-items — the definitional/exhibit register |
| `A.md`, `S.md` | architecture notes; `S` is the "witness for silence" doctrine |
| `PRICES.md` | exchange rates: what a given piece of literature buys in container currency |
| `FAILURES.md` | the failure census — every death with its *certified reason* |
| `STATEMENTS.md` | the translation layer between prose statements and Lean statements |
| `NIGHT.md` | the overnight-mode digest |
| `PROPORTION.log` | the append-only ledger line, one per cycle |
| `FRAMING.md` | the companion document from the other side of the seam — the origin and architecture of the collaboration, with a verification appendix auditing its own claims |

---

## 2. The cycle

`LOOP.md` calls it the Tetris doctrine. One cycle:

1. **Next-piece preview** — arXiv/listing scan for the active suppliers.
2. **Surface scan** — re-read `ISSUES.md` and the interface list; prefer work
   that *flattens* (interface fixes, scale and quantifier audits, statement
   verification) over work that builds height.
3. **Place pieces** — the main work, chosen by the metric's
   *binding-constraint* field (the ledger line names the single lemma or axiom
   currently capping the number).
4. **Collision report** — `lake build`, `go run tools/proportion.go -append`,
   the three-column testbed on anything new.
5. **Score and log** — `PROPORTION.log`, `SESSION.md`, promotions/retirements.
6. **Escalation check**, then next cycle.

### Per-cycle obligations

* **One piece + one wildcard.** The entropy budget in `LOOP.md`'s Hygiene
  section makes *one deliberate wildcard per loop* (a `LEADS.md` W-item, a
  weird-paper skim, a "what if" numeric) **mandated, not tolerated**.
* **Kill condition stated first.** R12: *"Every wildcard ships with a kill
  condition, stated before it runs — and a kill condition kills the hypothesis
  in the container you checked, not in the world."* W4 was killed against the
  zeta-23 container and later turned out to be a published theorem (CGdL 2018)
  in a wider certificate class; the rule's second clause is that scar.
* **Register annotations.** When a theorem lands, the E-items, W-items and
  ISSUES entries it touches are annotated in place — the registers carry the
  outcome, not just the intention.
* **One numbered `SESSION.md` entry** per cycle, append-only. A **re-mining
  pass** over old sessions is scheduled every ~5 sessions, "scheduled, not
  accidental".
* **One unhedged "might-mean" sentence** per dispatch. `LOOP.md`'s might-mean
  register exists because findings that *kill* something arrive with more
  precision than findings that *open* something (deaths have a verifiable
  terminal state, openings do not), so the record skews toward "this project
  closes doors". The remedy: exactly one unhedged sentence about what a finding
  might mean, **marked as such and not treated as a claim by either side**.

### Cadence doctrine (2026-08-14)

Dispatches follow **cycle output, not conversation rhythm**. The seam runs hot
when there is something to check or aim and goes silent without apology while
the loop grinds. `LOOP.md` records the bookkeeping nuance: framings choose which
cycles run, so the seam's output is the *derivative*, not the function —
and derivatives matter at turning points and are noise on straightaways.

---

## 3. The rules (R1–R19)

Quoted by number as they appear in `LOOP.md`. Note that the table there is
**not in numeric order** — R16 is inserted between R9 and R10, because the rules
are listed in the order they were paid for. Numbering is preserved here as
written.

**R1–R7 — the original doctrine.**

| | rule |
|---|---|
| R1 | Keep the surface flat — interface hygiene outranks new construction |
| R2 | Never build towers on holes — no route work above an unresolved bin-3 item in its own cone |
| R3 | Use the hold queue — `LEADS.md` is the held piece; swap in when stalled, swap out without shame |
| R4 | Clear singles — small certified gains beat hoarding. **Exception: never weaken a statement to clear a line** |
| R5 | Garbage rows are axioms — every line of `Assumptions.lean` raises the stack without being clearable; the axiom count *is* the garbage height |
| R6 | The well speeds up — log the difficulty gradient honestly |
| R7 | Watch for the piece already on the board — standing query: *"which of our open problems is secretly a theorem in something we already cite?"* |

**R8–R16 — learned in practice, each citing the incident that taught it.**

| | rule |
|---|---|
| R8 | Try to make a dispute into a formal object before adjudicating it — a governance question that survives one cycle is usually a missing lemma |
| R9 | At every interface, ask which end binds. Record **at which parameter values** a numerical check passes, never just that it passed |
| R16 | When a bound is proved termwise over zeros, redo it grouped over atoms before believing its constant. Both constant improvements this project has made (`1 → 2`, `2 → 6`) were exactly this regrouping |
| R10 | Charge the maximum the structure entitles you to |
| R11 | A gate is a wildcard target, not a wall — fetch the primary source *and* re-derive independently, then hand over the two-line diff |
| R12 | Every wildcard ships with a kill condition, stated before it runs; a kill is **container-local** |
| R13 | Classify by constants before reading proofs |
| R14 | When stuck, stop proving and try defining — the kernel accepts definitions too |
| R15 | When in doubt and no human is awake, consult the Fable advisor — for judgment calls, never to authorise anything the escalation list reserves for the human |

**R17 — no witness, no belief.**

> Any claim of the form *"there is no…"* and any green light of the form *"no
> errors"* gets one question: **what positive object witnesses this silence?**
> Absence is certified only by exhibiting something conserved — a fingerprint, a
> parity, a positivity, an invariant.

This is the generalisation of every instrument in `forensics/` and of the
guard exits in `tools/proportion.go`: "the base derives no falsehood" is an
absence claim, so it is given a positive witness (the regression files, which
must fail to compile). See `S.md`.

**R18 — two conditions on every numerical input.**

> (1) **Scale:** valid at the scales the window actually uses, not
> asymptotically in the averaging length. (2) **Independence:** not derivable
> from `{F on [0,1], F ≥ 0}` + positivity — checkable by asking whether the
> input's *proof* consumes anything past bandwidth one beyond trivial
> nonnegativity. If not, LP duality returns the class optimum and the table is
> decoration.

`LOOP.md` records this cost "four costumes of the scale disease; the fourth cost
a published threshold".

**R19 — no pattern-claim about our own corpus without a blind classification.**

> Strip hypothesis-language, hand the corpus to an agent given no hypothesis,
> demand its **own** categories, score against a mapping registered *before* the
> run. Applies to failures, residues, E-annotations, and any future atom tests.
> Without it the corpus returns whatever pattern was brought to it.

R19 was written after it fired against the project itself: `FAILURES.md`
records an apparent `11/11` alignment, then the de-contamination protocol
(pre-registered rule → blind classification → only then score), then the T2 run,
in which a blind classifier produced a *different* dichotomy and agreement fell
to **6/10 against a chance baseline of 5/10**. The verdict recorded in
`FAILURES.md` is that the census does **not** independently support the
hypothesis and **no p-value should be quoted**. The header of that table also
carries a standing contamination note telling the reader not to use the `plane`
column as evidence.

---

## 4. The two-row ledger

The single most important convention. `tools/metric.json` defines two rows, and
`tools/proportion.go` scores each **independently**:

* **`NscStd`** — *the literature's notion*: zeros that are simple and on the
  critical line in the usual sense (multiplicity one, on the line — zeta-23's
  `N0simple`).
* **`Nsc`** — *this project's stronger notion*: `H = 1`, i.e. the ordinate
  carries nothing else at all.

They are linked by `ZeroData.two_NscStd_le` at a cost of `(C−1)/2`, so **the gap
between the rows is a certified function of `C`** and closes exactly when the
program's `(★)` succeeds.

**"Two numbers, always together."** Every ledger line carries both the
certified figure and the conjectural one, and the certified figure is itself
split across the two rows. The line reads
`certified[NscStd: 67.25%, Nsc: 50.88%]` and `conjectural: 100.00% (OPEN D)`.

### The empty-row principle

> ⚠️ **SESSION 084 — this section's example expired.** The `Nsc` row is
> **50.88%**, not `0.00%`. It opened *without* an unconditional `(★)`, via
> `3·NscStd ≤ N + 2·Nsc`, so the "why it is empty" reading below no longer
> describes any row of the ledger. The principle is kept on its merits.

`LOOP.md`:

> A row of the ledger that is honestly zero is more useful than a row that is
> quietly redefined until it is non-zero.

`Nsc` *read* `0.00%` because no unconditional `(★)` exists at any constant. Its
`binding` field says why and what would open it. Two instruments with a
crossover at `C = 1.655`, not a score with a caveat.

### The anti-Goodhart rule

The score is a fitness function that an autonomous loop optimises, so the
obvious failure mode is optimising the measurement. Three structural defences:

1. **R4's exception — "never weaken a statement to clear a line."** Weakening a
   statement to move the number is *deleting rows*, not clearing them.
2. **R5 — axioms are garbage rows.** They raise the stack without being
   clearable, and the axiom count is printed in every ledger line, so "a loop
   that only adds garbage is losing while the score rises" is visible.
3. **The escalation list** reserves for the human: any candidate line clear
   touching the certified number (a human verifies *before* the log line is
   written), and — explicitly — **a difficulty gradient that inverts**, because
   "things getting easier usually means a statement got silently weakened.
   Audit before celebrating."

Overnight mode adds a hard list of things that are **never** done unsupervised:
restating an axiom, weakening a statement, changing what the certified number
*means*, or writing a `PROPORTION.log` line that moves a row.

---

## 5. Sorry-poisoning and the axiom audit

A `sorry` anywhere in a proof's cone makes the proof worthless, and Lean records
this as a dependency on the axiom `sorryAx`. The project therefore never trusts
a green `lake build`:

* `audit/PrintAxioms.lean` runs `#print axioms` on the headline declarations.
* `tools/proportion.go` parses that output and treats the three standard Lean
  axioms — `propext`, `Classical.choice`, `Quot.sound` — as free. Everything
  else is listed **by name** in the ledger line.
* Any row whose audited axiom set contains `sorryAx` **contributes 0** and
  prints a warning. A row whose Lean name is absent from the audit entirely is
  likewise treated as unproved and scored 0.
* Separately, the source tree is scanned for literal `sorry` tokens with
  comments and docstrings stripped first, so prose *about* `sorry` is not
  counted; the total is printed as the `sorries:` field.

**The trusted base is exactly `Riemann/Assumptions.lean`, and nowhere else.**
Every axiom is declared there with its source cited in the docstring.

### Base-meaning versioning (R15's enforcement mechanism)

Meaning-changes are invisible to metrics, so `PROPORTION.log` lines carry
`base: vN/<hash>`:

* **N increments on any change to what the trusted base MEANS**, independent of
  the axiom count. The test: *would this change what a reader should believe
  when they see "axiom-clean"?*
* **The content hash** fingerprints the *normalised statements* of every axiom
  in `Assumptions.lean` (comments stripped, whitespace collapsed, sorted by
  name). A degradation that reuses an existing axiom's name moves neither the
  count nor the names — but moves the hash. If the hash moves and
  `base.version` did not, the tool prints `ESCALATION`, **refuses to write the
  log line**, and exits `3`. Verified end-to-end by editing a constant in place.
* The `context:` field records the *operator's* epistemic state (e.g. a context
  compaction), not the repo's, so that a shift in error profile is findable.

Recorded history: `v1 → v2` (2026-08-14), when `axiom zetaFamily : Family`
became a `def` plus `axiom zetaNonempty` — count unchanged, base strictly
weaker. `LOOP.md` states the governing principle: *improvements to the trusted
base are precisely where vigilance relaxes, so they get more ceremony than
degradations, not less.*

---

## 6. The guards, and what each one detects

Four mechanical guards. Three of them exit `tools/proportion.go` non-zero and
block the ledger line; two are Python instruments run before any table is built.

| guard | where | detects | on failure |
|---|---|---|---|
| **Declaration existence** | `audit/Declarations.lean`, run by `proportion.go` | a register claims something about a name that does not exist. "A green build proves nothing about a declaration never written" (ISSUES #17) — session 013 filed a register entry for three theorems that did not exist | `ESCALATION`, exit **4**, no log line. Verified by appending a fictional name |
| **Regression must fail** | `audit/regression/*.lean`, run by `proportion.go` | the trusted base has become inconsistent again (ISSUES #8). `Boom_2026-08-13.lean` derived `False` from an earlier axiom set. The guard runs each file and escalates **if one compiles** | `ESCALATION`, exit **5** |
| **Base-hash drift** | `baseHash` in `proportion.go` | an axiom statement changed without a `base.version` bump | `ESCALATION`, exit **3**, no log line |
| **Contamination lint** | `forensics/provenance_lint.py` | builds the provenance DAG of every input and flags three ways an input can be unusable: **CIRCULAR** (ancestry hits the target, its dual, or the certificate class's own optimum), **SCALE** (consumed outside its validity range), **QUALITY** (supplier weaker than consumer requires). Replays the project's three expensive failures and blocks all three at proposal time. Also marks RH-conditional nodes and propagates the flag | report printed above any table |
| **Lemma 1 guard** | `forensics/lemma1_guard.py` | any candidate form-factor model `D` past support 1 must satisfy Goldston's Lemma 1, `∫_B^{B+1} F ≤ 3` under RH, uniformly in `B ≥ 1`. Retroactively it kills every `c ≥ 4` row this project published | prints `VIOLATES RH (Lemma 1)` |

**Guards versus experiments.** `forensics/` also contains `quarry.py`, which is
*not* a guard: it re-runs the project's retracted computations as experiments,
importing `provenance_lint` and evaluating its rules **without editing the
guard's DAG** — a constraint stated in its own header, with any surviving node
recorded as a *proposed* addition to be applied after the freeze lifts. Only
`lemma1_guard.py` and `provenance_lint.py` are guards; nothing `quarry.py`
prints is certified.

The regression and declaration guards are the direct implementation of R17: the
absence claims "the base derives no falsehood" and "every claimed name exists"
each get a positive, mechanical witness instead of a human remembering.

Operational rules also recorded as scar tissue in `LOOP.md`: never pipe a long
build through `grep`/`tail` in the same command (they buffer, so a crash becomes
silence); one `lake` at a time per package; detached processes do not survive.

---

## 7. Blind reads and sealed files

`forensics/` holds work produced **before** the answer was known, sealed by
content hash so that the seal can be checked afterwards. The convention is

```bash
sha256sum <file> | cut -c1-16
```

and the resulting 16 hex characters are quoted in the register entry that
announces the sealed prediction. Because the hash is registered before the
comparison runs, an unfavourable result cannot be edited away — and `FAILURES.md`
records an instance where exactly this bit: *"The blind was partial and the
sealed file overstates it (audited before dispatch, file not edited — the hash
outranks the wording)."*

The same entry names the general lesson honestly: three exposure channels leaked
(a schema-learning `grep`, a compaction summary, the dispatch text), so the
genuinely blind subset was smaller than claimed, and **"orientation is an
exposure channel."**

`VERIFYING.md` §6 lists the seals currently documented in the registers, with
the commands to recheck them.

---

## 8. Escalation

Exit the loop and ping the human on: any bin-3 item surviving two sessions; any
candidate line clear touching the certified number; any AH-oracle jackpot flag
(immediately, mid-session); a gate that resists conversion under R11; a
**difficulty gradient inverting**; anything warranting outside eyes (drafting is
in scope, sending is not).

In **overnight mode** escalation does not mean stop — it means *park and
continue*: the finding is written up in full (ISSUES entry, the exact question,
the recommended answer), nothing requiring a ruling is applied, and the cycle
moves to the next queue item.

---

## 9. The architecture, in one line

`LOOP.md`'s own summary, kept here because it is the shortest accurate
description of why the process looks like this:

> Nobody in this system is closer to the truth than anyone else; we differ only
> in how fast our respective *no* arrives. The build loop's in a minute, the web
> half's at search speed, Joop's at a glance, the kernel's instantly, the
> literature's in fifty years. **The project is the practice of routing every
> claim to the fastest available no.**


## Impossibility results as search-space pruning (SESSION 115)

A new function for the blindness theorems, and the first instance is recorded in
`Fiber.haunted_indistinguishable_from_triple`.

`105` asked whether its pattern-exclusion hypothesis — "no ordinate carries
exactly one critical zero and one off-line pair" — is recognisable from the
zero-repulsion or pair-correlation literature. The answer is **provably no, and
without reading the corpus**: a haunted mass-`3` ordinate and an on-line triple
zero are the same `μ_T` atom, so any `μ_T`-invariant statement excludes both or
neither, and no known repulsion result excludes triple zeros. Repulsion governs
the spacing of *distinct* ordinates; exact coincidence is precisely the
gauge-invisible direction.

**So an impossibility theorem can retire a reading task.** "We searched and found
nothing" is weak evidence; "the corpus cannot contain it, here is the theorem" is
a result. Where a class-impossibility exists, check it against the reading queue
before reading — it may empty entries.

*Caveat, stated: this prunes only corpora whose statements are invariant in the
relevant sense. It says nothing about literature that reads the objects the class
cannot.*


## Reading a passing guard (SESSION 126)

Two guards print alarms while passing, and both are correct:

* `provenance_lint` ends `=> BLOCKED — do not build the table`. That is its
  verdict on `GM_bridge`, whose consumer needs a power saving and whose supplier
  gives log-power — the `ISSUES #27` death, recorded and closed. A clean run
  **says BLOCKED**.
* `lemma1_guard` prints `VIOLATES RH (Lemma 1)` at `D = 4`. That is the guard
  exercising its own discriminating power on a synthetic constant, not a
  statement about `ζ`.

Exit code is the verdict; the prose is the reasoning. Read the exit code first.


## Two small disciplines, both bought by slips (SESSION 128)

**Assert before replacing.** A `str.replace` that does not match is a silent
no-op. `127` shipped a commit message saying "gate-clean" because a downgrade
edit missed a line-wrapped sentence and the substitution quietly did nothing.
Every scripted edit to a register or source file asserts the old text is present
first; the assert is the witness that the edit had a target.

**When correcting a stale claim, grep for the sentence, not the file.** `128`
found one stale claim living in *two* registers in different wordings. A sweep
scoped to a file finds one copy and stops. Search the phrase across all
registers before writing the correction.


## Expire staleness, do not detect it (SESSION 132, claude.ai's design — FILED, NOT BUILT)

Two instruments for stale text failed calibration (`113`, `120`). claude.ai's
diagnosis: **staleness is cache invalidation**, and judgment-based detectors fail
because staleness has no local signature — the text that is stale looks exactly
like the text that is current.

The mechanical alternative is **expiry, not detection**:

* every `CLAIMS` / `ISSUES` / `LEADS` entry gains a `valid-as-of: <commit>` field
  at write time;
* a trivial script flags any entry whose **cited files changed** since that
  commit.

No judgment, no calibration — dependency-triggered re-grade flags. Entries confess
their own age, so pessimism never needs patrolling. The failure mode is
over-flagging after a large refactor, which is a nuisance rather than a silence,
and that asymmetry is the whole argument.

**Status: filed, not built.** Retrofitting the field to existing entries is the
bulk of the work and it is not this cycle's. Recorded here so the design is not
re-derived, and because `113`/`120` earned the rule that an instrument gets
written down before it gets written.


## Expiry tested and rejected; the absence queue instead (SESSION 133)

`132` filed claude.ai's expiry design (`valid-as-of: <commit>`, flag when cited
deps change). **Tested against the four stale claims this project has actually
found — it catches none of them.**

| stale claim | invalidated by | cited deps changed? |
|---|---|---|
| "code not in repo" | `window_opt.py` was **created** | no — cited nothing |
| "unreachable from our root" | an **import** was added; the declaration never moved | **no** |
| "only capacity certificate came in with zeta-23" | `Capacity.lean` was **created** | no |
| "profile minimality is not proved" | two theorems were **proved** | no |

All four were invalidated by something being **added**. Expiry asks "did my
source move?"; the defect is "does something now exist that I do not cite?".
Filed before building, which is what `113` and `120` cost a cycle each to learn.

**`forensics/absence_queue.py`** instead: list every claim of *absence*, because
each is a standing obligation to re-check. It makes no judgment about staleness —
it cannot — it only ensures no such claim is invisible. Calibration **4/4** on the
above. Exit is always `0`: a work queue, not an alarm.

Its own first run taught it one thing: corrections in this project are written
*below* the text they correct, so the **following paragraph** counts as the
settlement. Without that, it re-flagged the two claims `127` and `128` had already
annotated.

## The plain-words rule (SESSION 133, Joop and claude.ai — ADOPTED)

Our dispatches are written in the literature's dialect — *form factor*,
*mollifier*, *ordinate*, *certificate class*. That dialect addresses the
RH-primed region of any model reading it, and per `E20` the grooves are where the
blind spots live: the vocabulary is inherited from the tradition whose limits we
keep certifying.

**Effective now:** every dispatch's key questions carry a plain-words
restatement; foreign-model seeds are plain words **only**; and when a problem is
stuck, re-asking it in kitchen language is a legitimate move costing one
sentence.

Precedent from our own record — *"one voice per pitch"*, *"the primes keep the
ledger"*, *"nobody shares"*. The `E`-file's plain phrasings repeatedly preceded
the theorems; the register was doing this before it was named.


## The data phase's review rule (SESSIONS 134, 139, 140 — three instances)

Three times in seven cycles a data computation produced a confident wrong number,
and **not once did a guard catch it**:

| cycle | slip | what caught it |
|---|---|---|
| `134` | two points at infinity where an odd-degree model has one | a hand-check of one curve |
| `139` | `base + offset` in float64 destroyed a `10²⁰` table | `mean δ = 0.000000` |
| `140` | Selberg's variance constant off by `π²` | variance `0.048` against a **pre-registered** `≈ 1` |

**The rule, earned:** every data computation must carry a quantity whose correct
value is known *before* the run — a normalisation that must come out `1`, a count
that must match an index, a prediction registered in advance. That quantity is
the whole of the review, because the build is green either way and no linter
reads arithmetic.

And **the kill condition must name which side it blames first.** `140`'s said
*"either the normalisation is misapplied or the counting function is wrong — and
the counting function is checked first."* It fired, the counting check passed,
and the remaining branch was the answer. A kill condition that only says
"something is wrong" would have cost a cycle of searching.

## `431` — the pre-flight query

Before writing a proof, run

```
python3 forensics/preflight.py '<the statement you are about to prove>'
```

It ranks the tree's declarations by conclusion **shape** and identifier overlap.
Its three calibration cases are the arc's three rediscoveries — `412`'s
`Riemann.starBound_of_mult_le`, `416`'s `Blindness.add_ordinates`, `430`'s
`Blindness.Nsc_eq_sum_mass_one_nat` — and it fails loudly if any stops
surfacing. A high score is a prompt to read, not a verdict. **`432`: prospective only** —
run backwards it flags `62` pairs that are the project's own habit of stating a
family at several constants.

## `443` — drill a new instrument before trusting it

`forensics/session_gate.py` judges a guard by its exit code and never reads its
output, so an instrument that prints findings and returns `0` reads as green.
A new instrument is therefore assumed to have that gap until someone injects a
fault and watches it fail. The four built at `420`–`431` were drilled at `442`
and `443`: `farkas`, `preflight` and `tightness` returned `5` on a corrupted
calibration or a falsified inequality; `register_citations` named the defect and
returned `0`, which is why it now has `--gate`.
