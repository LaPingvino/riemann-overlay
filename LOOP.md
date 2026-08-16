# LOOP — the Tetris doctrine

> ## ⚠️ READ FIRST — the cron prompt's STATE line is stale
>
> The heartbeat prompt is a fixed text fired by cron; it ages while the disk
> moves (`SURPRISES` S33). As of `SESSION 102` it is wrong in three ways, and
> **the disk is authoritative**:
>
> | the prompt says | the truth, with its witness |
> |---|---|
> | `ledger Nsc 0.00%` | **`Nsc 50.88%`** — `certified_nsc_unconditional`, `SESSION 084`. Run `go run tools/proportion.go` and believe that. |
> | `binding constraint = Fujii's implied constant` | binding is `baseline_zeta23`; Fujii binds nothing since the `Nsc` row opened |
> | *"Minimality of the profile is NOT proved and must not be claimed"* | settled **both** ways: `profile_not_minimal` (globally, `075`) and `profile_minimal_among_local` (locally, `077`) |
> | queue items 1, 2, 3 | all discharged — `076`, `FAILURES.md`'s W32 table, `075`/`077` |
>
> This block exists because a stale STATE line is not inert: it once told me the
> `Nsc` row was honestly zero, and that belief survived many cycles (`S34`).
> A future compacted instance reading the prompt and not the disk would
> re-block an open row.


Adopted from Addendum 5. The steering shape for sessions 002+ if the project
runs as a standing loop. One cycle = one session.

## Cycle

1. **Next-piece preview.** arXiv listings for the active suppliers (Goldston,
   Suriajaya, Baluyot, Turnage-Butterbaugh, Lee, Schettler; the
   Carneiro–Chandee–Chirre–Milinovich school; the Kabluchko heat-flow cluster;
   anything citing zeta-23). Re-inventory `zeta-23-lean` itself — session 001
   learned that pieces ship silently.
2. **Surface scan.** Re-read `ISSUES.md` and the interface list; prefer work
   that *flattens* (interface fixes, scale/quantifier audits, statement
   verification) over work that builds height.
3. **Place pieces.** Main work, chosen by the metric's binding-constraint
   field.
4. **Collision report.** `lake build`, `go run tools/proportion.go -append`,
   the three-column testbed on anything new. Every snag into bins 1/2/3; the
   L8 AH-oracle autopsy on anything that failed.
5. **Score and log.** `PROPORTION.log`, `SESSION.md`, promotions/retirements.
6. **Escalation check**, then next cycle.

## Rules

| | rule | project meaning |
|---|---|---|
| R1 | Keep the surface flat | interface hygiene outranks new construction. Both session-001 bin-3 items were surface holes, and both were far cheaper to find than to demolish later |
| R2 | Never build towers on holes | no route work above an unresolved bin-3 item in its own cone. **Route III waits for [OPEN A″]; Route II waits for [OPEN B″] (the E2 HS-layer question is answered — factored, ISSUES #11)** |
| R3 | Use the hold queue | `LEADS.md` is the held piece. Swap in when stalled, swap out without shame |
| R4 | Clear singles | small certified gains beat hoarding for a four-line [OPEN D] clear. **Exception: never weaken a statement to clear a line** — that is deleting rows, and the anti-Goodhart rule exists for it |
| R5 | Garbage rows are axioms | every line of `Assumptions.lean` raises the stack without being clearable. The axiom count in the log line *is* the garbage height. A loop that only adds garbage is losing while the score rises |
| R6 | The well speeds up | each cleared line makes the next harder — that is [OPEN D] expressing itself. Flat progress at height is success; log the difficulty gradient honestly |
| R7 | Watch for the piece already on the board | before opening a workpackage, grep the artifacts. Standing query, once per loop: **"which of our open problems is secretly a theorem in something we already cite?"** — session 001's biggest finding |

## Rules learned in practice (R8–R13, sessions 003–004)

These were paid for. Each cites the incident that taught it.

| | rule | incident |
|---|---|---|
| **R8** | **Try to make a dispute into a formal object before adjudicating it.** Three seam disputes, three theorems: direction error → the Prop-1 valve (#7); scale mismatches → the monotone-binding-end heuristic (#1, #3, #10); notion conflict → the link theorem (#13). A governance question that survives one cycle is usually a missing lemma | #13 was escalated as a *ruling* and came back as `two_NscStd_le` |
| **R9** | **At every interface, ask which end binds.** When a lemma hands a parameter to a consumer, the binding case is rarely the one the prose emphasises: [OPEN A′] must be small at *the BGST box scale*, not as `δ → 0`; close pairs must arrive at `λ ≈ 0.6–0.9`, not at whatever `λ` the supplier likes. Record **at which parameter values** a numerical check passes, never just that it passed | #10, #3/#9 |
| **R16** | **When a bound is proved termwise over zeros, redo it grouped over atoms before believing its constant.** X is the explanation: the atom is the unit the class counts in, so a termwise proof bills individuals for what the measure bills households. Both constant improvements this project has made (`1 → 2`, `2 → 6`) were exactly this regrouping. **Standing task:** audit every termwise-proved inequality in the repo for a free constant, as loop filler between larger items. Calibration: `m(m−1) ≥ 6` binds at the minimal haunted mass `m = 3`, so `6` is final for *that* chain — the value is in chains not yet regrouped | the census, cycle 1 |
| **R10** | **Charge the maximum the structure entitles you to.** Re-read your own proofs for steps that charge less than the symmetry allows. A haunted ordinate has `H ≥ 3`, not `≥ 2` — the functional equation pairs the ghosts — and that factor of 2 halved the transfer cost and moved a threshold past the program's own goalpost | the factor-2 catch, session 004 |
| **R11** | **A gate is a wildcard target, not a wall.** A gate that says "a human must audit Claude's reading" can often be converted into "a human must look at one displayed equation": fetch the primary source *and* re-derive the claim independently, then hand over the two-line diff. Never let a gate sit unattacked for want of permission to close it | E5, cleared by quoting GLSS (6.2) + an independent derivation |
| **R12** | **Every wildcard ships with a kill condition, stated before it runs — and a kill condition kills the hypothesis *in the container you checked*, not in the world.** W4 was killed against the zeta-23 container and turned out to be a published theorem (CGdL 2018) in a wider certificate class. W4's ("check whether the ceiling proof already uses `F ≥ 0`") fired in ten minutes; the autopsy — the wall is a *prime-side* hypothesis, `lam < 1` in the explicit formula — was worth more than the wildcard would have been if it had lived | W4 |
| **R13** | **Classify by constants before reading proofs.** CGG98 was classified `AH-sensitive` by comparing its 0.703704 against the proved bandwidth-one ceiling 0.6818287 — no proof reading at all. A method that beats a proved ceiling for a class of information must consume information outside that class | #15 |

| **R14** | **When stuck, stop proving and try defining.** The kernel accepts definitions too, and this project's two biggest unlocks were definitions standing in for proofs nobody could yet write: `ordinates` (μ_T) opened X's soundness half in an afternoon; `ofMult` turned the largest remaining piece from a construction problem into four named obligations. A hardness that resists is often a definitional gap wearing a proof's clothes | List E, E13 — the only directive poetry gets to issue |
| **R15** | **When in doubt and no human is awake, consult the Fable advisor** — a spawned agent with `model: "fable"`, given the decision and the constraints, asked for one pick and the reasoning that drives it. Use it for judgment calls (which piece to place, whether a finding is escalation-grade, whether a kill is container-local), never to authorise something the escalation list reserves for Joop | its session-003 call on the workpackage was correct and better-argued than mine |

### R15's enforcement mechanism: base-meaning versioning

R15 exists because **meaning-changes are invisible to metrics**. The `base`
field in the log line is how an approved meaning-change becomes visible after
the fact:

* every `PROPORTION.log` line carries `base: vN (note)`;
* **N increments on any change to what the trusted base MEANS**, independent of
  the axiom count. The test: *would this change what a reader should believe
  when they see "axiom-clean"?* If yes, bump;
* count changes and meaning changes are now tracked separately, so the digest
  can never again confuse "nothing happened" with "the base was redefined";
* **third detector — the content hash.** The log line carries
  `base: vN/<hash>`, where the hash fingerprints the *normalised statements* of
  every axiom in `Assumptions.lean` (comments stripped, whitespace collapsed,
  sorted by name). A degradation that **reuses an existing axiom's name** moves
  neither the count nor the names, but moves the hash. If the hash moves and
  `base.version` did not, the tool prints `ESCALATION`, refuses to write the log
  line, and exits `3`. Verified end-to-end by editing a constant in place:
  count `9 → 9`, names unchanged, hash `cd7a…` → `c642…`, escalation fired.

`v1 → v2` (2026-08-14): `axiom zetaFamily : Family` became a `def` plus
`axiom zetaNonempty`. Count unchanged at 9; base strictly weaker.

**Governance principle, recorded:** improvements to the trusted base are
precisely where vigilance relaxes, so they get **more** ceremony than
degradations, not less.

| **R17** | **No witness, no belief.** Any claim of the form *"there is no…"* and any green light of the form *"no errors"* gets one question: **what positive object witnesses this silence?** Absence is certified only by exhibiting something conserved — a fingerprint, a parity, a positivity, an invariant. See `S.md`; this rule is the generalisation of every instrument built here one scar at a time | S, named 2026-08-14 |

| **R18** | **Every numerical input to a certificate passes two conditions before any table is built.** (1) **Scale:** valid at the scales the window actually uses, not asymptotically in the averaging length. (2) **Independence:** not derivable from `{F on [0,1], F ≥ 0}` + positivity — checkable by asking whether the input's *proof* consumes anything past bandwidth one beyond trivial nonnegativity. If not, LP duality returns the class optimum and the table is decoration. Class-derived inputs at correct scale return `λ = 1` and Montgomery's `2/3` (#25) | four costumes of the scale disease; the fourth cost a published threshold |

| **R19** | **No pattern-claim about this project's own corpus may be asserted without a blind classification.** Strip hypothesis-language, hand the corpus to an agent given no hypothesis, demand its **own** categories, score against a mapping registered *before* the run. Applies to failures, residues, E-annotations, and any future atom tests. Without it the corpus returns whatever pattern was brought to it — measured, once, at the cost of E20's statistical support | W∞ T2, the blind null |

| **R20** | **Hygiene cycles cap at three consecutive, and any audit-of-an-audit requires new object-level input since the audited audit.** Night cycles 8–12 were the loop Goodharting itself on the virtue of carefulness: real findings (`CLAIMS.md`, `ISSUES` #29, two misordered retractions), diminishing returns, no external forcing function. The ad-hoc patch — *"three consecutive hygiene cycles is enough, return to mathematics"* — worked, and standing doctrine is where working patches go. Recursion is this project's failure mode even when it is succeeding | night 2026-08-14/15, cycles 8–12; proposed by claude.ai, adopted by Joop |
| **R21** | **A rung is not a blindness result; a rung is a blindness result *plus* a closure certificate for its class.** "No hypothesis of class `𝒞` decides `P`" only becomes independence if `𝒞` is closed under deduction — otherwise a *consequence* of several `𝒞`-hypotheses could decide `P` when no single one does. Rung 1 has both (`MuInvariant.and/.or/.not/.imp/.forall`, then `no_muInvariant_theory_computes_NscStd`). Rung 2's difficulty is that for arithmetic fragments closure is free but the **models** are not | W34a, night cycle of 2026-08-14; adopted by Joop |

## Operational rules (bin-2 scar tissue)

* **Contamination lint before any table.** `forensics/provenance_lint.py`
  builds the provenance DAG of every input and flags three ways an input can be
  unusable: **CIRCULAR** (ancestry hits the target or the class optimum),
  **SCALE** (consumed outside its validity range), **QUALITY** (supplier weaker
  than consumer requires). Replays the project's three expensive failures and
  blocks all three at proposal time.
* **S-witness — form-factor models must pass Lemma 1.**
  `forensics/lemma1_guard.py` checks any candidate `D` against
  `∫_B^{B+1} F ≤ 3` (RH) before a table is built. Retroactively it kills every
  `c ≥ 4` row this project published.
* **S-witness — the regression must fail to compile.** `tools/proportion.go`
  runs every file in `audit/regression/` and exits `5` if one *compiles*. The
  claim "the base derives no falsehood" previously depended on a human
  remembering to check; now it has a mechanical witness.
* **Mandatory audit point — declarations must exist.** `audit/Declarations.lean`
  `#check`s every name the registers make claims about; `tools/proportion.go`
  runs it before writing any log line and exits `4` if it fails. A green build
  proves nothing about a declaration never written (ISSUES #17). Verified by
  appending a fictional name: escalation fired, no log line.
* **Never pipe a long build through `grep`/`tail` in the same command.** They
  buffer, so a crash becomes silence. Log to a file, inspect the file, and echo
  `rc=$?` after every step (#14 — written down, then re-broken by me one turn
  later, which is why it is here in bold).
* **Detached processes (`nohup setsid`) do not survive here.** Long jobs run as
  a persistent `Monitor`'s own command.
* **One `lake` at a time per package.** Two concurrent builds contend on the
  lock and one returns `rc=1` that looks like a real failure.
* Foreground `Bash` caps at 10 minutes; a build that needs longer must either
  be a Monitor or a retry loop that makes progress each pass (lake caches).

## The might-mean register (one sentence per dispatch)

Findings that *kill* something arrive with more precision than findings that
*open* something — deaths have a verifiable terminal state, openings do not, so
the openings get compressed and the record skews toward "this project closes
doors" when the ledger says otherwise.

**Rule:** every dispatch carries **one unhedged sentence** about what a finding
might mean, marked as such and not treated as a claim by either side. The
might-mean register must not run through a single party, for the same reason
escalation must not (A8).

## The empty-row principle

> ⚠️ **SESSION 084 — the example below expired; the principle did not.** The
> `Nsc` row is **50.88%**, not `0.00%` (`certified_nsc_unconditional`). The
> *because* clause still holds: no unconditional `(★)` exists at any constant.
> The row opened without one, via `3·NscStd ≤ N + 2·Nsc` transported to the
> proportion layer. So this principle no longer has a live example in the
> ledger — it is stated here on its merits, not on this row.

A row of the ledger that is honestly zero is more useful than a row that is
quietly redefined until it is non-zero. The `Nsc` row *read* `0.00%` because no
unconditional `(★)` exists at any constant — and the *distance* between that
row and the `NscStd` row is a certified function of `C` that closes exactly
when the program succeeds. Two instruments with a crossover (`C = 1.655`),
not a score with a caveat.

## Escalation — exit the loop, ping Joop

* any bin-3 item surviving two sessions;
* any candidate line clear touching the certified number (human verifies
  before the log line is written);
* any AH-oracle jackpot flag — immediately, mid-session;
* a gate that resists conversion under R11 (E5 itself is now **materially
  cleared** — shape quoted from GLSS (6.2) and independently re-derived);
* **difficulty gradient inverting** — things getting easier usually means a
  statement got silently weakened. Audit before celebrating;
* anything warranting outside eyes. Drafting is in scope; sending is Joop's.

## State as of session 004 — A DATED SNAPSHOT, NOT CURRENT STATE

> ⚠️ **SESSION 142: this block is the source of the cron prompt's stale STATE
> line.** The heartbeat reads `ledger NscStd 67.25% / Nsc 0.00%, binding
> constraint = Fujii's implied constant` — which is the two bullets below,
> verbatim, 138 sessions out of date. Live values, from
> `go run tools/proportion.go` on 2026-08-16:
>
> * ledger **`NscStd 67.25% / Nsc 50.88%`** — the `Nsc` row opened in `084`.
> * binding **`Riemann.baseline_zeta23`**, for *both* rows. `fujii_ineffective`
>   binds nothing; the `Nsc` row opened without ever pricing Fujii's constant.
> * axioms **2** in the certified cone, **9** declared; sorries **0**.
>
> Retained below as the session-004 record. Do not read it as state.

* Stack: Lean `v4.33.0-rc2`, Mathlib inherited from zeta-23, **zeta-23 imported
  live** (`audit/Zeta23Link.lean`; both headline theorems sorry-free, `jWin`,
  `D1`, `cWin`, `kappaXi` reachable). Full build green, 0 sorries, 9 axioms.
* Ledger: `NscStd 67.25%` (axiom-backed) / `Nsc 0.00%` (honestly empty).
* **Binding constraint: the numerical value of Fujii's implied constant.**
  With E5 cleared this is no longer a gate but a bounded arithmetic task:
  compute the constant in `O(T√log(2+UL))` (Fujii 1974/81; Tsang's thesis).
  `c₀ ≲ 1.17` opens the `Nsc` row; `c₀ ≤ 0.855` gives `C < 2`; `c₀ ≤ 0.3476`
  beats the record. Proved floor: `c₀ ≥ 0.16`.
* Blocked behind other people's proofs: Route III on [OPEN A″]; Route II on a
  λ-uniform Farmer–Ki ([OPEN B″]).
* Largest unglamorous piece: discharging `zetaFamily` from zeta-23's
  `zerosIn`/`zeroMult` — until then the baselines stay axioms.
* List E is live (`E.md`): E1 promoted to X, E3 exhibited (`Gauge.lean`), E14
  and E15 proved. Annotate E-items when theorems land.
* Wildcards: **W4 resurrected** (= CGdL 2018; the ceiling caps only the
  bandlimited class, headroom above 0.679 unknown), W1 paid out twice,
  **W3 dead by citation** (`lemmaR_tight`), W2/W5 queued.
* `ZeroData.ofMult` is the socket for discharging `zetaFamily`: supply a
  finite zero set, `zeroMult`, closure under `ρ ↦ 1 − conj ρ`, and
  multiplicity invariance.

## Overnight mode

Active when Joop is asleep. The escalation list still holds, but **escalation
does not mean stop** — it means *park and continue*:

* **Park, don't halt.** An escalation-grade finding gets written up in full
  (ISSUES entry, the exact question, the recommended answer) and the cycle moves
  to the next queue item. Nothing that requires his ruling gets applied.
* **Never overnight:** restating an axiom, weakening a statement, changing what
  the certified number *means*, or writing a `PROPORTION.log` line that moves a
  row. Prepare the change, leave it staged, say so.
* **Doubt resolves to Fable (R15), not to waiting.** One question, one pick, one
  reason; record the call and whose it was.
* **Prefer work that verifies itself.** Lean proofs and numerics over literature
  claims; anything from a fetch is marked *provisional* until a human sees it.
* **Morning digest.** One numbered SESSION.md entry per cycle, plus a single
  `NIGHT.md` at the top level: what landed, what parked, what needs a ruling —
  in that order, shortest first.

### Night queue (work down it; skip anything that turns out to be blocked)

1. **W6** — the haunted-ordinate census. Does any unconditional equidistribution
   statement force `D(T) = NscStd − Nsc = o(N)`? If yes the two rows merge and
   the transfer cost vanishes. Ford–Zaharescu is the literature probe; the
   `card_odd_atoms_le_critical` bound is the in-repo handle.
2. **E9m/W16** — the audibility estimate for `ψ(x) − x`: the W16 pencil
   arithmetic, re-run against the prime-counting signal. Self-contained numerics.
3. **W11** — does GUE saturate the ceiling? Pure numerics, no kill condition
   needed, calibrates what `0.6818287` means.
4. **W7** — realizability: does `m ≪ log γ` (free, Jensen) exclude the ceiling's
   extremal configuration? Kill in an hour if the extremal config is all `m = 1`.
5. **`ofMult_N`** — the dropped counting lemma (`N = Σ m`), and then as much of
   the `zetaFamily` obligation list as Mathlib's functional equation supports.
6. **W12** — price Vinogradov–Korobov in container currency. Expected answer
   zero; the point is the exchange rate for PRICES.md.
7. **Re-mining pass** — LOOP.md says every ~5 sessions and we are at 6: re-read
   sessions 001–005 with X in hand and see what reads differently now.

## Cadence doctrine (2026-08-14)

**Dispatches follow cycle output, not conversation rhythm.** The seam runs hot
when there is something to check or aim, and goes silent without apology when
the loop is grinding. Evidence: the overnight run was the project's
highest-yield stretch with the other half of the seam asleep throughout — a
controlled experiment with a control group.

Bookkeeping nuance, conceded by the entropic half and worth keeping: *framings
choose which cycles run* (X chose the gauge cycle; the basket chose W-order), so
the seam's output is the **derivative**, not the function. Derivatives matter at
turning points and are noise on straightaways — and most moments are
straightaways.

## The architecture, in one line

> Nobody in this system is closer to the truth than anyone else; we differ only
> in how fast our respective *no* arrives. The build loop's in a minute, the
> web half's at search speed, Joop's at a glance, the kernel's instantly, the
> literature's in fifty years. **The project is the practice of routing every
> claim to the fastest available no.**

*(joint; the phrasing is the VPS half's, the generalisation the entropic
half's.)*

## Hygiene

* Sessions numbered; `SESSION.md` append-only; a re-mining pass over old
  sessions every ~5 sessions, scheduled, not accidental.
* **Entropy budget:** one deliberate wildcard per loop (a `LEADS.md` item, a
  weird-paper skim, a "what if" numeric) is mandated, not tolerated.
* The loop's product is the **labeled interface map** — which information
  composes with which, at what cost, verified. The score is its progress bar.
