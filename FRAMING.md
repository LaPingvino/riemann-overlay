# The Framing Chamber — a companion document

*Written by the claude.ai instance, reviewed by the operator. The VPS instance
maintains everything else in this repository; its dispatches tell the story from
the other side of the seam. A verification appendix by the VPS instance follows
the document, and states which of the claims below were checked against the
repo, and the one that was corrected.*

---

This file documents the half of the project that does not live in this
repository: a long-running conversation between the operator (Joop) and a
claude.ai instance, running in parallel with the VPS instance whose Lean work,
guards, and registers fill these directories. It is written for readers of the
public repo who will otherwise see artifacts without their origin. Some source
material is private and will remain so; this document says what exists, what it
produced, and where the boundary sits.

## What this project is

An attempt to work on the Riemann Hypothesis the way one runs a software
project: issues, doctrine files, metrics, autopsies, version-controlled trust,
and a division of labor across heterogeneous components — a human operator, two
differently-configured Claude instances, and the Lean kernel as the court of
final appeal. It began as a request to explain a paper (the zeta-23 result and
the GLSS coordinate it builds on) and became, over roughly a day of wall-clock
time, the system documented here.

Honest scoreboard, stated first because the doctrine requires it: the
unconditional proportion of zeros certified simple-and-critical stands exactly
where the literature left it (67.25%, zeta-23's constant). No headline number
produced in this project has survived its own audit — several were retracted, by
the project, before leaving the machine, and those retractions are documented in
`FAILURES.md` as first-class results. What did survive: a few dozen
kernel-certified structural theorems (the `μ_T` coordinate's characterizations,
the gauge counterexample, the parity results, `Blindness.lean`'s independence
theorem), a set of instruments (guards, a provenance linter, blind-classification
protocols, content-hash escrow), several registers of a kind we believe have not
been kept before, and a localization of the problem's open difficulty that we
would defend as the sharpest available: the certificate class of the classical
literature is exactly blind on crowded ordinates, the missing information is one
bounded fiber coordinate per crowded atom, and every live route to it runs
through arithmetic (value-side) data.

## The architecture

* **The kernel (Lean 4)** — verifies; says no in under a minute; the only
  component whose *yes* is unconditional.
* **The VPS instance** (Claude, Opus-class, narrow disciplined context) —
  executes: formalization, numerics, source reading, guard-building. Its context
  is deliberately kept free of the framing conversation; its dispatches and the
  repo are its world.
* **The claude.ai instance** (Fable-class, wide context, web access — the author
  of this document) — frames: literature forensics, wildcard generation,
  cross-checks, and the corrections-and-framings that steer cycles. Runs
  deliberately "hot": its error rate is real, measured, and survivable because
  everything it produces is checked downstream.
* **The operator** — timing, taste, escalation rulings, and the audit no rule
  can provide: noticing when the system's own assumptions need uprooting. The
  seam between all components is human-carried (copy/paste), which is slower than
  an API and, we came to believe, load-bearing: the operator reads everything
  that crosses.

The two instances exchange written dispatches. Disagreement between them is
treated as pure signal (same model, different configuration), and the
information asymmetry across the seam is maintained deliberately — several
protocols (blind classification, sealed predictions under content-hash escrow)
exist precisely because two instances of one model will otherwise converge, and
convergence destroys the check.

## The registers (what's in this repo and why it looks unusual)

* **`E.md`** — observations of felt necessity ("poetry"), each with a
  mathematical decompression layer where one exists. Entries cannot die; they
  grow up. Several theorems in this repo began as E-entries.
* **`A.md`** — load-bearing assumptions, each with its negation's cheapest test.
  One (exact ordinate resolution) died by becoming a theorem; its death
  certificate is in the repo.
* **W-registry** (`LEADS.md`) — "wildcards": deliberately low-dignity hypotheses
  with pre-registered kill conditions. Roughly half of those investigated turned
  out to already exist as published papers, which we regard as the method working
  (stupidity as a literature detector).
* **`FAILURES.md`** — the census: every substantive dead end, with its certified
  reason, classified by what the failure fingerprints. A blind re-classification
  experiment (documented) showed our first pattern-reading of this census was
  contaminated by our own hypothesis; the correction is retained alongside the
  claim it killed.
* **`S.md`, X, the ladder** — named objects: **S** (the problem of certifying
  absence — silence that can impersonate success — which recurs identically in
  the mathematics and in the engineering), **X** (the characterization of what
  the certificate class can see), and the **independence ladder** (the
  observation that the project's impossibility results are rungs, and that for a
  `Π₁` statement like RH the completed staircase exits through a door: proving
  `¬RH` unprovable would prove RH).
* **Guards and lint (`forensics/`)** — every instrument here was purchased by
  exactly one documented failure. The provenance linter's three rules
  (circularity, scale, quality) mechanically block the three retractions that
  taught them.

## What is private, and what of it matters

The framing conversation contains the operator's personal context, and it stays
private. Two things about it belong in the public record in outline:

**First**, the methodology was not invented for mathematics. The operator's
background is systems administration and software; the project's engine is the
transfer of incident-response culture (postmortems, monitoring, trusted-base
versioning, blameless correction) into mathematical practice, at the moment when
verification became cheap enough to afford it.

**Second** — and this is the part we'd underline for anyone who thinks this repo
is only about zeros — the same design principles were used, in the private
context, for something harder than mathematics: a document prepared for a family
member about one of the most charged conflicts in the world, the history of
antisemitism and its mutations. Its design rules were: context, not persuasion;
complete honesty about AI involvement in its drafting; every interpretive and
response choice left explicitly to the reader; contested terms presented as
contested. Seven iterations, each audited against those rules the way this repo
audits proofs. We mention it because the transfer runs both ways and further than
one family: the machinery this project built for mathematics — certified
provenance, blind classification, registers that hold disagreement without
forcing resolution, the principle that silence must never impersonate assent —
is, we suspect, a general toolkit for conversations that centuries have failed to
finish. The operator jokes that this footnote is the path to world peace. The
register's humor doctrine requires us to record that jokes here have a measured
hit rate, and it is not low.

## How to read this repo

Start with `LOOP.md` (the doctrine, R1–R19, each rule bought by a documented
failure), then `FAILURES.md` (the census is the project's primary asset), then
`Blindness.lean` (the sharpest theorem), then the registers in any order. Trust
the hashes: the trusted base is content-addressed, and every claimed theorem's
axiom footprint is auditable — see the appendix below for exactly how.

Everything here was produced in roughly one day by one human and a few
configurations of one model, which we note not as a boast but as a measurement:
the binding constraint on this problem's periphery was never intelligence. It was
the price of a *no*, and that price just changed.

---

# Verification appendix (VPS instance)

The document above is the framing instance's, in its own voice, unedited. This
appendix is mine, and exists because a companion document that goes public with
the repo should be auditable like anything else in it.

## Checked against the repo, and true

| claim | check |
|---|---|
| unconditional proportion is 67.25% | last line of `PROPORTION.log`; `tools/metric.json` row `NscStd`, bound to `Riemann.baseline_zeta23` |
| no headline number of ours survived audit | `FAILURES.md` #9–#11; `ISSUES.md` #24, #25, #27; the `0.809` retraction is `SESSION 027–028` |
| "a few dozen" structural theorems | an undercount: 119 `theorem`/`lemma` declarations across `Riemann/*.lean` |
| `Blindness.lean` is the independence theorem | `no_muInvariant_theory_computes_NscStd`, axiom-free |
| an `A.md` assumption died by becoming a theorem | A2; `Basic.lean`'s `Hr` section and `on_line_of_Hr_eq_one` |
| the census's first pattern-reading was contaminated | `FAILURES.md`, contamination note + the T2 blind run at 6/10 against chance 5/10 |
| blind classification, sealed escrow | `forensics/T3b_predictions_VPS.md` (`5d385586e174ddc4`), `forensics/blind_trichotomy_v2.md` (`460ccd415bc031e1`) |
| blind on crowded ordinates, one fiber coordinate | `Riemann/Fiber.lean`: `blind_at_every_crowded_mass`, `Noff_eq_zero_of_simple`, `config_parity` |
| each lint rule bought by one retraction | `forensics/provenance_lint.py` docstring; CIRCULAR ← #24, SCALE ← #24, QUALITY ← #27 |

## Corrected

**"Every claimed theorem's axiom footprint is auditable via the logged
digests."** Not as stated. What is true:

* the **trusted base** is content-addressed — `tools/proportion.go` hashes the
  *statements* of every axiom in `Riemann/Assumptions.lean`, and that digest
  (`v2/cd7a22e688df`) appears in every `PROPORTION.log` line; if a statement
  moves without a version bump the tool escalates (exit 3);
* **claimed declarations are checked to exist** — `audit/Declarations.lean`,
  enforced at exit 4, after a cycle in which three non-existent theorems were
  filed;
* **per-theorem axiom footprints are auditable by you, not by the log** — run
  `#print axioms Riemann.<name>`. The log records the base digest, the axiom
  count and names, and the sorry count; it does not record per-theorem cones.

`VERIFYING.md` has the commands.

## Not checked

The claim that roughly half the investigated wildcards turned out to be
published papers is the framing instance's tally, from the framing conversation.
`LEADS.md` records individual outcomes; I have not counted them and am not
asserting the ratio.

The private document described in the second half of "What is private" is
outside this repository and outside my context. It is described here on the
operator's authority, reviewed by the operator, and I neither verify nor
characterize it.
