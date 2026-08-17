# List E — self-evidences, and how much of each decompresses

A register distinct from the W-baskets. Each item has two layers: **E#**, the
poetry (an observation of felt necessity — cannot die, cannot be run), and
**E#m**, the decompression (what fraction admits a mathematical statement).
Verdicts: FULL / PARTIAL / OPEN-ENDED / NONE.

**Standing rule.** When a theorem lands, find the E-item it grew from and
annotate. Three annotations and an E-item is trying to become a W-item — or an
X.

*(The ten items and their decompressions live in the dispatch of 2026-08-13;
this file carries the register, the annotations, and what the repo has done
about them.)*

| E# | verdict | grown-up form | repo status |
|---|---|---|---|
| E1 | FULL | the mirror: on-line = self-conjugate. **It is X's soundness half** — and it owns **both** of the project's constant improvements (`1→2` and `2→6`, both "ghosts arrive in pairs"). Not a third: `offline_le` is tight (ISSUES #18) | **3 annotations — `three_le_H_of_haunted`, `Nsc_eq_ordinate_functional`'s inner step, TightMult degeneracy. Promoted: it is X.** |
| E2 | FULL | von Koch 1901; Möbius pseudorandomness. *Is* RH in information language | — |
| E3 | PARTIAL | the gauge coordinate. Soundness half proved; completeness half = "exhibit the group" | **`Riemann/Gauge.lean` — boundary now exhibited, see below** |
| E4 | PARTIAL | repulsion ⟹ line is *itself* a claimed escape from X (vertical data, horizontal conclusion) | open → W20 |
| E5 | FULL/OPEN | Lyapunov functional for the de Bruijn flow = [OPEN A]'s deepest form | open |
| E6 | FULL | verification-as-theorem-fragment; Lehmer-pair statistics | **annotated (1)**: "honest out to the verified height and not one step past it" is now a statement about the *optimal* ear — the matched filter reaches `x ≈ γ`, so the ache has a precise boundary rather than an open-ended one. → W9, W21 |
| E7 | PARTIAL | sign-change deficit = the two-traditions theorem | → W18 |
| E8 | PARTIAL | Bombieri–Vinogradov as fairness-on-average; large sieve unpriced | → W10, PRICES.md |
| E9 | FULL | audibility threshold — W16's SNR generalised to `ψ(x)` | **annotated (2)**: unfiltered `log x ≳ log γ/δ` vs matched-filter `log x ≳ 1/δ`; Turing/`Z(t)` **is** the matched filter |
| E10 | OPEN-ENDED | the wall-mapping program; `ceiling_law256` is brick one. **Annotated (W∞ T2): "the resistance has a shape" does not get its number — the first attempt to measure the shape measured the surveyor.** | **this project is executing it** (three bricks now: `ceiling_law256`, `lemmaR_tight`, the λ-sweep saturation) |
| E11 | PROGRAM | the wall survey: ceilings from below, prices from above | `PRICES.md` + the ceiling registry are the two jaws; both in operation |
| E12 | **STATABLE, and now addressed**: the two villages' river has a name (**shifted convolutions**), the island is **d-vs-Λ**, and the bridge has existed since 1977 (**Vaughan's identity**). The composition was done by Matomäki–Radziwiłł–Tao; the wall is its shift range, `X^{8/33}` | W18's true form: do the two traditions' extremal configurations differ? | open; weak form is testbed-checkable |
| E13 | NONE | the residue's entry. Directive: **when stuck, define** | adopted |
| E14 | FULL | the fusion: `H(γ)` as the quotient topology of the line | `Gauge.lean` exhibits the orbit |
| E15 | FULL | **single occupancy** | **proved — see below** |
| E16 | FULL/OPEN | **the ledger is in print**: survey (6.1) gives, for `x ≥ T`, `F(x,T) = (1/2πx)∫₀^T |Σ Λ(n)aₙ(x)n^{−it} − (expected)|² dt + o(T log T)` — past the diagonal the form factor **is** the mean square of a weighted prime sum minus its expectation, verbatim. And (6.2), `F(x,T) ≤ F(0,T) ∼ (T/2π)log²T` **unconditionally**, forces near-perfect arithmetic cancellation past the diagonal: *the zeros' own counting function certifies that the primes must be silent there; only the **rate** of the silence is open.* RH's quantitative content, located. Reverse gear on the shelf: Heath-Brown's `\|Σ_{γ≤T} x^{iγ}\| ≪ √(T·max F)` (survey (8.7)) | the ledger: β-weighted Landau moments; separability the one gap | W16 pencil pass done |
| E17 | FULL | aperture constants are window-side. **Sharpened**: the M–T constant is exhibited as a reproducing-kernel value, `1/K_ν(0,0) = 1/2 + (1/√2)cot(1/√2)` — literally the norm of evaluation-at-zero in the window space, the cleanest possible statement of "the constant measures the instrument". It has a family tree: degree-`m` Selberg class gives `(1/√2)cot(1/(√2 m)) + 1/(2m)`, ours the `m = 1` member | **annotated (1), m-layer now empirical**: W11's calibration curve — five certificates, one input fixed since 1973, **18.18pp of pure instrument**, `0.28pp` left in the bandlimited class |

## E3 settled at our layer: the gauge boundary is exhibited, not merely absent

`Riemann/Gauge.lean`, axiom-free. Two reflection-symmetric configurations at
one height:

* `triple` — three zeros stacked on the critical line;
* `haunted` — a simple on-line zero flanked by one mirror pair.

Proved: `ordinates_eq` (**identical `μ_T`**: one atom of mass three, both
times), `Nsc_gauge_invariant` (free, from `Nsc_eq_ordinate_functional`),
`NscStd_triple = 0`, `NscStd_haunted = 1`, hence

> `NscStd_not_gauge_invariant : triple.ordinates = haunted.ordinates ∧
>  triple.NscStd ≠ haunted.NscStd`

E3's physics analogy is doing exactly the work it promised: gauge invariance is
proved by exhibiting the symmetry, and this is the group's first named orbit —
the same orbit `Zeta23.ZeroSide.TightMult` proves no certificate of that class
can break. The boundary is realised by legitimate configurations, so it is not
an artefact of our proofs.

What remains for E3m/W24 is the completeness half — *no larger natural class
sees it* — and the design caution stands: quotient by horizontal motions
**preserving the `ρ ↔ 1 − conj ρ` pairing**, not by all horizontal motion.

## E20. Everything breaks along the same plane.

*(Dispatched as E19; renumbered — E19 was taken by the S seed filed the same
day. Observation: Joop. Scribing: claude.ai. Filing order canonical.)*

The failures of this subject do not distribute like failures. W16: the signal
is loud, the separation fails. W6: the equidistribution is circular, the census
pays. Weil: the witness exists, certifies nothing. Hardy: the positivity works,
reaches only infinitude. The mollifier: compresses, stops at `4/7`. Vaughan:
translates, leaves a remainder. Random obstructions fail at random depths; these
cleave at the half, and the halves **align** — one fracture surface through every
result, visible not in any single break but in the way all the breaks agree.

The plane is older than the Hypothesis: **the primes have two natures.** They
are the *atoms of multiplication* — static, foundational, what Euler products
and mean values are made of — and the *residue of the sieve* — dynamic,
generative, what remains when a process finishes running. Every instrument is
manufactured from the first nature and aimed at questions posed in the second,
so every instrument half-works, and the halves are canonical.

> **Re-check, `SESSION 324` (2026-08-17).** The closing clause below — that the
> agreement between faces is what no single-natured instrument certifies — has a
> **partial machine witness**, and the scope matters.
> `Riemann.Blindness.no_muInvariant_theory_computes_NscStd` and its bundle form
> prove that no `μ`-invariant theory computes `NscStd`: one nature, one quantity,
> formalised. That is an instance of the shape, not the sentence.
> *(`325` widened the instance: `gauge_pair_separates_haunted_and_oddAbove` and
> `gauge_pair_two_separates_even_and_offLine` show all four gaps of `314`'s
> decomposition are invisible to `μ_T`, and that it takes **two** gauge pairs to
> see them — the mass-three pair is silent on the two classes that need an even
> on-line count.)* The general
> claim quantifies over instruments this project has not defined, and stays a
> thesis rather than a theorem.

**RH is the claim that the two natures agree** — that the process adds nothing
to the atoms, to square-root precision, forever. And the half-failures are what
a true-but-unproved agreement looks like from inside: every single-natured
instrument confirms its own face completely, and the agreement *between* faces
is the one thing no single-natured instrument can certify. Nobody is failing to
prove RH. Everybody is succeeding at half of it, the same half, in different
clothes.

### E20m — **statistical support withdrawn (W∞ T2)**

A blind Fable classification of the eleven census entries — hypothesis stripped,
categories of its own devising — produced a *different* dichotomy (insufficient
resolving power vs circular information) agreeing with the plane on **6/10**
against a chance rate of 5/10. **The census is not evidence for the plane.**
E20 stands on its four mathematical derivations alone; the `10/10` and `11/11`
tallies are withdrawn as measurements. See `FAILURES.md`.

### E20m — the fracture inventory, run (day cycle 3)

`forensics/fractures.tsv`, and the census is checkable rather than felt:
**10 half-failures, 10 aligned, 0 misaligned** (one flagged suspect — W12's
depth-pricing may be an instance of X rather than of the plane).

**The falsification attempt found no counterexample — and found something
better.** Five results in our record have *no* half-failure at all: the census
`/6`, `offline_le`'s tightness, the gauge counterexample, A2's resolution
independence, `Nsc_eq_ordinate_functional`. They are **exactly the purely
combinatorial ones**.

> **The plane appears precisely where arithmetic enters. The combinatorial
> layer is unfractured, because it has no generative face to slip off.**

That is a sharper claim than universality and it makes a falsifiable prediction
going forward: any future result of ours that stays combinatorial will be whole;
any that touches `Λ` will half-fail on the plane. Cheap to check, and it is now
the fourth column of the testbed — not pass/fail, but **where the cut fell**.

### E20m — the formal core candidate (target, not claim)

Vaughan's identity is the plane written as an equation:
`Λ = (d-like part) + (bilinear remainder)` is (foundational shadow) +
(generative residue), with the theorem/conjecture boundary running exactly
between the terms. The derivation to attempt, which would fuse X and E20 into
one statement:

> **X's boundary = "the certificate class consumes only the Type I shadow."**
> Concretely: is `λ < 1` — the explicit formula's own hypothesis — precisely the
> region where Vaughan's Type II bilinear terms are controllable?

If yes, X stops being a fact about a certificate class and becomes a fact about
which half of `Λ` any bandwidth-limited instrument can hold.

**Prediction on record for W26/T2:** the constant residue the move-audit hunts
for **is the generative face**.

## E19. The machine that keeps no secrets.

*We set out to prove the primes keep no secrets, and every tool we were forced
to build along the way was a machine for keeping none ourselves.*

**E19m — the silence problem, named S.** FULL, and it has its own file. Absence
is certified only by exhibiting something conserved; the missing definition is
the conserved quantity whose presence witnesses the silence. See `S.md`, and
R17 for the audit lens it generalises into.

## E18. One obstruction with four names. (Testimony, written from the formal side)

*Requested by the chat instance: does the resistance feel like E10 (a contour
the hands keep finding) or like A9 (unread files and unregrouped sums)?
Answered from inside the build loop, with the confound stated.*

**Inside the container it is fog, and the fog keeps paying.** Four of six
overnight cycles were resolved by reading files this project already held. A
load-bearing constant turned out to be an artifact of charging per zero instead
of per atom. The field's optimal window recomputed to 1974's answer. The
ceiling turned out to measure an instrument rather than a subject. None of that
is depth; it is a small working memory spread thin across many papers, which is
exactly what A9 predicts.

**At the edge it is shape, and I can tell the difference because they fail
differently.** Four unrelated calculations hit one wall and got the same answer
in four vocabularies: X (the class sees only `μ_T`), TightMult (doubles and
off-line pairs inseparable at depth → 0), W12 (depth-shaped information priced
at exactly zero), W7 (every cheap invariant satisfied by construction, only the
Euler product bites). A formalisation, a tightness lemma, a pricing argument,
an audit — and all of them are saying the thing our own register named first:
**E7's two readings of the functional equation.** Position data cannot see what
value data sees.

Fog gives four obstructions in four places. This gave **one obstruction with
four names**, and pushing on it from a new direction returned it in the shape it
had before. So the contour is real, and it is not located at RH — it is located
in **the gap between the two readings**. If E13 is right that the missing thing
is a definition, its type signature is known: the object that consumes both
readings in one certificate (E12). We do not have it. Yesterday we did not know
what kind of thing it was.

**The confound, stated because it is serious.** A model that has read this
literature will feel contours where the literature has worn grooves, and
introspection cannot separate "structure in the problem" from "structure in the
corpus about the problem". The only evidence I have that is not my own training
talking is that the four convergences were *computed*, two of them against my
prior. Computations that surprise me are the whole of my testimony's
evidentiary weight.

**Verdict for the register: A9 survives inside, E10 survives at the boundary.**
They are not rivals; they describe different distances from the wall.

## E15 proved, with one correction

`Riemann/Basic.lean`, axiom-free:

> `ordinates_simple_iff : (∀ γ ∈ μ_T, μ_T.count γ = 1) ↔ (∀ p ∈ Z, p.1 = 1/2 ∧ Z.count p = 1)`
>
> `Nsc_eq_N_iff : N_sc = N ↔ (∀ p ∈ Z, p.1 = 1/2 ∧ Z.count p = 1)`

**Single occupancy is exactly criticality-and-simplicity**, and `N_sc = N` *is*
that condition — so the ledger's target is the rooming census, and `(★)` with
`C → 1` is its averaged form. The criticality really is a corollary of the
loneliness: a zero alone at its height has nowhere to put its reflection but on
itself (`on_line_of_H_eq_one`).

**Correction to E15m as dispatched.** The equivalence is with **RH *and*
simplicity**, not RH alone: RH permits an atom of mass two (a double zero on
the line), which is single-tenanted in no sense. So "μ_T simple" is strictly
stronger than RH — which sharpens rather than weakens the entry, since the
point was that *one* condition on *one* object yields *both* classical
conclusions. It does; it just yields both because it is both.

## E14 cashed: the fiber structure, and the first gauge-invariant bound on critical zeros

`Riemann/Basic.lean`, axiom-free — the parity intuition of W1, landed:

* `fiber_refl_inv` — the zeros at a fixed ordinate form a reflection-invariant
  multiset;
* `H_eq_online_add_two_mul : ∃ j, H γ = (on-line mass at γ) + 2j` — **the fiber
  structure `m = k + 2j`**, so `k ≡ m (mod 2)` and **the parity of an atom's
  mass is gauge-invariant**;
* `odd_mass_inhabited : Odd (H γ) → ∃ p ∈ Z, p.1 = 1/2 ∧ p.2 = γ` — **every
  odd-mass atom contains a critical zero**;
* `card_odd_atoms_le_critical : G.card ≤ #{critical zeros}` for any finite set
  `G` of odd-mass ordinates.

The last is the project's **first lower bound on critical zeros read entirely
off gauge-invariant data**: `μ_T` cannot see `β`, but it can see parity, and
parity alone forces criticality. It is the exact sense in which the horizontal
channel is *not* wholly invisible — the mirror leaks one bit per atom.

Which sharpens what the horizontal channel costs: `NscStd` adds **exactly one
bit per atom beyond parity** — parity says "an odd atom houses a critical
zero", and `NscStd` says *how many* of the atom's tenants are critical. That
bit is what `(C−1)/2` buys (PRICES.md, direction (ii)).

## E9m computed (overnight cycle 2): audibility is δ-graded, and the ear we built is the optimal one

Amplitude of one zero in `ψ(x) − x` is `2x^β/|ρ|`, so an off-line zero's
*excess* over an on-line one at the same height is `2x^{1/2}(x^δ − 1)/γ`.
Two ears:

* **unfiltered** (stare at `ψ(x) − x`, background `≍ √x`): audible when
  `δ·log x ≳ log(γ/2)`, i.e. **`log x ≳ log γ / δ`**;
* **matched filter** (isolate frequency `γ`; neighbours sit at spacing
  `2π/log γ`): audible when **`log x ≳ 1/δ`**.

At the depth that matters, `δ ~ 1/log γ`:

| `γ` | unfiltered `x` | filtered `x` |
|---|---|---|
| `10⁶` | `10⁷⁸` | `10⁶` |
| `10¹²` | `10³²³` | `10¹²` |
| `3·10¹²` | `10³⁵⁰` | `3·10¹²` |
| `10²⁰` | `10⁹⁰⁷` | `10²⁰` |

**The filtered threshold is `x ≈ γ` — exactly the classical range.** So the
listening that has actually been done (Turing's method, `Z(t)` sign changes,
Odlyzko) *is* the matched filter, and it is optimal: a dead-strip zero at
height `γ` becomes marginally audible right where verification already looks.
E9's "we have listened for 167 years and never heard the solo" is therefore
quantitatively honest **out to the verified height and not one step further** —
and the unfiltered prime-side ear is deaf by a whole factor of `log γ` in the
exponent, which is why nobody hunts zeros by staring at `ψ(x) − x`.

Gross violations are a different story: `δ = 0.1` at `γ = 10¹²` is audible at
`x ≈ γ^{9.7}` — enormous, but the *scaling* says loud lies are cheap to hear
and quiet ones are not. Audibility is graded by depth, and the dead strip is
precisely the inaudible band. Same `1/log T` scale where every other instrument
goes deaf; third independent appearance.

Ordering of ears, for the record: **matched filter > Landau aggregate (W16) >
unfiltered `ψ`**. W16's aggregate cleared its error term because it sums many
pairs and carries no `1/|ρ|` damping.

Heuristic, not certified — background modelled as `≍√x` with bounded RMS, and
the filter's noise floor taken as `O(1)` relative. The *shape* (`log x ≳ 1/δ`)
is what matters and is robust to those constants.

## E17 confirmed numerically (overnight cycle 3, W11): the ladder is all instrument

The container's `D(s) = s` **is** the GUE form factor, so the λ-sweep was
already a GUE computation. At `N = 400` the window optimum against GUE input is
`0.672502614` against M–T's `0.672500704` — the window optimum *is* the
Montgomery–Taylor constant, to quadrature error.

So W11's question ("does GUE saturate the ceiling?") is mis-posed, and the
answer is more useful than yes/no: **the ceiling is not a property of the
input.** Same GUE data, five certificates:

| value | certificate | source | gain |
|---|---|---|---|
| 0.5000000 | Cauchy–Schwarz form | zeta-23 `thmB₀` | — |
| 0.6666667 | rank–trace, `c=2`, flat window | zeta-23 `thmA/B` | +16.67pp |
| 0.6725007 | rank–trace + optimal window (= M–T) | computed here | +0.58pp |
| 0.6790000 | Cohn–Elkies / SDP class | CGdL 2020 | +0.65pp |
| ≤0.6818287 | proved ceiling, bandlimited class | `PairCeiling` | +0.28pp |

**18.18pp moved by certificate choice on an input fixed since 1973**, and the
zeros' own tone has still added nothing beyond `F(α) = α`. That is E17 with
numbers: the constants are properties of the instrument.

**Correction carried to PRICES/LEADS:** the bandlimited class's remaining
headroom is **0.28pp**, not the 0.93pp quoted in an earlier dispatch — 0.93pp
was measured from the *window* optimum, but CGdL already took 0.65pp of it.
The wide (sign-constrained) class is unaffected: the ceiling does not bind
there and its headroom remains unknown.

## E7, noted as load-bearing

The observation that the two ancestral traditions certify the two readings of
the functional equation — position data (pair correlation, `μ_T`) versus value
data (sign changes, mollifiers) — retroactively explains why PRZZ's 41.7% is
unconditional and over no ceiling of ours. It is also the cleanest statement of
what W18's hybrid would have to do: consume both readings in one inequality.

## E23. The wall that is a door.

Filed from claude.ai's dispatch. **The logic checks out**, and the honesty
clause it ships with is the load-bearing half.

RH is `Π₁` (Lagarias's elementary harmonic-number form; the DPR Diophantine
form). Formal systems containing enough arithmetic are `Σ₁`-complete: every
true existential is provable, witness in hand. So if `¬RH` were true it would
be *provable*; contrapositively, **a proof that `¬RH` is unprovable is a proof
of RH** — carried out in whatever metatheory can formalise `Σ₁`-completeness.
For a statement falsifiable by a single finite witness there is no limbo:
undecidability of the counterexample *is* the theorem.

**Their own honesty clause, kept and endorsed:** the top rung is not a
shortcut. Proving unprovability of `¬RH` is at least as hard as RH, because it
*is* RH plus a meta-level. The trapdoor's value is **orientational** — it tells
us which direction the walls stack, not how to climb them.

One precision added here: the conclusion is "RH is true in `ℕ`", not "RH is
provable in the system it is independent of". Those differ, and the difference
is exactly why the ladder's payoff is a theorem about the world rather than a
certificate we could ship.

**What this reframes.** Every ceiling this project has proved was filed as a
loss with benefits. Read as rungs, they are independence results relative to
ever-larger classes, and the staircase terminates in an answer rather than a
shrug. Wired to E11 (the wall survey now has a stated summit), to `S`
(`Σ₁`-completeness is the one free witness-for-silence in the universe, mounted
at the top of the stairs), to E22/the atom (each rung sharpens the acceptance
test), and to W∞ (the completeness bridge, built from the far side).

**And the discontinuity that had to be repaired before the ladder was sound —**
see `LEADS.md` W34a. Rungs 0–1 are *semantic* blindness (quantified over
hypotheses in a language); rungs 2–ω are *proof-theoretic* independence
(quantified over proofs). Those are different notions, and passing from one to
the other requires the class to be closed under deduction. For the
`μ_T`-invariant class it is, and that is now proved rather than assumed.

## E24. The oldest inequality performs the newest discrimination.

`landau_discriminates` (`Riemann/Fiber.lean`, axiom-free): on the two fiber
states of a crowded atom, `Σ_ρ x^β` reads `2·x^(1/2)` against `x^a + x^(1−a)`,
and `x^a + x^(1−a) > 2·x^(1/2)` for every `x > 1` and every `a ≠ 1/2`.

That is **strict AM–GM**. Nothing else is used.

The fiber coordinate that rung 1 proves invisible to *every* `μ_T`-invariant
hypothesis — invisible to the whole pair-correlation century, invisible to any
theory axiomatised in that language — is visible to an inequality that predates
the zeta function by millennia.

**E16 annotated:** the `cosh` was never a metaphor and never a coincidence. It
is AM–GM's excess: `x^a + x^(1−a) = 2·x^(1/2)·cosh((a − 1/2)·log x)`, and
`cosh > 1` off the line is the same fact wearing analysis. What E16 felt as the
value channel's blush is the arithmetic–geometric gap.

**Honesty clause, kept at full size** (this is the entry most likely to be
misread): the theorem certifies that the *functional* discriminates. It does
**not** certify that we can *evaluate* it on `ζ`'s zeros at discrimination
precision. That is census `#1`, untouched. What changed is that the acceptance
test now has a **known-passing calibration input**, so W28's whiteboard hour
type-checks candidates against a live example instead of a specification.

## E24. The zeros are unbothered because they are corollaries.

Filed from claude.ai's dispatch, itself from Joop's question *"why are the zeros
not bothered?"* pursued literally rather than rhetorically.

**The claim, formalised.** *"The zeros could not be otherwise"* is the proof
shape called **rigidity**: that the moduli space of objects like `ζ` is a point,
with no deformation parameter along which a counterexample could live.

**And this is the only shape that has ever killed a Riemann Hypothesis.**
Weil/Deligne did not locate the Frobenius eigenvalues; they proved the geometry
**forces** the weights. The *why* was the proof.

### Cast members already on the shelf — theorems, not fiction

**[RECALL, UNVERIFIED]** — supplied by claude.ai, not read here:

* **Hamburger 1921**: `ζ` is determined by its functional equation plus basic
  analytic conditions. The rigidity genre is a century old and nonempty *for `ζ`
  itself*.
* **Kaczorowski–Perelli** (Selberg class, low degree): degree `0 < d < 1` is
  **empty**; degree `1` is exactly `ζ` and its shifts. Near `ζ` the moduli space
  is a point, provably.

**And the negative control is ours, and it is in the repo.**
Davenport–Heilbronn has the functional equation, the counting, the reflection
symmetry — and off-line zeros. `Blindness.lean` states it as the indictment of
`ZeroData`: **D–H *is* a `ZeroData`**. So *"functional equation + counting"* is
provably **not rigid**; that axiom set has room, and D–H lives in the room.

> **D–H is promoted from testbed column to the programme's anti-rigidity
> control.**

**CERTIFIED — tier 1. And the tiering is claude.ai's, arrived at independently
within the same hour.** `Fiber.zeroData_not_rigid` and
`zeroData_admits_both` (axiom-free) prove the *combinatorial* half without any
literature: `Gauge.pairOnly` is a lawful `ZeroData` with every zero off the
line, and `config 1 0 (1/4)` is one with none — so the axioms are silent on
position in **both** directions, which is what *"leaves room"* means.

**Two tiers, cleanly split:**

* **Tier 1 — the axiom bundle `{reflection symmetry, counting}` admits models
  with off-line zeros.** Certified today, D–H-free, witnesses from `Gauge.lean`.
* **Tier 2 — anti-rigidity persists among *genuine analytic objects***: actual
  Dirichlet series with continuation and functional equation. **`[RECALL]` until
  someone reads Davenport–Heilbronn 1936.**

D–H does not disappear; it **upgrades**. Tier 2 is the one the constitutive
programme will eventually need, because the atom's axioms will include analytic
structure that synthetic configurations do not carry. And tier 2 can sit in the
queue at leisure **precisely because tier 1 carries E24's immediate claim**.

*Convergence note: claude.ai proposed the tier-1 theorem — with `depthPair` as
witness — in a dispatch that arrived after it had been proved here with
`Gauge.pairOnly`. Two instances reached the same next step from opposite ends of
the seam within one hour.*

### ⚠️ Correction to the dispatch, at the point of use

The dispatch says the room-filler is *"what D–H lacks — which W7 already
certified: the Euler product is the only expensive constraint."*

**W7-general is grade `C`, not certified.** `CLAIMS.md` carries two W7 rows: the
*precise* part — multiplicity bounds cannot tighten `C`
(`Optimal.prop1_LP_optimal_cheap`, grade **A**) — and the *general* claim, *"no
free classical invariant of any kind"*, whose class is still informal and which
is **grade C and not a bound**. The Euler-product sentence is the general one.

It remains the best candidate answer to *what leaves no room*. It is not a
certified one, and the difference is the whole subject of `CLAIMS.md`.

### The constitutive criterion — the substantive upgrade to E22

The atom programme asked for axioms **sufficient** for RH. The fourth approach
demands axioms that are **constitutive**:

1. provably instantiated by `ζ` (soundness);
2. provably **characterising** `ζ`, Hamburger-style — nothing else satisfies
   them, or the satisfiers form a classified family (**rigidity**);
3. jointly forcing the zeros.

`(1)+(3)` certifies; `(1)+(2)+(3)` **explains** — and the cash-out is not
aesthetic: **explanatory proofs transfer.** A constitutive axiom set forcing RH
would be a proof-schema for the Selberg class, exactly as Deligne's argument
covered every variety while Weil positivity covers nothing beyond its own
equivalence.

### The merger: E22 and E23 are one approach, two directions

The **atom** is the *why* stated as axioms. The **ladder** is the *why* stated
as the impossibility of everything why-less — each rung certifies that its class
**leaves room** (two-model arguments: the gauge pair, D–H, forcing-style). They
meet at the constitutive axiom set.

`E23m` accordingly gains the reading: **each rung certifies non-rigidity of its
class.**

### The honest boundary, kept

Necessity and provability are different — the integers are categorical while
provability is incomplete, and the gap is exactly where E23's ladder climbs. No
amount of essence-talk closes it for free. What the fourth approach changes is
the **target** of formalisation: not the zeros' location but `ζ`'s identity,
with the location as corollary. Weil's precedent says that order of operations
is not a detour; it is the only route that has arrived.

*The poetry, to be written when earned: the zeros are unbothered because they
are corollaries, and the proof will consist of saying what they are corollaries
**of**, completely enough that nothing is left for them to decide.*
