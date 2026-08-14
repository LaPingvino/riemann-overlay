# FAILURES — the census (W∞, T1)

Every death, with its certified reason. Raw failure is inert; **"fails BECAUSE
P" is the asset.** An entry whose `certified reason` cannot be filled is not
enriched and goes back to the refinery.

**Schema:** `id | attempt | certified reason | plane | what it fingerprints | source`

`plane`: `crystal` (foundational face) · `cascade` (generative face) ·
`off-plane` · `n/a`. **See the contamination note at the bottom before reading
this column as evidence.**

| # | attempt | certified reason | plane | fingerprints | source |
|---|---|---|---|---|---|
| 1 | W16, Landau sums, single `x` | signal clears error by orders of magnitude; **phases shared with the on-line chorus** — no separation at one `x` | cascade | the ledger is loud but unseparable pointwise | pencil pass, cycle 2 |
| 2 | W6, equidistribution half | **circular**: bounding ordinate coincidences needs the zeros distinct | cascade | exact coincidence is not approachable from counting | cycle 1 |
| 3 | W7, realizability | extremal configs use `m ≤ 3`; Jensen permits `~log γ` — **vacuous by an order of magnitude**; only the Euler product bites | cascade | cheap invariants are satisfied *by construction* | cycle 4 |
| 4 | W8, container run backwards | `TightMult`: the certificate **provably cannot separate** a double zero from an off-line pair at depth → 0 | crystal | `H(γ)` fuses the two failure modes because the information forces it | source read |
| 5 | W4 (first verdict) | wrong: killed against one container, resurrected as CGdL 2018 | n/a | *kill conditions are container-local* | dispatch |
| 6 | W11, "does GUE saturate?" | mis-posed: the ceiling is **class capacity**, not an input property; 18.18pp is pure instrument | crystal | every constant measures the aperture | cycle 3 |
| 7 | W12, depth-shaped input | price **exactly zero**: `N⊛` is depth-blind, `μ_T` has no `β` coordinate | crystal | horizontal info enters only via counting | cycle 6 |
| 8 | A2, fatten the atoms | **forced**: the mirror preserves ordinates exactly, so no vertical smoothing separates a zero from its twin | crystal | resolution is not a free parameter | Lean, cycle 5 |
| 9 | `#24`, CMR constant fed back | **circular** (one extremal problem, two faces) **and scale-mismatched** (asymptotic in `ℓ`) | crystal | class outputs cannot be class inputs | cycle 8 |
| 10 | `#25`, class walls past support 1 | Lemma 1 + LP duality: optimum snaps to `λ = 1`, Montgomery's `2/3` — extension is *harmful* | crystal | two-sidedness must enter through the **inputs** | cycle 9 |
| 11 | `#27`, **the gate** | the weighted sum amplifies each shift's error by `h`, forcing power savings; MRT supplies **log-power** — `X^θ ≪ (log X)^{A+1}` is false | cascade | the two literatures are separated by exactly the Type II gap | cycle 11 |

## Contamination note — read before using the `plane` column

The alignment `11/11` **is not a measurement**, because I classified these
entries *knowing the hypothesis*, and for each one I chose which half counts as
"succeeded" and which as "failed". With two or more defensible readings per
entry, alignment is close to guaranteed by construction. The naive figure
`2⁻¹¹ ≈ 5×10⁻⁴` is arithmetic, not evidence.

**De-contamination protocol, required before any p-value is quoted:**

1. **Pre-register the classification rule** — what counts as the succeeded half,
   in schema terms, with no reference to crystal/cascade.
2. **Blind classification** — a party without the hypothesis (a Fable agent
   given only the schema and the rule) assigns the halves.
3. **Only then** score alignment against the plane, and only entries where the
   blind and hypothesis-aware classifications agree count as data.

Until that runs, E20's pattern is *suggestive and unmeasured* — which is exactly
what W26's T1 taught about the historical sequence, now aimed at our own record.


## T3(b) — the ¬RH rubric, answered mechanically

Three-valued per the amended schema: `survives` · `changes-numerically` (same
failure, different constants) · `changes-structurally` (the failure does not
exist as stated). **The authoritative answer is the lint's, not anyone's guess**
— `provenance_lint.py` marks RH-conditional nodes and propagates the flag:

| # | death | consumes RH via | rubric |
|---|---|---|---|
| 1–8 | (all) | — | **survives** |
| 9 | `#24` CMR fed back | `CMR_1.3208` | **changes-structurally** |
| 10 | `#25` LP collapse | `Lemma1_cap3` | **changes-numerically** (discriminator half is class-derivable and survives; the cap `3` is RH) |
| 11 | `#27` the gate | `GM_bridge` | **changes-structurally** |

**3/11 are bridge material.** The census is **73% instrument.**

**Scoring round 1: my sealed prediction was 2, the mechanical answer is 3,** and
the extra entry is `#27` — the one I was most confident about. The gate's
*comparison* (log-power < power) is unconditional, but what it compares against
is the GM bridge's requirement, and that bridge is RH-conditional: in a ¬RH
world the failure does not exist as stated. Sealed hash of the prediction file:
`5d385586e174ddc4`.

## T2 RUN — and the alignment is **not confirmed**

The de-contamination protocol was executed, not proposed: a Fable agent received
the eleven attempts with their certified reasons, all crystal/cascade language
stripped, no hypothesis supplied, and was asked to sort them into **two groups
of its own devising**.

**It produced a different dichotomy:**

* **Group A — insufficient resolving power** (the tool cannot make the required
  distinction): 1, 3, 4, 7, 8, 11
* **Group B — circular / self-referential information** (the input was
  downstream of what it was trying to establish): 2, 5, 6, 9, 10

Against my plane classification, under the best mapping (`cascade ↔ A`),
agreement is **6/10 — chance is 5/10.**

> **The census does not independently support E20's plane.** The `11/11`
> alignment was an artefact of classifying with the hypothesis in hand, exactly
> as the contamination note feared. No p-value is available and none should be
> quoted.

**This does not refute E20** — the plane was derived from the *mathematics*
(X, TightMult, W12, W7 converging), not from this census, and that derivation
stands untouched. What dies is the claim that the failure record is *evidence*
for it. E20 reverts to: a structural reading with four independent derivations
and **zero** statistical support.

## T2b — a third independent read (context v2, the compaction dividend)

A post-compaction operator — knows the mathematics, does not remember the
battles — was handed columns 1–3 only (`awk`-extracted, so `plane` and
`fingerprints` were never rendered) and asked for its own categories before
reading E20, A3, or the rubric. Sealed at `460ccd415bc031e1`; comparison in
`forensics/tri_read_comparison.md`.

Its axis is **coupling**: `FUSED` {1,2,4,7,8,9} (the discriminant is a function
of things that move together; circularity is the limiting case) · `SLACK`
{3,6,10} (the container admits orders of magnitude too much to bite) ·
`SHORTFALL` {11} (correctly coupled, supply short by a growth class) ·
`verdict error` {5}.

**Co-classification across all three reads leaves exactly two clusters:**
`{4,7,8}` — what the functional cannot see — and `{6,10}` — what the class
cannot exceed. **X and the ceiling, and nothing else.** Three axes, one of them
amnesiac, recover only the two objects the project already treats as primitive.

**Asymmetry worth more than the clusters:** 5 of 6 `crystal` entries sit in a
stable cluster; **0 of 4** `cascade` entries do. Stable reasons are statements
about a *fixed object* (this functional lacks this coordinate); disputed reasons
are statements about an *argument's fate* (the bound was vacuous, the supply was
short). Only object-statements are census-gradeable. *Candidate rule — not
adopted this cycle:* mark each entry `object` / `fate` and exclude `fate`
entries from pattern-claims. Held pending Joop, per the re-entry protocol's
freeze on doctrine edits.

**The blind was partial and the sealed file overstates it** (audited before
dispatch, file not edited — the hash outranks the wording). Three exposure
channels: a schema-learning `grep` rendered rows 1–2 with their plane column;
the compaction summary carried E20's plane, the T3(b) verdicts, and
cause-language for `#24`/`#25`/`#27`; the dispatch named the 73% figure.
**Genuinely blind subset: 3–8.** `{4,7,8}` lies wholly inside it, so the
headline cluster passed a *harder* test than claimed; `{6,10}` is half-clean;
the `#11` claim below is downgraded to hypothesis-aware. Second consecutive
cycle in which a blind leaked through an instance being useful — the
generalisation is that **orientation is an exposure channel**.

**Three claims the third read makes that neither prior read contains:** `#11`
is `sui generis` (not a resolution failure — the only death whose exit is
external arithmetic supply); `FUSED` and `SLACK` have antagonistic remedies, so
the record should oscillate rather than accumulate; and the `FUSED` bin is a
harvested list of six conserved quantities, which is what `S`/A9c has been
searching for from the other end.

**And the blind result is a finding in its own right.** An unprimed classifier
looking at our eleven deaths sees, as the dominant axis, **circularity** — five
of eleven failures are the input being an output. That is a fact about *our
method*, not about `ζ`: the project's most common failure mode is feeding the
machinery its own exhaust, and R18's condition (2) was written after the fourth
instance rather than the first.
