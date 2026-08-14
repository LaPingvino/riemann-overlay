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
| 11 | `#27`, **the gate** | the weighted sum amplifies each shift's error by `h`, forcing power savings; MRT supplies **log-power** — `X^θ ≪ (log X)^{A+1}` is false **at every `θ > 0`** (quarry, exp. A) | cascade | the two literatures are separated by exactly the Type II gap | cycle 11 |

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


## Quarry annotations (A3 annex) — `forensics/quarry.py`

Deliberately **not** new census entries: the quarry re-runs retracted
computations as experiments and its yield is sharper *reasons*, not more
deaths. Inflating the census would be exactly the Goodhart move the doctrine
forbids.

**On `#11` (the gate) — it is a shape gate, not a range gate.** Wildcard, kill
condition stated first: *if some `θ > 0` satisfies `X^θ ≪ (log X)^{A+1}`
asymptotically, the gate is a threshold in `θ` and the "shape not range"
reading dies.* It did not fire. For every `θ > 0` the left side is a power and
the right a log-power, so the gate fails uniformly in `θ`: **the axis the field
has advanced on for thirty years (Mikawa `1/3` → MRT `8/33`) is orthogonal to
the requirement.** Improving the shift range moves the crossover and never
crosses it.

**And the quantitative half is the find.** The failure is *purely asymptotic*.
Crossover `log X` at which the gate closes:

| θ \ A | 2 | 5 | 10 | 20 | 50 |
|---|---|---|---|---|---|
| Mikawa `1/3` | 31 | 79 | 169 | 373 | 1067 |
| MRT `8/33` | 48 | 118 | 251 | 546 | 1545 |

i.e. `X` beyond `10^13` … `10^671`. **No numerical experiment at any feasible
height could have seen this obstruction, and none could ever have warned us.**
`#27` survived a hand computation and died to a shape check — which is exactly
the disease the QUALITY rule was built for, now with a measured invisibility
radius.

**On `#9` (CMR fed back) — circular at *every* scale.** Run at window scales
`0.3, 1.0, 1.32, 1.5, 3.0`: CMR is CIRCULAR at all of them (ancestry hits
`EP1`) and additionally SCALE-invalid below `3.0`. The scales where it is
scale-valid are ones our window never reaches, and Rule 1 blocks it there too.
So the corridor is not under-fuelled from this node — it is **unfuellable** from
it, and no choice of window rescues it.

**Hypothesis-depth stratification.** 8/11 unconditional, 3/11 RH, **0/11 GRH**.
The GRH tier is empty, which is a recruitment criterion rather than a gap: a
death consuming GRH would be bridge material that changes in *more* worlds, and
we have manufactured none. *Proposed for after the freeze:* GRH as a second
flag on the guard's DAG rather than a member of `RH_CONDITIONAL`, so hypothesis
depth becomes a partial order instead of a bit.


## Guard generalisation (night cycle 2) — hypothesis depth is now a partial order

**Kill condition, stated first:** *if generalising `RH_CONDITIONAL` from a bit
to a depth order changes the T3(b) answer away from 3/11, the change has
altered a published result rather than refined it, and it reverts.*

**It did not fire.** `provenance_lint` now carries
`HYPOTHESIS_DEPTH = {RH: 1, GRH: 2}` with `RH_CONDITIONAL` retained as the
`depth ≥ 1` set, so every existing caller keeps its meaning. Re-run: changers
`[9, 10, 11]`, **3/11**, unchanged; tiers **8 unconditional / 3 RH / 0 GRH**.

**R17 witness for the green light:** `quarry.py`'s local experiment table and
the guard's new `depth()` were two independent implementations, and they agreed
exactly (8/3/0) *before* the swap. The local table has now been deleted and the
guard is the authority — the agreement is what licensed the deletion.

**And the progress axis is now a node family.** `Mikawa_third`, `BBMZ_theta`,
`MRT_8_33` are in the DAG, all three supplying `log-power`. Run against
`GM_bridge` they produce **three identical QUALITY verdicts**. Three decades of
progress, one rejection reason. The guard now says mechanically what quarry
experiment A says arithmetically: **the axis the field advances on is not the
axis the bridge bills.**


## W34d — the ladder audit (registered prediction, scored)

**The criterion is mechanical, deliberately.** An entry has a **rung** iff a
*machine-checked* statement exists of the form "no member of class `C` decides
(or exceeds) the target", with `C` explicitly named. Certificate existence is an
`#print axioms` check, not a judgement; only the class-*naming* half is
judgement, and it is marked where it matters.

Two rung genres emerged, and the distinction is not cosmetic:

* **two-model** — exhibit two structures agreeing on everything `C` sees and
  disagreeing on the target. The forcing shape.
* **capacity** — bound `C`'s optimum below the target. The LP/extremal shape.

| # | class it is independent of | certificate | genre | rung |
|---|---|---|---|---|
| 1 | single-`x` phased Landau evaluation | — | — | *candidate* |
| 2 | — | — | — | none (fate: circular) |
| 3 | cheap classical growth invariants (Jensen) | — | — | *candidate* |
| 4 | `μ_T`-invariant hypotheses | `no_muInvariant_theory_computes_NscStd`, `blind_at_every_crowded_mass` | two-model | **rung 1** |
| 5 | — | — | — | none (fate: verdict error) |
| 6 | bandwidth-one certificates | `Zeta23.PairCeiling.ceiling_law256` — axiom-free, **verified tonight** | capacity | **rung 0** |
| 7 | `μ_T`-invariant hypotheses | `no_muInvariant_bundle_computes_Noff` | two-model | **rung 1** |
| 8 | `μ_T`-invariant hypotheses, at every smoothing radius | `two_le_Hr_of_off_line` | two-model | **rung 1** |
| 9 | — | — | — | none (fate: circular) |
| 10 | `{F on [0,1], F ≥ 0}` + positivity | `Riemann/Capacity.lean` — **skeleton** certified; the *instantiation* to the actual LP is still prose | capacity | rung 0 *partial* |
| 11 | — | — | — | none (shortfall) |

**Certified rungs: 4 of 11.** Three at rung 1, all built this week; one at rung
0, and it is **imported**, not ours.

### Scoring the pre-registered prediction

Registered before the run (`LEADS.md`, SESSION 034): *has-rung / no-rung will
roughly reproduce the crystal/cascade split.*

**Confirmed in direction, and cleanly.** All four certified rungs are `crystal`;
**no `cascade` entry has one.** The defectors are `#9` and `#10` — crystal with
no certificate — plus `#5`, which is `n/a` by construction.

**No p-value, and none is available.** The sample is 10 classifiable entries and
the class-naming half was done with the prediction in hand, which is exactly the
contamination R19 exists to prevent. What is clean is the certificate half: the
theorems either exist or they do not, and that half is what carries the
direction. Note also that `#9` is the same lone crystal defector that broke the
tri-read's co-classification — it is unstable under every classifier we have run.

### The finding that was not predicted, and it is the uncomfortable one

**Rung 0 is not ours and is not certified.** `#10`'s LP-duality collapse — the
rung the ladder brief listed as *owned* — exists in this repo as **prose**.
There is no Lean statement that the class `{F on [0,1], F ≥ 0}` + positivity
fails to decide the target; the argument is written out and believed. The only
capacity certificate we can actually run is `ceiling_law256`, which came in with
zeta-23.

So the honest ladder is: **rung 1 occupied by three theorems we built, rung 0
occupied by one theorem we imported, and the rung-0 result we claimed as our own
still owes its certificate.** Filed as a debt, not a defect — the argument may
well be right; it is simply not yet a rung by this audit's own criterion.


## The rung-0 debt, partly paid (night cycle 4)

`Riemann/Capacity.lean` — 7 declarations, sorry-free, axiom-free, and it
mentions neither `ζ` nor pair correlation, which is exactly why it was reachable
without arithmetic input.

**Kill condition, stated before the file existed:** *if the statement cannot be
made without assuming the LP duality it is meant to establish, it dies and the
debt is permanent.* **It did not fire**, and the reason is worth its own line:
**no duality theorem is used at all.** The register's certified reason reads
"Lemma 1 + LP duality"; the capacity half needs neither. It is an infimum
computed directly by exhibiting the adversary's move — a fact about an order,
not a theorem about a program.

* `pinned_value_is_floor` + `pinned_value_attained` — with `K ≥ 0` outside the
  known set, the guaranteed value is **exactly** the pinned sum.
* `unbounded_below_of_neg_outside` — with `K < 0` anywhere outside, the program
  is **unbounded below**: for every target `B` there is an admissible `F`
  undercutting it. The certificate proves nothing.
* `value_eq_pinned` — both halves as one `IsGreatest`.
* `no_gain_past_known` — two multipliers agreeing on `known` guarantee **the
  same value**, however wildly they differ beyond it.

So the extension is *worthless* when nonnegative and *fatal* when not. Never
profitable. That is `#10`'s content, and it is now machine-checked.

### What is still owed, by this audit's own criterion

The class certified here is `{F pinned on a finite `known`, F ≥ 0 outside}`.
The class named in `#10` is `{F on [0,1], F ≥ 0}` — an integral program over a
continuum, not a `Finset` sum. **These are not the same class**, and the ladder
audit's criterion demands a machine-checked statement about the class actually
named.

**Honest verdict: rung 0 is `partial`, not `certified`.** The skeleton is
proved; the instantiation — the map from a bandwidth-one certificate to this
program, and the passage from `Finset` to integral — remains prose. Recorded as
`SURPRISES` S20: I expected formalising the collapse would discharge the rung,
and it discharged its skeleton.

The remaining step is measure-theoretic bookkeeping rather than mathematics, and
it is now a well-posed Lean task instead of an argument.
