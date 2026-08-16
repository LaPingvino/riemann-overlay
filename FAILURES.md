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
| 10 | `{F on [0,1], F ≥ 0}` + positivity | `Riemann/Capacity.lean` — certified over a **continuum** for the named class; the modelling map is a trusted-base question | capacity | **rung 0** |
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

> ⚠️ **Stale since `Capacity.lean` (`SESSION 128` found it in two registers at
> once).** `Riemann/Capacity.lean` carries eleven capacity theorems of our own,
> axiom-free and audited — `pinned_value_is_floor`, `value_eq_pinned`,
> `no_gain_past_known`, `unbounded_below_of_neg_outside`, their integral forms,
> and `reweighting_worst_case`. The "next rung-0 item, and it is cheap" named
> below **was done**: that is exactly what `no_gain_past_known` states. So
> `ceiling_law256` is no longer the only runnable capacity certificate, nor the
> only one we can *own*.


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

> **SCOPED, `SESSION 199`.** The sentence below is true **of the full
> admissible class** and is not true of a subclass.
> `Capacity.no_gain_past_known_fails_on_subclass` exhibits `K`, `K'` satisfying
> every hypothesis of `no_gain_past_known` — agreeing on `known`, both
> nonnegative outside — whose guaranteed values over the subclass "`F ≥ 1` off
> `known`" are `2` and `3`.
>
> The mechanism is the one `198` found from the other side: once `F` is
> constrained off `known`, the multiplier's values off `known` stop being free
> to be zeroed out, so they reach the guaranteed value. A bandwidth-one class
> carries exactly such a constraint.
>
> So what is machine-checked is the full-class statement. `#10`'s claim about
> bandwidth-one certificates is still believed and is still not proved, and the
> gap is now named twice over: `198` (the floor rises) and `199` (the no-gain
> conclusion does not transfer).

So the extension is *worthless* when nonnegative and *fatal* when not. Never
profitable. That is `#10`'s content, and it is now machine-checked.

### What is still owed, by this audit's own criterion

The class certified here is `{F pinned on a finite `known`, F ≥ 0 outside}`.
The class named in `#10` is `{F on [0,1], F ≥ 0}` — an integral program over a
continuum, not a `Finset` sum. **These are not the same class**, and the ladder
audit's criterion demands a machine-checked statement about the class actually
named.

> **DISCHARGED, `SESSION 193` (2026-08-16).** The "partial" verdict below is
> stale. `Riemann.Capacity.value_eq_pinned_unit_interval` states the collapse
> for `α = ℝ`, `A = Set.Icc 0 1`, `μ = volume` — the class `#10` actually
> names — and is axiom-free (`propext, Classical.choice, Quot.sound`). It is a
> specialisation of `value_eq_pinned_integral`, which was already stated over an
> arbitrary measure space, so nothing new was proved today; what was missing was
> the *instantiation*, and that is exactly what this register said was owed.
>
> Scope of the discharge, stated narrowly: the theorem covers the pinning-and-
> nonnegativity structure of `#10`'s class. The other half of the "what is
> still owed" paragraph — the map from a bandwidth-one certificate into this
> program — is **not** discharged and remains prose.

**Honest verdict: rung 0 is `partial`, not `certified`.** The skeleton is
proved; the instantiation — the map from a bandwidth-one certificate to this
program, and the passage from `Finset` to integral — remains prose. Recorded as
`SURPRISES` S20: I expected formalising the collapse would discharge the rung,
and it discharged its skeleton.

> **CORRECTED, `SESSION 198`.** The sentence below is wrong about what is left.
> The `Finset`-to-integral passage it had in mind was indeed bookkeeping and was
> done in `193`. The *other* half — the map from a bandwidth-one certificate
> into this program — is **not** bookkeeping, and
> `Capacity.subclass_floor_strictly_above_pinned` is the reason:
>
> `pinned_value_is_floor` computes a floor over `Admissible known F₀`. A
> bandwidth-one class is a **subclass** of that, carrying a Fourier-support
> constraint on top. A floor is an infimum, and an infimum over a smaller class
> can be larger — the theorem exhibits a two-index case where restricting the
> class raises the floor strictly. So the capacity results bound the
> bandwidth-one program from below and do not compute it.
>
> What the map needs, named: a Fourier-support notion and a pair-correlation
> form factor. A grep of `Riemann/*.lean` for `Fourier`, `bandwidth`,
> `formFactor` and `pairCorrelation` returns prose mentions in
> `Blindness.lean:35` and `Basic.lean:378` and no declaration. The debt is
> therefore **blocked on a named analytic input**, which is a better status
> than "owed" and a worse one than "bookkeeping".

The remaining step is measure-theoretic bookkeeping rather than mathematics, and
it is now a well-posed Lean task instead of an argument.


## Rung 0, certified over the continuum (night cycle 5)

**Kill condition, stated before the section existed:** *if the integral
machinery forces a side-condition that is itself the disputed content, the
instantiation dies and rung 0 stays partial.* **It did not fire.** The only
side-conditions are `MeasurableSet A` and integrability of the integrand —
facts about whether the symbols denote anything, not about whether extending
support helps. No hypothesis is placed on `K` outside `A` beyond the sign
condition that is the theorem's own.

`value_eq_pinned_integral` and `no_gain_past_known_integral` (axiom-free): for
any measurable `A` — `[0,1]` included — the guaranteed value is exactly the
pinned integral, and **two multipliers agreeing on `A` guarantee the same value
however they differ outside it.**

**The class now matches the one `#10` names.** What remains unformalised is the
*modelling map*: bandwidth-one certificate `↦` multiplier `K`, and proportion
bound `↦` program value.

**And that gap is not a new debt — it is the project's existing boundary.** It
is the same species as the nine constants in `Assumptions.lean`: the place where
our mathematics meets the literature's setup. Recording it as such rather than
as an open item, because the alternative is an infinite regress in which no rung
is ever certified. **Rung 0 is ours, at the same standard as everything else on
the certified row.**


## Census `#10`, fully certified (night cycle 6)

The continuum section proved extension **useless**; it had not proved it
**harmful**. `unbounded_below_of_neg_outside_integral` closes that half,
axiom-free.

**Kill condition, stated first:** *if stating it requires a hypothesis that
already assumes the conclusion, it dies and "harmful" stays `Finset`-only.* **It
did not fire.** The hypothesis is `∫_E K < 0` for some measurable `E ⊆ Aᶜ` with
`K` integrable there — "there is a place outside the pinned range where the
multiplier is negative on average", which is precisely the situation being ruled
out, not the ruling itself. The witness is explicit: pin `F` on `A` and add a
constant bump `t` on `E`; the value is `P + t·∫_E K`, which runs to `−∞`.

**So census `#10` now reads, entirely in the kernel:**

> extension past the known range is **useless** when the multiplier is
> nonnegative outside (`no_gain_past_known_integral`) and **fatal** when it is
> negative on average anywhere outside
> (`unbounded_below_of_neg_outside_integral`). **Never profitable.**

Both halves hold for any measurable `A`, `[0,1]` included, and neither mentions
`ζ`.


## A second docstring promoted to a theorem (night cycle 7)

The ladder audit's standard — *a claim about what a class cannot do needs a
machine-checked statement, not a docstring* — was aimed at census entries. Turned
on our own `Gauge.lean` docstring it found the same disease: **"no linear bound
`Nsc ≥ αN + βN⊛` beats `(2,−1)`"** was prose, with only a single tightness
witness proved.

`Riemann/Optimal.lean` (axiom-free) fixes that with exactly two configurations:

* a single simple on-line zero (`N=1, N⊛=1, Nsc=1`) forces `α + β ≤ 1`;
* the lone mirror pair (`Gauge.pairOnly`: `N=2, N⊛=4, Nsc=0`) forces
  `α + 2β ≤ 0`.

Those two already give `α + βC ≤ 2 − C` throughout `1 ≤ C ≤ 2`, attained by
`(2,−1)`. **Kill condition** — that two configurations would not suffice —
**did not fire**.

**And the certified statement is stronger than the prose it replaces:** no sign
hypothesis on `β` is required. I had written `β ≤ 0` into the theorem as an
obvious precondition; Lean's *unused-variable linter* pointed out the proof
never touched it (`SURPRISES` S21).

So the register's standing consequence is now load-bearing rather than
asserted: **improving Proposition 1 requires leaving the two-moment world** — a
third moment `Σ m³`, which is [OPEN D]'s currency. The reduction and the ceiling
want the same missing input, and that sentence now rests on a theorem.


## W32 — the census as atom unit-tests. Run, and the coverage is the finding.

**Kill condition, stated first:** *if every entry needs both bundles, the test
has no discriminating power and W32 dies.* **It did not fire** — but what
happened instead is more informative than either branch.

Bundles per `forensics/W28_atom_interface_cold.md`: **M** = the multiplicative
nature (free monoid, `Λ ≥ 0`, Euler product, explicit formula); **S** = the
sieve nature (Type I/II, level of distribution, short intervals).

| # | which bundle would a fix have needed? | basis |
|---|---|---|
| 1 | **M** — Landau sums are built from `Λ`; the fix wanted is correlated control of them | judgement |
| 2 | **neither** — circularity is a logic defect, not a supply shortfall | forced |
| 3 | **M** — *"only the Euler product bites"* is the certified reason verbatim | forced by the entry |
| 4 | **neither** — an *information* limit; `Blindness.no_muInvariant_theory_computes_NscStd` | **theorem-backed** |
| 5 | **neither** — a verdict error | forced |
| 6 | **neither** — class capacity; `Zeta23.PairCeiling.ceiling_law256` | **theorem-backed** |
| 7 | **neither** — `Fiber.ledger_visibility_split`: `N_off` is not a `μ_T` functional at any order | **theorem-backed** |
| 8 | **neither** — `Blindness.two_le_Hr_of_off_line`: structural, at every radius | **theorem-backed** |
| 9 | **neither** — circularity plus scale | forced |
| 10 | **neither** — `Capacity.no_gain_past_known_integral`: a capacity fact about the class | **theorem-backed** |
| 11 | **S** — the bridge wants a power saving from the sieve side | forced by the entry |

**Tally: M = 2, S = 1, neither = 8. No entry needs both.**

**So the test discriminates — and it classifies only 3 of 11.** The atom bundles
sort *supply* failures, and **eight elevenths of this census is not about supply
at all**: it is information limits, capacity limits, and logic defects. Five of
those eight are now theorem-backed rather than judgement, which is why the
attribution is defensible where the earlier plane-classification was not.

**Consistency check, unplanned and worth recording:** this `3 : 8` split lines
up with T3(b)'s `3 : 8` (RH-consuming vs unconditional) and with
`ledger_visibility_split`'s `2 : 3`. The entries that need an arithmetic bundle
are the entries that consume a hypothesis; the entries that need neither are the
ones whose obstruction is a property of the instrument. **Three independent
classifications of the same eleven objects agree on where the line falls.**

**Consequence for W28's interface:** an `Atom` structure supplying M and S
addresses **2/11 and 1/11** of the recorded difficulty respectively. The
interface is worth having for what it makes statable, not as a route to the
census's main mass — and nothing in the atom programme was ever going to touch
the eight.

*Contamination note, per R19: this is a per-entry attribution, not a
pattern-claim, and the five theorem-backed rows are not judgement at all. The
three judgement rows (1, 3, 11) are marked as such. No p-value is quoted and
none is available.*

---

## W19 — Fujii/Selberg S-moments as a haunted-density bound. Dead, and the margin is `√(log log T)`.

**Kill condition, as filed (`143`):** *if the published error term in the
`2k`-th moment formula for `S(t)` is `Ω(T)` — larger than the `2δL` signal a
haunted density produces — then no such identity can see haunted mass at any
`δ`, and W19 dies at the supply rather than at the scale.* **It fired.**

**The route.** `Fiber.six_mul_haunted_le_factMoment_three` gives
`6·hauntedCount ≤ Σ H(H−1)(H−2)`; a bound feeds `HauntedDensity` and hence
`proportion_of_hauntedDensity`. `143` measured what the ledger's own quantity
does to an S-moment: a mass-`3` ordinate perturbs `∫S²` by exactly `2δL`
(`forensics/w19_price.py`), a term with **no `log log T`**.

**The supply, read off displayed formulas** — Chirre–Quesada-Herrera,
arXiv:2006.08503 §1.2:

| source | condition | error term | verdict |
|---|---|---|---|
| Selberg 1946, their (1.4) | **unconditional** | `O(T·√(log log T))` | swamps `2δL` for every `δ`, every `T` |
| Selberg, their (1.4) | RH | `O(T)` | swamps `2δL` for small `δ` |
| Goldston 1987, their (1.8) | RH | **`o(T)`** | precise enough — and useless |

**Why the one that works is useless.** RH gives `Noff = 0`; `Noff = 0` gives
`NoHaunted` by `Fiber.noHaunted_of_Noff_zero` (axiom-free, in this repo). So
`hauntedCount = 0` identically in **every** world where the identity precise
enough to bound it becomes available — an implication only, since
`Fiber.noHaunted_not_imp_Noff_zero` puts `NoHaunted` in strictly more worlds
than RH. **The want-ad is filled only where the
goods are worthless.**

**What the death is worth.** Not "the moments are too weak" — a *located*
margin. The whole distance between a live route and a dead one is the
`√(log log T)` separating Selberg's unconditional error from Goldston's
conditional one. That is the smallest gap any route in this census has died in,
and it is the reason the numerics at `T ≈ 7.5×10⁴` looked so encouraging
(`11.2·δ`, `143`): the signal really is loud, and the error bars are louder.

**A shared input, noted and not overread.** (1.8)'s second-order constant is
built from `∫₁^∞ F(α)/α² dα` — the pair-correlation form factor on `[1,∞)`,
which is the corridor `PRICES.md` prices and `LEADS`:623 calls "certified bare"
past `A`. The S-moment route and the corridor route consume the **same**
unavailable input. Recorded as a shared dependency, **not** as an identity of
routes: that would be the `S30` shape.

*Scope: only `k = 1` was fetched. Higher-`k` asymptotics and their error terms
remain `[RECALL, UNVERIFIED]` and carry no part of this verdict.*
