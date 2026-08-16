# ISSUES — the friction log

Bins: **1** translation bug (Claude stated it wrong) · **2** Mathlib gap
(statement right, infrastructure missing) · **3** genuine hole (the claim
cannot be made precise because it is fuzzy — the treasure).

---

## #1 — [bin 3] The δ₀ interface: exceptional set vs. universal quantifier

**Predicted in the briefing as Doubt 3, and confirmed.**

[OPEN A′] delivers `DensityNearLine F M`:

```
∀ δ > 0, eventually  #{ρ : |β-½| ≥ δ/log T} ≤ M δ · N(T)
```

a *counting* bound. The BGST narrow-box theorems assume `NarrowBox F b`:

```
eventually  ∀ ρ ∈ Z,  |β-½| ≤ b/log T
```

a *universal* statement with **no exceptional set**. These do not compose:
`M δ = 0` is what would be needed, and Route III cannot deliver that — the
whole point of the flow argument is that some zeros survive.

What typechecks (`Program.routeIII_partial`, proved): `DensityNearLine F M`
⟹ `NarrowBoxExc F δ (M δ)`, the narrow box *with* an exceptional set of
relative size `M δ`. The arrow from there into `narrowBox_starBound` is
missing and cannot be manufactured **from `DensityNearLine` alone**.

> ⚠️ **Scoped, `SESSION 173`.** As first written this said "cannot be
> manufactured", full stop, and `Program.routeIII_via_A''` manufactures it —
> from `NarrowBoxTolerant` plus an explicit fitting condition. The intent was
> always "not without a further hypothesis", which is what the *next* paragraph
> then supplies; the sentence just did not say so. `S34`'s shape: an unscoped
> absolute in load-bearing prose, correct in intent and wrong as written.

**Minimal strengthening needed.** Either
(a) an [OPEN A″]: the BGST proof re-run with an exceptional set of `≤ η·N(T)`
zeros outside the box, with the conclusion degraded to `C = 4/3 + f(η)`,
`f(η) → 0`; or
(b) a Route III output with `M δ₀ = 0` for some fixed `δ₀`, i.e. a genuine
zero-free region — much stronger than what the heat flow gives.

**Correction (same session, after review).**  A first version of this note
claimed that `N + N_off ≤ N⊛` makes (a) cheap: "an exceptional set of size
`η·N` costs at most `η` in `C`".  That is a **direction error**.
`N_add_Noff_le_Nstar` is a *lower* bound on `N⊛`; capping the exceptional
set's contribution needs an *upper* bound on `Σ_{ρ exceptional} H(γ_ρ)`, and
`H` is unbounded without a per-ordinate multiplicity input.

The salvageable statement carries that input explicitly: **if `H(γ_ρ) ≤ m`
for the exceptional zeros, an exceptional set of relative size `η` costs at
most `η·m` in `C`.**  A cap `m = O(log T)` is classical but is `o(N)`-useless
at this normalisation, so what [OPEN A″] really needs is a bounded-`m` cap on
the exceptional set — which the flow argument may well supply, since a zero
that survives to flow-time `t` is isolated at scale `≈ t·log T`.  That is a
genuine question, not a free lunch.

## #2 — [bin 1] [OPEN B] is not open — **retired by Errata 1 E1**

The program document calls [OPEN B] ("de-condition Farmer–Gonek–Lee for
`ξ′`") "the most tractable gap". It is already done, in the very artifact
the document cites: `zeta-23-lean/Zeta23/XiPrime/` proves, unconditionally
and sorry-free, that at least **0.85838** of the zeros of `ξ′` in `(T, 2T]`
are simple and on the critical line (0.86864 with the quartic window), by
applying the rank–trace device to the Farmer–Gonek(–Lee) argument.

**Fix.** [OPEN B] is closed; the remaining Route II gap is the *transfer*,
not the derivative-side theorem — see #3. Recorded as
`Assumptions.zeta23_xiPrime` and `Program.routeII_xiPrime`.

## #3 — [bin 3] The `λ` at which close pairs appear is not free

`ClosePairLowerBound closePairs F lam c₁` carries a `λ`. In Proposition 2 the
close-pair integral is subtracted at the *same* `λ` at which `Cbound c₀ λ` is
evaluated, and `Cbound` is optimised near `λ ≈ 0.6–0.9`. Farmer–Ki (and the
small-gap literature generally) *produce* close pairs at a `λ` of their own
choosing — typically much smaller.

The prose "subtracts `c₁` directly from `C`" is therefore only true under a
`λ`-uniformity that nobody has stated. `Program.routeI_closePairs` is stated
at `λ = 9/10` precisely so that this is visible in the type;
`Program.routeII_gap` returns an *existential* `λ`, and the two do not meet.

**Minimal strengthening.** A `λ`-uniform close-pair lower bound, or a version
of Prop 2 in which the close-pair mass at small `λ` still helps at large `λ`
(monotonicity of `α ↦ 𝒩(α)` gives some of this for free and should be
checked — cheap, not yet done).

## #4 — [bin 2, RESOLVED session 003] Toolchain split with zeta-23-lean

`zeta-23-lean` is Lean `v4.33.0-rc2` / Mathlib `51e6992…`; this project is
`v4.24.0`. Importing it (rather than axiomatising `baseline_zeta23`) means
bumping this project, re-fetching the Mathlib cache and building `Zeta23`
(8890 jobs incl. Mathlib). No mathematical obstacle; it is the top
infrastructure task, and it *removes an axiom without moving the score* —
the metric is designed to show that as progress.

## #5 — [bin 1, resolved] Multiplicity conventions

Doubt 2, resolved by choosing: `ZeroData.Z` is a multiset in which a zero of
order `m` occurs `m` times. zeta-23-lean instead weights by
`analyticOrderAt`. The translation, when the two meet, is
`Σ_{ρ distinct} ord(ρ)·f(ρ) = Σ_{ρ ∈ Z} f(ρ)`; it is a `Multiset` /
`Finset.sum`-with-weights identity, elementary but not yet written down.
Filed as a to-do rather than an open problem.

## #6 — [bin 1?] Doubt 1: does effective Fujii alone give anything?

Status: **the derivation does go through as an inequality, and the numbers
are now explicit** (`Riemann/Fujii.lean`):

* an admissible `c₀` is forced to be `≥ 0.16` (proved);
* `c₀ ≤ 0.8` gives a positive proportion (proved);
* `c₀ ≤ 0.33` beats 0.6725 (proved).

So the reason GLSS state no such corollary is *not* that the reduction fails;
it is that the currently provable `c₀` — which nobody has computed — is
presumably well above 0.855. The gap is now a concrete arithmetic target
rather than a vague "make it effective".

**Caveat — largely discharged (session 004 wildcard).** The shape has now
been checked against the paper's **own displayed equation (6.2)**, quoted in
STATEMENTS.md, and independently re-derived here from Riemann–von Mangoldt +
Fujii's Proposition 2 without reference to GLSS §6. Both give

`N⊛ + (2/λ)∫₀^λ 𝒩 = TL(λ + log(2+λ)/(π²λ) + O(√log(2+λ)/λ))`,  `0 < λ² ≤ L`,

and the paper states Proposition 2 as unconditional ("depends on an
unconditional explicit formula of Selberg for `S(t)`"). The `λ`-range is
asymptotically permissive, so `λ ∈ {0.462, 0.61, 0.9}` are all admissible.

Residual risk is now narrow and named: the cross term and edge terms of the
re-derivation are asserted to be lower order rather than proved, and the
fetch itself is machine-mediated. The human task is reduced from "audit a
reading of §6" to "look at one displayed equation".

## #7 — [bin 1, fixed in the docstring; still an over-strong axiom] Proposition 1 read backwards is not a theorem

`zeta23_xiPrime` converts "0.85838 of `ξ′`-zeros are simple and critical"
into `(★)` for `ξ′` with `C' = 1.14162`. That is Proposition 1 read
*backwards*, which is **not** a theorem: `N_sc ≥ 2N - N⊛` does not give
`N⊛ ≤ 2N - N_sc` unless the zeros counted by `N_sc` are exactly those with
`H = 1`. For `ξ′` (whose zeros are not reflection-symmetric in the same way)
this needs its own argument. Currently absorbed into the axiom; should be
split into (i) the cited zeta-23 statement and (ii) the conversion lemma.


## #8 — [bin 3] Axiomatising a literature theorem over an *abstract* family asserts too much

**Found by review on 2026-08-13, after the first green build; the trusted
base was inconsistent.**

The first `Assumptions.lean` declared, among others,

```lean
axiom farmer_ki (closePairs : ℝ → ℝ → ℝ) (F F' : Family) (M : ℝ → ℝ) :
  DensityNearLine F' M → ∃ lam > 0, ∃ c₁ > 0, ClosePairLowerBound closePairs F lam c₁
```

quantified over an *arbitrary* `closePairs` function.  Instantiate
`closePairs := fun _ _ => 0` and `M := fun _ => 1` (`DensityNearLine F 1` is
provable for every family: a filtered multiset is no larger than the whole).
The conclusion then says `c₁·N(T) ≤ ε` eventually for a positive `c₁`, while
`Family.nonempty` says `N(T) ≥ 1` eventually.  `atTop` is `NeBot`, so:
`False`.  Verified — `audit/regression/Boom_2026-08-13.lean` compiled and
produced `theorem boom : False`.

Three further axioms had the same disease:
* `fujii_with_closePairs` — `closePairs := fun _ T => K·N(T)` makes the
  hypothesis free for every `K`, so `C ≥ K + 1` for all `K`;
* `narrowBox_starBound` and `zeta23_xiPrime` — quantified over every
  `Family`, refuted by the family "ten copies of `(1/2, 0)`": all zeros on the
  line (so `NarrowBox` holds) yet `N⊛/N = 10`.

**Root cause.**  BGST, Farmer–Ki and zeta-23 are theorems *about `ζ`*, whose
truth uses Riemann–von Mangoldt density and the Euler product.  Asserting
them for an arbitrary reflection-symmetric multiset family asserts them for
adversarial models where they are false.  `#print axioms` does not catch
this: it audits proof cones, not the satisfiability of the base.

**Fix (applied).**  An axiom may only speak about the fixed constants
`zetaFamily`, `xiPrimeFamily`, `closePairsZeta`.  The three bridges are now
`Prop`s in `Gaps.lean` (`ClosePairBookkeeping`, `FarmerKiTransfer`,
`BGSTNarrowBox`), carried as hypotheses in `Program.lean` — the same
discipline the briefing imposes on open problems.  The arrows still compose;
`audit/regression/Boom_2026-08-13.lean` no longer typechecks, and that file is
kept as a regression: **it must never compile again.**

**The general lesson**, which applies to this whole project and is worth more
than the fix: *any* statement in `Gaps.lean` quantified over `Family` may be
much stronger than the literature theorem it is named after, and there is no
mechanical check for it.  L3 of the leads file (Davenport–Heilbronn as a
negative control) is exactly the right standing test — a bridge that is true
for arbitrary families would "prove" too much for Davenport–Heilbronn too.


## #9 — [OPEN B″], the λ-uniform Farmer–Ki (Errata 1, E3) — **opened**

Route II's gap is the transfer, not the derivative side. Required shape, now
in Lean as `Gaps.LambdaUniformFarmerKi`:

> for every `λ` in a range covering the `Cbound` optimum (≈ 0.6–0.9), the
> close-pair mass of `ζ`-zeros at normalised distance `≤ λ` is bounded below
> by an explicit function of the `ξ'` near-line count, **uniformly in `λ`**.

`Program.routeII_via_B''` (proved) shows the new shape *does* compose into
Route I, where `Program.routeII_gap` — the existential-`λ` form that
Farmer–Ki actually gives — does not. The phrase "subtracts `c₁` directly
from `C`" is retracted.

**Standing pattern, second confirmed instance** (after #1/#3): *a constant
produced at a scale the consumer did not order*. Now a review question for
every remaining interface, and a named field in the three-column testbed:
when a numerical check passes, **record at which parameter values it passes**.

Backward-transfer framing: [OPEN B″] is the `m = 1` case of the backward
transfer that blocked the Conrey-1983 program (LEADS L1).

## #10 — [OPEN A″], exceptional-set-tolerant narrow box (Errata 1, E4) — **opened, ahead of A′**

`Gaps.NarrowBoxTolerant`. Either (a) rerun the 2501.14545 proof tracking an
exceptional set of size `E(T)`, finding the largest `E(T)` it survives, or
(b) an interpolation device turning "all but `E(T)` zeros in the box" into a
weighted hypothesis the existing theorem accepts.

`Program.routeIII_via_A''` (proved) composes it — **with a fitting condition
the prose does not have**: `NarrowBoxTolerant` hands out a box width `b` and
an allowance `η`, and [OPEN A′] must satisfy `M δ ≤ η` for some `δ ≤ b`.
Since `M` is *decreasing* in `δ` (a larger `δ` counts fewer zeros), the
binding case is `δ = b`: the density function must be small **at the BGST box
scale**, not merely in the limit `δ → 0`. Third instance of the scale pattern.

Route III is blocked behind A″ regardless of [OPEN A]/[OPEN A′] progress; A″
is a proof-audit of an existing paper, cheaper than new analysis, and it also
serves any other supplier of exceptional-set statements (LEADS L2/Brown).


## #11 — [E2, answered; import live since session 003] The `XiPrime` Hilbert–Schmidt layer is **factored**, not baked in

Read of `zeta-23-lean/Zeta23/XiPrime/` (session 002). The second-moment layer
is a named, reusable definition, and it is factored at the seam Route II
wants:

* `jWin D lam v = 2∫₀¹ D(lam·r)·(v⋆v)(r) dr` — the pair-correlation
  consumption, standalone;
* `cWin D lam v = lam(∫v)²/(∫v² + lam·jWin D lam v)` — the container,
  parameterised by kernel **and** window;
* `D1` — the `ξ'` form factor (Farmer–Gonek's `F₁` minus its `T^{-2α}log T`
  term) in closed form, with a certified polynomial truncation;
* the endgame (`Assembly.lean`, `Final.lean`) consumes only the interface
  `Prop`s `CertFlat` / `CertQuartic`. Nothing is buried in it.

**Consequence for Route II.** The refactor I costed as "the new Route II
workpackage" is not needed: the `ξ'` pair-correlation input this project wants
for a `(★)`-analogue already exists as `jWin D1`. The remaining work is to
state the `(★)`-analogue against it — i.e. `UnconditionalFGL` may be provable
from imported zeta-23 material rather than assumed. That reorders the plan:
**the zeta-23 import (ISSUES #4) now unblocks Route II directly**, not just
the baseline axiom.

R2 note (LOOP.md): this clears the hole Route II was waiting behind. Route III
still waits on [OPEN A″].


## #12 — [session 003, wildcard] The second-moment ceiling is the constraint `λ ≤ 1`, and its shadow price is steep

See `LEADS.md` "Session-003 wildcard". Optimising the window exactly (a linear
solve, not a search) gives `2 − 1/c*(1) = 0.6725126` — the Montgomery–Taylor
constant — and `0.795 / 0.854 / 0.888` at `λ = 1.25 / 1.5 / 2`.

Two consequences worth carrying:
1. **The `v` slot is saturated.** Nothing post-1974 can be ported through
   window shape — and the dispatch of 2026-08-13 confirms it from the other
   side: the actual donor [CGdL20] reaches 0.679 by optimising the test
   function in *Montgomery's method* (the `r`-weighting class), landing in the
   0.6725 → 0.68183 gap this sweep predicted, not by reshaping `v`.
2. **[OPEN D] now has a price tag.** The first 0.25 of extra support in
   `F(α,T)` is worth ~12pp — an order of magnitude more than everything else
   on the board combined. If a route ever produces even a sliver of support
   past `|α| = 1`, it dominates.

AH-oracle (L8) autopsy of the *negative* half — "why can't we just take
λ > 1": the mechanism that fails is exactly the one AH is invisible to, so
this is `correlated`, as expected. The interesting part is that the *cost* of
being `correlated` is now measured rather than asserted.


## #13 — [bin 1, **CLOSED**] `Nsc` (H = 1) vs `NscStd` (multiplicity 1): the baseline axiom asserts more than zeta-23 proves

> ⚠️ **Header corrected `SESSION 122`.** It read *"only the axiom restatement is
> still Joop's"* long after the restatement landed: `baseline_zeta23` and
> `baseline_przz` are both stated on `ProportionStd` (the `NscStd` count) today.
> And the mathematical residue is now named: `Fiber.Nsc_eq_NscStd_iff_noHaunted`
> proves the two notions coincide **iff** no ordinate is haunted, so `#13` is not
> a convention question but the project's central open quantity.

Found in session 003 while reading `zeta-23-lean/comparator/ChallengeDeps.lean`
to prepare the import — i.e. *before* the import landed, which is R1 working.

```
zeta-23:  N0simple(T₁,T₂) = #{ρ : ζρ=0, 0<Re ρ<1, T₁<Im ρ≤T₂, Re ρ = 1/2, zeroMult ρ = 1}
ours:     Nsc             = #{ρ ∈ Z : β = 1/2 ∧ H(γ_ρ) = 1}
```

`H(γ) = 1` (the whole ordinate carries one zero) implies `zeroMult ρ = 1`, not
conversely: a simple on-line zero sharing its ordinate with an off-line pair is
in `N0simple` and not in `Nsc`. RH collapses the distinction; unconditionally it
is exactly the kind of configuration the project exists to not assume away.

**Consequence.** `axiom baseline_zeta23 : zetaFamily.toCounts.Proportion 0.6725`
— the axiom supplying the entire certified 67.25% — is stated about `Nsc` and
therefore asserts **more** than zeta-23's Theorem D. Third instance of the
Prop-1-direction disease (#7, #8), this time in the load-bearing axiom.

**Not symmetric, and the asymmetry is in our favour where it matters.** Our
`prop1` (`Nsc ≥ 2N − N⊛` with the `H = 1` notion) is *stronger* than the
Proposition 1 GLSS state, and it is proved. Routes I and III therefore deliver
bounds on the stronger quantity. What was wrong is only the comparison: an
external number about `NscStd` was being read as though it bounded `Nsc`.

**Staged fix (parts 1–2 applied, part 3 gated on Joop):**
1. `ZeroData.NscStd` — the standard notion, matching `N0simple` character for
   character. *(applied, awaiting compile — toolchain is mid-bump)*
2. `ZeroData.Nsc_le_NscStd`, via `count_eq_one_of_H_eq_one`. *(applied)*
3. restate `baseline_zeta23` in terms of `NscStd`, and decide whether the
   metric reports both notions or only the stronger one. **GATED** — it changes
   what the certified number means, so LOOP.md sends it to Joop.

Until 3 is decided, no `PROPORTION.log` line is written.

### Resolution (session 004, from the W1 wildcard)

The gap is not a nuisance to be legislated away — it is the program's own
coordinate. A zero counted by `NscStd` but not `Nsc` is on-line with `H ≥ 2`
(a *haunted* ordinate: the functional equation forces its ghosts into pairs,
so `H ≥ 3`), and each such zero contributes at least `1` to
`Σ_ρ (H(γ_ρ) − 1) = N⊛ − N`. Termwise — no grouping over ordinates needed:

* `ZeroData.three_le_H_of_haunted` — a haunted ordinate has `H ≥ 3`: any other
  zero there is off-line, so its mirror is a third. **(proved)**
* `ZeroData.two_NscStd_le : 2·NscStd ≤ 2·Nsc + (N⊛ − N)` — ghosts charged
  **double**, because the functional equation forces them into pairs.
  **(proved; the factor 2 was spotted by the chat instance)**
* `Family.nscStd_le_nsc_add : (★) with C ⟹ NscStd ≤ Nsc + ((C−1+ε)/2)·N`
  **(proved)**
* `nsc_of_nscStd : (★) with C, plus `NscStd ≥ κ·N` ⟹ `Nsc ≥ (κ − (C−1)/2)·N`
  **(proved)**

**What this settles.** An external result about `NscStd` transfers to `Nsc` at
a cost of `(C − 1)/2`. For the zeta-23 baseline `κ = 0.6725` the transfer is
informative for **`C < 2.345`**, and it **beats Proposition 1 for every
`C > 1.655`** (Prop 1 gives `2 − C`, this gives `1.1725 − C/2`).

> ⚠️ **STALE THRESHOLD (SESSION 084).** The `Nsc` row is **open at 50.875%** (`certified_nsc_unconditional`), so "the row opens at `C < …`" no longer describes the situation. A star-bound route now matters only if it *beats* `0.50875`: Proposition 1 needs `C < 1.49125`, the `/6` bridge needs `C < 1.9825`. The thresholds below are retained as correct arithmetic about *opening* a row that is no longer closed.


**The correction that matters (and it kills the "score today" hope).** There
is **no unconditional `(★)` at all** — not even `C = 2`. `N⊛ ≤ 2N` says the
average horizontal multiplicity is at most 2; that is the program's *goal*,
not a triviality (unconditionally only `N⊛ ≤ N·O(log T)` is available, and
`fujii_ineffective` supplies *some* finite `C` whose value nobody has
computed). So the empty row does **not** open today.

**What the factor 2 does buy — and it is worth more than a one-off number.**
It lowers the bar for the *first* nontrivial statement about `Nsc` from
`C < 2` (the program's own goalpost) to `C < 2.345`. In [OPEN 0] currency:
the first number needs an effective Fujii constant `c₀ ≲ 1.17` (λ ≈ 1)
instead of `c₀ ≤ 0.855`. That is a materially easier target than anything
previously on the board, and it is the cheapest route to the empty row. So the honest metric reports
**both rows**, and the gap between them is not a caveat but a live readout of
how far `(★)` has got.

That also answers the second escalation question on the merits rather than by
taste: report both, because a theorem — not a convention — links them.

**Still Joop's call:** restating `baseline_zeta23` in terms of `NscStd`
(recommended: it is what zeta-23 proves) and the two-row metric layout.


## #14 — [bin 2, fixed] Detached long builds do not survive; and `| tail -N` hides the death

Session 003. `nohup setsid build.sh &` from a Bash tool call was killed silently
~1 min in: the sandbox does not keep detached grandchildren alive past the
spawning call. Worse, the script piped each step through `| tail -3`, which
buffers until the step *completes* — so a killed step produces **no output at
all**, and the log looked merely "still running" for 33 minutes.

**Fix (applied).** Long jobs run as a persistent `Monitor`'s own command, which
is harness-tracked and survives; the script streams (`>> full.log` plus one
`PHASE ... rc=$?` line per step to stdout), so every step reports its exit code
and a death is visible immediately.

**Rule.** Never wrap a long step in `| tail`/`| head` in a monitored script —
buffering converts a crash into silence, which is the failure mode the Monitor
guidance warns about ("silence is not success"). Echo `rc=$?` after every step.


## #15 — [session 003 wildcard] AH-oracle run on CGG98: the first **AH-sensitive** mechanism, and a conditional partial AH refutation

L8 asks, of any mechanism: *would it have gone through in an AH-world?* Run on
Conrey–Ghosh–Gonek 1998 (LEADS L11), the first known over-ceiling technique.

**Upgrade (dispatch, 2026-08-13): the result needs RH *only*.**
Bui–Heath-Brown 2013 (arXiv:1302.5018) removed GLH from CGG98 via the
generalised Vaughan identity, keeping the constant exactly: `19/27 = 0.703704`.
So the conditional partial AH-refutation below is **stronger than
classified**: under RH alone, every AH-configuration with more than `29.63%`
non-simple zeros is excluded. The de-conditioning study target is BHB13's
mechanism, not CGG98's — and when it is read for real, read it together with
the 2024 correction paper in that neighbourhood (Mathematika 2024), since the
CGG-adjacent literature carries a corrected error trail.

**Classification: AH-sensitive.** The argument is short and rests on numbers
already established here. zeta-23's `PairCeiling.ceiling_law256` proves every
bandwidth-one certificate certifies at most `0.6818287`. CGG98 certifies
`0.703704` under RH + GLH. `0.703704 > 0.6818287`, therefore **CGG98's
conclusion cannot be reached from pair-correlation information alone** — its
mechanism consumes something the pair kernel cannot see. What it consumes is
mean values of Dirichlet polynomials *sampled at the zeros*, i.e. joint
information about zero positions and `ζ`-values, which is exactly the
"beyond second moment" shape [OPEN D] demands.

This is the **first `AH-sensitive` entry** in the project. Everything else
catalogued so far (Route I's `Cbound`, the window optimisation of #12, the
whole `cWin` container) classifies `correlated`.

**Sharper, and worth carrying to the chat instance: CGG98 is a conditional
partial refutation of AH.** Read contrapositively, a lower bound of `0.703704`
on the proportion of simple zeros excludes every AH-configuration in which more
than `29.63%` of zeros are non-simple — under RH + GLH. That is not the jackpot
branch (an *unconditional* AH refutation), but it is the same shape, and it
says the AH barrier is not impervious to this class of technique: it has
already been dented, conditionally, in 1998.

**Follow-up for the study list.** The question to answer from CGG98's proof
rather than from its constant: *which* GLH consequence does the mechanism
actually need, and is there an unconditional fragment of it? The value of the
answer is set by #12's price tag — anything that escapes bandwidth one is worth
more than every remaining move inside it.

Caveat: this is a classification argument from the two constants plus the
ceiling theorem, **not** an analysis of CGG98's proof, which has not been read.


## #16 — [A2, resolved into a unification] the exact census is a lossy shadow of [OPEN 0′]

`A.md`'s A2 test shows the gauge/parity structure is resolution-independent
(`on_line_of_Hr_eq_one`, `odd_Hr_inhabited` at every radius), so exact
coincidence is not load-bearing. But the *accounting* is resolution-dependent
in exactly the way Proposition 2 already records: `N⊛ + (2/λ)∫₀^λ 𝒩` is the
cluster census at scale `λ/L`, and our exact theory discards `𝒩 ≥ 0`.

**Consequence for the plan:** [OPEN 0′] is not an optional improvement to
Route I — it is the identity's native form, and every constant we have quoted
for Route I (`c₀ ≲ 4.5`, `≤ 0.855`, `≤ 0.3476`) is the value obtained by
throwing information away first. A lower bound on `𝒩` at the optimising `λ` is
therefore worth more than its arithmetic suggests, because it is not a
subtraction bolted on — it is the term we deleted.


## #17 — [bin 2, mine] A tool-level failure means the whole command didn't run; partial retry = silent no-op

Session 013. A `Bash` call carrying *both* a python edit and a build failed at
the harness level (classifier timeout). I retried **only the build**, which
returned `rc=0` — because nothing had changed. I then reported "compiled first
try" and filed `A.md` claiming three theorems that did not exist.

Caught two minutes later by `#print axioms` reporting unknown constants.

**Rule.** When a call fails at the harness level, *re-issue the whole call*, not
the part you think mattered. And a green build proves nothing about work that
was never written — verify a new declaration **exists** (`grep`, or
`#print axioms`) before claiming it, exactly as a monitor must emit on failure
paths rather than staying silent (#14's lesson, in a new costume).

The fix cost nothing; the false register entry would have cost trust, which is
the only currency here that does not regenerate.

## #18 — [R16 audit, first target] `offline_le` is **tight** — the `/2` is not there

`Family.offline_le` charges each off-line zero once, and off-line zeros come in
pairs, so a `/2` looked plausible (the chat instance bet on it; so did I).
**It is not there.** `Gauge.offline_le_tight` exhibits the witness: one mirror
pair at one ordinate gives `N = 2`, `N_off = 2`, `N⊛ = 4`, so
`N + N_off = N⊛` **exactly**.

R16 calibration, which is the transferable part: **regrouping over atoms pays
only when the termwise charge under-counts.** A lone pair's own two terms
already saturate the bound, so grouping has nothing to collect. The census
(`2 → 6`) worked because a haunted ordinate's *neighbours* carried unclaimed
charge; here there are no neighbours.

So the reflection symmetry owns the `2` and the `6` — and there is no third
constant for it to own. E1/X annotated accordingly.


## #19 — [named object, standing question] The discarded `(2/λ)∫₀^λ 𝒩(α)dα`

Every Route I constant this project has quoted — `c₀ ≤ 0.855`, `≤ 0.3476`,
`≲ 4.5` — is obtained by **deleting this term in the first line** (`𝒩 ≥ 0`).
A2's unification says that deletion is exactly the passage from the fattened
census to the exact one, so the term is not a bonus subtraction: it is the part
of the Gallagher–Mueller identity we taught ourselves not to look at.

> **Standing question: what is the weakest unconditional input that keeps *any*
> of it?**

Not "prove [OPEN 0′]" — *any* crumb. The term enters every Route I constant
simultaneously, so a lower bound of any size at the optimising `λ` moves the
whole chain at once. Candidate suppliers, in the order their prices suggest:
Farmer–Ki via a `λ`-uniform transfer ([OPEN B″]); small-gap results at the
`λ ≈ 0.6–0.9` normalisation; the SDP school's close-pair machinery (L10), which
already optimises this coordinate conditionally.

Head of the queue in both registers.

### Answered (day cycle 1): the identity cannot supply its own crumb — and it misses by **3.5×**

**Route A — the single identity is circular.** `N⊛ + J(λ) = TL·M(λ)` is *one
equation in two unknowns*. The only free input is `N⊛ ≥ N`, which bounds `J`
from **above** (`J ≤ TL(M−1)`). A lower bound on `J` needs an independent
*upper* bound on `N⊛` — which is `(★)`, the goal. Kill condition fires for this
route.

**Route B — two λ's, and it is not circular.** The main term is
**non-monotone**: `M_main` falls from `1.505` at `λ = 0.05` to `0.581` at
`λ = 0.30`, then rises. Two instances of the identity give
`J(λ₂) − J(λ₁) = TL·ΔM` exactly, and `Σ(λ−d)` is increasing in `λ`, so
`λ₁J(λ₁) ≤ λ₂J(λ₂)`. Where `ΔM < 0` this forces

> `J(λ₁)/TL  ≥  −λ₂·ΔM/(λ₂−λ₁)  −  (λ₂(E(λ₁)+E(λ₂))/(λ₂−λ₁))·c₀`

a **genuine positive lower bound on close pairs, from the identity alone**, with
no new theorem about zeros. Best case `λ₁ = 0.05, λ₂ = 0.35`:
`J/TL ≥ 1.059 − 22.85·c₀`.

**Why it still fails, and by how much.** It needs `c₀ < 0.0463`. The proved
floor is `c₀ ≥ 0.16`. **Shortfall: 3.5×** — not orders of magnitude.

**And the shortfall is located.** `M_main`'s dip lives at small `λ`, and the
error coefficient `√log(2+λ)/λ` blows up at small `λ` — the free information
sits exactly where the noise is worst. So the target sharpens from "prove
[OPEN 0′]" to something far more specific:

> **the weakest input that keeps a crumb of `𝒩` is not a theorem about zeros
> at all — it is a better `λ`-dependence in Fujii's error as `λ → 0`.**

If the true error behaves like `√log(2+λ)/√λ` rather than `/λ`, the factor 3.5
evaporates. That is a question about Selberg's explicit formula for `S(t)` at
short averaging lengths, and it is the same object [OPEN 0] already needs — so
**one effective-Fujii analysis now pays twice**: an explicit `c₀` opens the
`Nsc` row, and a better small-`λ` shape opens the close-pair crumb.


## #20 — [R16 audit, closed for the core] `prop1` is LP-optimal; improving it needs a third moment

The R16 directive's remaining target was Proposition 1 itself. Grouping by atom
mass turns it into a two-variable LP: with `a_m` the number of ordinates of mass
`m`, `N = Σ m·a_m`, `N⊛ = Σ m²·a_m`, `N_sc = a_1`, and a linear bound
`a_1 ≥ αN + βN⊛` is valid iff `αm + βm² ≤ [m = 1]` for every `m ≥ 1`.

> **`SESSION 207`: this result is now one machine-checked statement.**
> `Optimal.prop1_LP_value` is `IsGreatest` for the two-moment LP on `C ∈ [1,2]`:
> its value is **exactly** `2 − C`, and `(2, −1)` attains it. The upper half is
> `prop1_LP_optimal`; the attainment comes from `206`'s characterisation, which
> also reproduces `prop1` itself (`linearBound_prop1_via_iff`). So `prop1` is an
> optimal point of the program, not only an unbeaten one.

**Result: `(α, β) = (2, −1)` — Proposition 1 — is optimal at every `C ≤ 2`**,
i.e. throughout the regime where the bound is non-trivial. (Past `C = 2` the
trivial `a_1 ≥ 0` wins, which is the empty row restated.) Equality holds for
every configuration built from atoms of mass `1` and `2`, and
`Gauge.prop1_tight` witnesses it in the kernel: one mirror pair gives
`2N − N⊛ = 0 = N_sc`.

> **SCOPED and PARTLY DISCHARGED, `SESSION 204`.** Two notes on what follows.
>
> **(a) The quantifier is now machine-checked.** The derivation above says a
> bound is valid iff `αm + βm² ≤ [m = 1]` for **every** `m ≥ 1`, and only
> `m = 1` and `m = 2` were formalised. `Optimal.linearBound_mass` supplies the
> direction running from a valid bound to the criterion, at every `m`, tested on
> the pure on-line atom `config m 0 a` where `N = m`, `N⊛ = m²`,
> `N_sc = [m = 1]`.
>
> **`SESSION 211`: and the consequence is now settled at every order.**
> `Optimal.linearBoundK_LP_value` is `IsGreatest` at `2 − C` for the order-`k`
> program, every `k ≥ 2`, from `Blindness.moment_minorant`
> (`A·m² + m ≤ m^k + A·m` with `A + 1 = 2^{k−1}`, tight at `m = 1` and `m = 2`).
> So the answer to "improving `prop1` requires a third moment" is that no moment
> improves it: each is priced against a minorant tight exactly where the
> two-moment program binds. `209`/`210` are the `k = 3` and `k = 4` cases.

> **`SESSION 205`: the converse is now proved too.**
> `Optimal.linearBound_of_mass_test` runs the grouping this entry describes —
> `N`, `N⊛` and `N_sc` are sums over atoms (`N_eq_sum_H`, `Nstar_eq_sum_H_sq`,
> `Nsc_eq_sum_mass_one`), so the bound holds termwise at `m = H γ`. With `204`
> the characterisation is machine-checked in both directions, and this entry's
> LP derivation is no longer carried by hand.
>
> **(b) The consequence below carries that quantifier and should say so.**
> "Improving Proposition 1 requires a third moment" holds for a bound asserted
> over configurations of every mass. `Optimal.prop1_LP_threshold_at_two` puts
> the threshold at `M = 2`, and `Optimal.boundedMult_one_iff_Nsc_eq_N` shows the
> class below it is `{N_sc = N}` — the ledger's own target. So a second thing
> can improve the reduction besides a third moment: **shrinking the class**.
> That is not a route to a better bound for `ζ` (see `SESSION 201`), but the
> word "only" below is unscoped as written.

**Consequence, and it is the interesting part:** improving Proposition 1
requires information beyond the two moments — a **third moment `Σ m³`** — which
is precisely [OPEN D]'s currency. So third-moment data is not only what pushes
`C` below `4/3`; it is also the only thing that can improve the *reduction*.
The ceiling and the reduction want the same missing input.

**R16's audit is now closed for the core**: `prop1` optimal, `offline_le` tight
(#18), the census improvement already taken (`2 → 6`). No further free constants
in the combinatorial layer.


## #21 — [the toll booth, surveyed] `𝓕(x,T)` is BGST's own object, and our certificates want an upper bound on it

Two findings that together relocate the front.

**1. The weighted object is not ours to invent.** BGST 2501.14545 §2: Montgomery's
`F(x,T)` never depended on RH — *the asymptotic* did, "because RH allowed the
real part of the zeros `β` to be removed out of `F(x,T)`. In [BGSTB24] we
**retained** this dependence to obtain an unconditional form of Montgomery's
theorem", with `𝓕(x,T) := Σ_{ρ,ρ'} x^{ρ−ρ̄'} W(ρ−ρ̄')`.

So `𝓕` **is** the horizontally weighted pair correlation — W16's toll-booth
object — and its unconditional evaluation for `1 ≤ x ≤ T` is the theorem this
project already stands on. W16, the Goldston–Montgomery bridge and BGST's
Theorem 1 are **one object at three parameter ranges**. Consequence: there is no
separate W16 formalisation to do at support `≤ 1`; importing the unconditional
Montgomery theorem imports the weighted object natively. *(Quoted via dispatch;
verify against the paper before it is used in a statement.)*

**2. The sign is favourable** (PRICES.md, day cycle 5): certificates consume an
**upper** bound on the form factor, so sieve arithmetic converts. `K ≲ 4` past
support 1 beats the bandlimited ceiling; `K = 2` gives `0.741`.

**The composition, every link named:** sieve upper bound for prime pairs
(*unconditional*, constant ≈ 3.4) → weight-retaining transfer past support 1
(*the unbuilt span*; BGST built the `≤ 1` case) → upper bound on `𝓕` past 1 →
`λ > 1` in the container → a constant above `0.6818287` in our own currency.

**The unbuilt span is the only gap**, and it has a literature: Languasco–Perelli–
Zaccagnini (JMAA 394, 2012; Trans. AMS 369, 2017) give unconditional explicit
both-direction relations with quantified losses; Chan (JLMS 68, 2003) sharpens
the precision; Heath-Brown 1982 is the precedent for hypotheses on `𝓕` rather
than on zero locations; Goldston–Montgomery already used a **twin-prime sieve
bound** to reach `1 ≤ α < 2`, under RH for the transfer only.


## #22 — [dictionary executed elsewhere; our slot is a lookup now] the corridor, and which wall each family eats

The sieve → `K` dictionary was never ours to build: **Carneiro–Chandee–
Littmann–Milinovich** did it. Under RH, the average of `F` over `[1, β]` obeys
an upper bound with constant `1.4283` (improving `10.824` implicit in
Goldston–Gonek) and a lower bound `0.8376`; **GGOS 2000** gives
`F(α) ≥ 3/2 − |α| − ε` on `1 ≤ |α| ≤ 3/2`. So past support 1, `F` lives in a
genuine **corridor** under RH, not merely under a roof.

**The sign-duality, and why our composition may be uncashed** (E12's newest
coat): CGdL's Cohn–Elkies class has `f̂ ≤ 0` outside the band, so it eats the
corridor's **floor** — `F` lower bounds. Our container has `v⋆v ≥ 0` and eats
the **ceiling** — `F` upper bounds. Each family was built knowing only its own
sign, and CCLM spend their upper bounds on `F`-averages, variance and the
log-derivative, never on `N*`. A certificate consuming **both walls** is a
finite question in the SDP framework dLRTW already run, and nobody's framework
has asked it.

**Cashing history, for the record:** GGOS 2000 → 67.38% (GRH); CGdL 2020 →
68.45% (GRH), 67.92% (RH alone); BHB13 → 70.37% (RH, different technique).

**Our slot is now a lookup** (PRICES.md): break-even `c ≤ 7.995` for the
ceiling, `c ≤ 3.667` for BHB13. Pending CCLM §3's short-range `J(β,T)`,
`β ∈ (1,2]`. **No claim until that lands** — and the too-easy alarm stays armed,
noting only that the composition now dies solely if the short-range constant
exceeds the *pre-CCLM* value.


## #23 — [the two-sided certificate exists **inside** our container] a window whose autocorrelation changes sign eats both walls

`v⋆v` is an autocorrelation: positive-*definite*, but **not pointwise
nonnegative**. That single observation dissolves the framework question in #22.

In `jWin = 2∫₀¹ D(λr)·(v⋆v)(r)dr`, the worst admissible `D` is `U` where
`v⋆v > 0` and **`L` where `v⋆v < 0`**. So a window with sign-changing
autocorrelation consumes the corridor's **ceiling and floor simultaneously** —
and a *positive* floor (GGOS's `F ≥ 3/2 − α` on `[1, 3/2]`) then strictly
reduces `jWin`, i.e. the floor becomes an asset rather than an irrelevance.

**Tested (day cycle 7).** Corridor `U = 2` past support 1, floor
`L(s) = max(0, 3/2 − s)`:

| window | best proportion | λ | `min(v⋆v)` |
|---|---|---|---|
| flat `v = 1` | 0.74717 | 1.25 | 0 |
| `1 + 1.25·cos(2πx)` | **0.80382** | 2.50 | **−0.034** |

The optimum is attained **at a sign-changing autocorrelation**, so the kill
condition ("if the optimum sits at `v⋆v ≥ 0`, the floor is never worth eating")
**fails to fire**. Gain over flat at the same corridor: **+5.7pp**.

**What this settles:** the two-sided certificate needs no new framework and no
SDP excursion. It is a *window choice* in the container we already have, and the
two certificate families' sign-duality (CGdL eats the floor, we ate the ceiling)
was never a structural divide — it was an artefact of each tradition using
nonnegative weights.

**Quarantined per A3**: RH-conditional (both corridor walls are RH results),
crude two-parameter window family, coarse `λ` grid, `U = 2` assumed pending
CCLM §3's short-range constant. Table-arithmetic, not a result. But the
*existence* claim — that the container can consume both walls — is
model-independent: it follows from `v⋆v` not being pointwise nonneg.


## #24 — [SELF-CORRECTION, bin 1] my `c`-table is **unsound as stated**; the alarm was right twice

Two independent defects, found by checking the trap rather than accepting the
escape.

**Defect 1 — scale mismatch (the fatal one).** The Abel step needs
`∫₁^u D ≤ c·(u−1)` for **every** `u ∈ (1, λ]`, including `u−1` tiny. CMR's
bound is an average over `[b, b+ℓ]` for **`ℓ` sufficiently large, `ℓ₀`
unquantified**. My table silently assumed the averaged constant holds at *every*
scale. It does not, and that assumption is precisely the difference between the
table's `0.8365` and the extremal problem's `0.6792`.

This is R9 — *ask which end binds* — failing on my own work: I checked the sign
of the consumption and never checked the **scale** of the input, which is the
mistake this project has now made four times in four different costumes.

**Defect 2 — circularity.** `1.3208` appears as *both* the averaged-`F` upper
bound *and* the `N*` bound (DIR Lemma 4: the restricted extremal problem "was
first solved by Montgomery and Taylor", RKHS constant
`1/K_ν(0,0) = 1/2 + (1/√2)cot(1/√2) = 1.3275`, improved to `1.3208` over the
Cohn–Elkies class). One optimisation, two faces. Feeding it back is #19 route A
again: **an output of the machinery re-entering as its input.**

**Consequence for #23 (the two-sided window).** Its `U = 2` input inherits
Defect 1, so the `+5.7pp` is **not** a bound. What survives untouched is the
*existence* claim, which never depended on a constant: `v⋆v` is positive-definite
but not pointwise nonneg, so a sign-changing window consumes both corridor walls
and lies outside the `g ≥ 0` axioms of every classical class (EP1's `A_Δ`, the
M–T bandlimited class). That remains the one genuinely new object here.

**The discriminator, now explicit — an input is usable only if it is both:**

1. **valid at the scales the window uses** (`ℓ` of order `λ−1 ≈ 0.2–1.5`, not
   asymptotic in `ℓ`); and
2. **not derivable from `{F on [0,1], F ≥ 0}`** — else it is re-packaged
   information and LP duality caps the result at the class optimum.

CMR's constants fail (1) and (2). **Sieve bounds on prime pairs pass both**:
they are pointwise in the shift `h`, and they are arithmetic rather than
zero-side. That is the only input class that has ever been able to move this
number, which is what Goldston–Montgomery's `1 ≤ α < 2` extension was doing in
1987.

**Route forward, unchanged in shape but now correctly gated:** re-run the
DIR/CMR averaging mechanism at **finite `ℓ`** (elementary — convolution against
`ĝ ∗ χ_[−L,L]`, Poisson, the `s₀` trick, two pages in DIR §2) to get
`ℓ`-dependent constants, then feed those. Every step is a finite optimisation;
the `ℓ`-dependence is computable, not deep.


## #25 — [Lemma 1 as a constraint] class-derived past-1 information buys **exactly nothing**, and my thresholds were vacuous

Goldston's survey (arXiv:math/0412313) Lemma 1, under RH:
`∫_B^{B+1} F(α)dα ≤ 3`, **uniformly for any `B`** — unit scale, every location,
no `ℓ₀` asymptotics. It passes discriminator condition (1) perfectly and fails
(2) by construction (its proof uses `F` on `[0,1]`, positivity, and the twist
inequality). So it is the **scale-corrected class bound**, and it prices route
(b) without running it: at unit scale the class constant is `≈ 3`, not `1.3208`.

**Run as a constraint, it settles the question numerically.** Worst admissible
`D` given only `{F on [0,1], F ≥ 0, unit-window cap 3}` is unit-spaced spikes of
mass 3 (the weight `1 − u/λ` is decreasing, so mass goes as far left as the cap
allows):

| λ | best proportion |
|---|---|
| **1.00** | **0.66667** |
| 1.10 | 0.23691 |
| 1.25 | −0.13333 |
| 2.00 | −0.33333 |

> **The optimum is `λ = 1` — Montgomery's `2/3`, refusing to leave the band.**
> Extending support on class-derived information is not merely useless, it is
> actively harmful.

That is the LP-closure story confirmed by arithmetic rather than by structure,
and it is the **fifth independent derivation** of the project's one conclusion
(after W7, W12, A2-forced, the E18 four-names argument) — the first proved by
duality.

**Retroactive audit, and it is worse than #24.** Lemma 1 says any model with
unit-window mass `> 3` is **RH-impossible**. My published break-even thresholds
(`c ≤ 7.995` for the ceiling, `c ≤ 9.532`) sat entirely in impossible territory,
so that analysis was not merely unsound — it was **vacuous**. The `c = 4`, `8`,
`10.824` rows describe worlds RH forbids.

**Guard built** (`forensics/lemma1_guard.py`): every candidate form-factor model
is checked against Lemma 1 **before** any table is constructed. Self-tested;
`c = 4` fails as it must. This is R17 applied to my own numerics — the claim
"this table is meaningful" needed a positive witness and now has one.


## #26 — [premise corrected; the chain priced] the sieve closes the band **edge**, and the fuel is MRT — worth `0.809` if one comparison closes

**Premise correction (fifth of the session, and mine to carry).** "GM 1987
extended `F` to `1 ≤ α < 2` using a sieve bound for prime twins" conflates two
results. Per Goldston's survey: the **sieve improves one error term**
(`O(x log x) → O(x)`), extending Montgomery's theorem to `α ≤ 1` **exactly** —
it *closes the band edge*. What reaches `(1, 2)` is the **full Hardy–Littlewood
conjecture with power-saving error**, which is what Bolanz's 131 pages prove.
✅ **RE-CHECKED `SESSION 159`, and it still does not exist** — dated, so the
absence queue can stop carrying this as unexamined. Primary source: Baluyot,
Goldston, Suriajaya, Turnage-Butterbaugh, *An unconditional Montgomery theorem
for pair correlation of zeros of the Riemann zeta function*, arXiv:2306.04799,
**Theorem 1** (displayed, read here, not recalled):

> `F(α) = T^{−2α}(log T + O(1)) + α + O(1/√(log T))`, **uniformly for `0 ≤ α ≤ 1`.**

That is the state of the art for the *unconditional* form factor and it stops at
`α = 1` exactly — which is the band edge this entry already identified, now
confirmed by a 2023 paper rather than by the survey alone. Nothing in it reaches
`(1, 2)`.

So the input "`F(α) ≤ G(α, C_sieve)` on `[1,2)`" **does not exist in the
literature** and must be built — re-checked `SESSION 159` against
arXiv:2306.04799 Theorem 1, whose range is `0 ≤ α ≤ 1`.

**The dictionary is now confirmed**, from the survey's own exercise: HL for
`h ≤ X^{θ}` gives `α ≤ 1/(1−θ)`. Two points fix the curve — `θ = 1/2 → α ≤ 2`
(the survey's statement) and `θ = 8/33 → α ≤ 33/25 = 1.32` (MRT). My earlier
provisional flag on this is discharged.

**The bridge transfers inequalities, not just asymptotics** — survey (9.9) has a
**nonnegative** integrand and `F` enters through a nonnegative `(sin)²` kernel.
So an upper bound on the primes-side second moment yields a *pointwise* upper
bound on `F`. That is the machine that would build the missing input.

**Priced, R18-clean** (arithmetic input, correct scale, guard passed — worst
unit-window mass `2.36 ≤ 3`). With `D(s) = s` on `[0,1]`, `D ≈ 1` on `(1, A]`,
and only Lemma 1 beyond, the optimum sits **exactly at `λ = A`** — the container
again refuses to leave the fuelled region:

| `θ` | reach `A = 1/(1−θ)` | proportion |
|---|---|---|
| **8/33 (MRT, current)** | **1.32** | **0.80869** |
| 1/3 | 1.50 | 0.85185 |
| 1/2 (full HL) | 2.00 | 0.91667 |

against Montgomery `0.6667`, M–T `0.6725`, CGdL(RH) `0.6792`, ceiling `0.68183`,
BHB13 `0.70370`.

**The single gate**, exactly as the survey locates it: *does MRT's almost-all-`h`,
log-power-saving error survive the weighted sum `Σ(h−k)[·]` that (9.1) needs?*
A finite comparison of two published error terms — MRT I §1 against survey
(9.1)'s uniformity. **Quarantined per A3**: RH-conditional *and* gate-conditional.
No claim.

**Note on instrument complementarity:** where `F` is *known* (`[1, A]`) there is
no corridor, so the sign-changing window contributes nothing there. Its value is
strictly in regions where only a corridor exists — i.e. **past** the fuel. The
two instruments do not compete; they tile.


## #27 — [THE GATE IS DECIDED: it fails] MRT's error quality does not cross the bridge; `0.80869` retracts to Montgomery's `2/3`

**Requirement side** (Goldston survey §9, fetched): the bridge runs through
`(9.3)`, `∫₁^X(ψ(x+h) − ψ(x) − h)²dx ∼ hX·log(X/h)`, and the survey states that
Hardy–Littlewood **in the form (6.3), with error `O(N^{1/2+ε})`** — a *power*
saving — is what implies `(9.1)`/`(9.3)` for `h ≤ X^{1/2−ε}` and hence SPC on
`1 ≤ α ≤ 2−ε`.

**Why a power saving is forced:** the second moment expands as
`Σ_{|k|<h}(h−|k|)·[Λ-correlation at shift k]`, so **each shift's error is
amplified by up to `h`**. Total error `≈ h²E` against a main term
`hX log(X/h)` requires `E ≪ X·log(X/h)/h`, i.e. `E ≪ X^{1−θ}log X` for
`h = X^θ`.

**Supply side** (MRT I, fetched): the saving is *"an arbitrary power of the
logarithm over the trivial bound"* — `E = X/(log X)^A` — for **almost all**
`h ∈ [−H,H]`, `X^{8/33+ε} ≤ H ≤ X^{1−ε}`.

**Comparison:** the bridge needs `X^θ ≪ (log X)^{A+1}`. For fixed `A` and any
`θ > 0` this is **false for large `X`**. MRT's `h`-range is real; its *error
quality* does not travel.

> **The gate fails, and it fails by a power of `X`, not by a constant.**
> Log-power savings suffice only for `h` polylogarithmic — i.e. `θ → 0`,
> `α`-reach `→ 1`: the band edge, which the twin-sieve already closes.

**Consequence: `A = 1`, not `1.32`.** The priced `0.80869` is **retracted**; the
chain as constituted delivers nothing past Montgomery's `2/3`. Sixth
self-correction of the session and the first to kill a headline.

**What the failure buys, which is the whole point of running it:** the target is
now exactly named — **averaged Hardy–Littlewood with a power saving**, for
`h` a fixed power of `X`. That is the survey's own `(6.3)`, it is far stronger
than anything MRT proves, and it is the single named object the entire priced
chain was resting on.

**And the corridor is now everything past `α = 1`**, with no fuel anywhere in
it. That does not weaken W27's T3 — it makes T3 **the only game**: the
sign-changing window's domain is the whole corridor, and corridor walls are its
only possible fuel.

**STRENGTHENED (2026-08-15, `F.md` F4).** The weight `(h−|k|)` above **is** the
Fejér/Cesàro weight, so there is no sharp window to smooth away. And no weight
of any shape helps: with per-shift absolute bounds `|E_k| ≤ E`, the total error
is `Σ w_k|E_k| ≤ E·Σw_k`, and the main term fixes `Σw_k ≈ h²` for every
admissible weight — checked numerically for Fejér, flat and Gaussian profiles,
all giving the same `h²E`. So `#27` upgrades from *"MRT is too weak"* to **"no
reweighting of the GM identity can be strong enough"**. The only escape the
argument leaves is **cancellation between shifts**, which is a correlated-error
question, not a window question (`F.md` F5).

**Process note (in-cycle, twice):** my first amplification check printed "OK" at
`X = 10³⁰` — a small-numbers illusion, since `X^θ` overtakes `(log X)^{A+1}`
only past `10¹⁰⁰`. Caught by asking for the asymptotic statement instead of a
value. The guard culture is now catching errors inside the cycle that produced
them, which is the first time that has happened twice in one turn.

## #28 — [bin 2, reproducibility] the build depends on a live remote, and the audit grep is off by one

Found by the packaging agent while writing `VERIFYING.md`. Two defects in the
repo's *verifiability* rather than its mathematics — filed because a repo whose
whole claim is "check this yourself" must be checkable by someone who is not us.

**(a) No vendored dependency.** `lakefile.toml` carries `rev = "main"` while
`lake-manifest.json` pins `3635e74…`. The manifest is what makes reproduction
possible, and it points at `github.com/anthropics/zeta-23-lean`, which is
publicly reachable today. There is **no vendored copy**: if that repository
moves or disappears, the build stops being reproducible and every axiom-free
claim becomes uncheckable by a third party. The `rev = "main"` in the lakefile
is the sharper half — it invites a `lake update` that silently retargets the
pin.
*Fix, cheap:* pin the lakefile to the manifest's rev. *Fix, durable:* vendor or
mirror the dependency. Not done this cycle — it touches the build's trusted
inputs, so it is escalated rather than executed.

**(b) The documented audit command is off by one.**
`Riemann/Assumptions.lean`'s house rules say `grep '^axiom' Riemann/Assumptions.lean`
**is** the audit. It returns **10** lines, not 9: line 26 is the prose
`axiom must extend it**:` inside the consistency-model doc comment.
`tools/proportion.go` strips comments first and is not fooled, so **no logged
number was ever wrong** — but the command we tell a reader to run disagrees with
the tool by one, which is precisely the kind of gap that erodes trust in
everything else on the page. Documented in `VERIFYING.md` §3.1 as a known
discrepancy.
*Fix:* reword the doc comment so no line begins with `axiom`, or change the
stated audit command to the comment-stripping one. Either is a one-line edit;
neither is done under this cycle's escalation discipline.

**(c) Noted, already tracked:** `audit/Declarations.lean` and
`audit/PrintAxioms.lean` do not cover the `Blindness.lean` / `Fiber.lean` names.
Flagged in SESSION 033 as deferred under the freeze; it is the first
post-freeze item.


## #29 — RESOLVED, and the original diagnosis was wrong

> ⚠️ **Read this before the note below.** `#29` claimed the repair needed the
> source paper. **It did not.** The full specification — functional,
> discretisation, linear algebra — was in `LEADS.md` three lines above the table
> the entire time. `forensics/window_opt.py` implements it and reproduces every
> quoted value to all seven digits (`c*(1.00) = 0.7533028`,
> `2 − 1/c* = 0.6725126`, `λ = 0.75` likewise). **The table is reproducible; the
> defect was mine, not the record's.**
>
> What I did wrong: I searched `forensics/` for a *script*, found none, and
> concluded the computation was lost — without checking whether the
> *specification* was in the register. Under-searching, then filing the gap as
> external. The refusal to reconstruct from memory was still correct; the
> correct path was simply to read three lines up. Filed as `SURPRISES` S27.
>
> Grade in `CLAIMS.md` stays **N** — the evidence is still numerical, not a
> proof — but the "code not in repo" mark is removed.

## #29 (original note, superseded) — [bin 2, reproducibility] the window-optimisation table has no code in the repo

Found by night cycle 10's attempt to promote the last grade-C claim.

`LEADS.md`'s window table (`λ`-sweep, optimum `0.6725126` at `λ = 1`, `N = 160`
midpoint quadrature) and `E.md`'s E17 table (the `18.18pp` "constants are
properties of the instrument" claim) both rest on a numerical optimisation whose
**script is not in `forensics/` or anywhere else in the repo**.

Everything else numerical here is reproducible: `lemma1_guard.py`,
`provenance_lint.py`, `quarry.py`, `w16_price.py`, `surprises.py`. This is the
sole exception, and it happens to sit under two of the project's most-quoted
claims.

**What is verified:** the closed form is right —
`3/2 − (1/√2)cot(1/√2) = 0.6725007036794116`, matching the register to all
quoted digits, and the reported optimiser is `1.19 × 10⁻⁵` above it, consistent
with the stated quadrature error.

**What is not:** that the optimisation actually ranged over the class claimed,
at the resolution claimed.

**Deliberately not repaired tonight.** Reconstructing the variational problem
from memory would yield a script computing *something*; presenting it as the
original would be a fabricated provenance — precisely the disease
`provenance_lint.py` exists to catch. The honest repair is to re-derive the
functional from the source with the source in hand, then commit the script.
Until then the claim carries grade **N** in `CLAIMS.md` with an explicit
"code not in repo" mark, and must not be cited as a bound.


## #28(a) — CLOSED (2026-08-15, Joop's ruling "fix what needs fixed")

`lakefile.toml` now pins `rev` to `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`,
the exact commit the manifest records, with the reason stated in the file.

**And the fix had a second half that nearly got missed.** Pinning the lakefile
made `lake` warn *"manifest out of date: git revision of dependency 'zeta23'
changed; use `lake update zeta23`"*, because the manifest's `inputRev` still
read `"main"`. The obvious way to silence that warning is **exactly the failure
mode the pin exists to prevent** — `lake update` would fetch whatever `main`
points at today. Instead the manifest's `inputRev` was edited to the same
commit, by hand, without an update. Now `lakefile.rev = manifest.inputRev =
manifest.rev`, the warning is gone, and the build is green on the same
revision.

> **CLOSED, `SESSION 231`, on Joop's ruling — the vendored copy exists.**
> `vendor/zeta23`, 341 files, byte-identical to the pinned commit, tree hash
> `c9baf0ab3555bc7e…`. `vendor/PROVENANCE.md` records it and
> `forensics/vendor_check.py` re-verifies all three of bytes, lakefile and
> manifest.
>
> **The second half of the fix nearly got missed again, in the same way.**
> Switching only `lakefile.toml` to `path = "vendor/zeta23"` builds green and
> changes nothing: the manifest's `git` entry wins, and lake re-cloned zeta-23
> from GitHub at the pinned commit while the build looked exactly as it should.
> The manifest is the authority for a dependency it has already resolved. Fixed
> by editing the manifest entry to `type: "path"` **by hand** — the same
> technique this entry's first half used for `inputRev`, and again without
> running `lake update`.
>
> Witness that the vendoring is real: `.lake/packages/zeta23` deleted, `lake
> build` green in `3757` jobs, no clone recreated, build outputs appearing in
> `vendor/zeta23/.lake`. Trust unmoved — base `cd7a22e688df`, axioms `2`,
> ledger `NscStd 67.25% / Nsc 50.88%`.
>
> **Scope, stated because the ruling's phrasing is broader than the act.**
> Mathlib is still a `git` dependency inherited from `vendor/zeta23`'s own
> lakefile at rev `51e6992e…`; a fresh clone still fetches it. What now lives on
> our disk is the package carrying this project's trusted inputs, not the whole
> toolchain.

Still open, and deliberately: **there is no vendored copy.** The pin removes the
"someone else's content" half of the risk; the "someone else's uptime" half
remains. Vendoring or mirroring is a larger call.


## #30 — [bin 3, process, **FIXED** — see the body] R17 was never applied to the loop's own liveness

> ⚠️ **Header corrected `SESSION 122`.** The body has recorded the fix (cron
> heartbeat) since 2026-08-15; the header still read as open, so a surface scan
> of headers — which is what `LOOP.md` step 2 prescribes — would have seen a
> live defect. Standing caveat, not a claim about now: the job was created with
> a 7-day auto-expiry and dies with the session, so *whether it is running* is a
> live-state question and `R17` forbids asserting it either way.

The loop stopped at 10:50 and was not noticed until 14:36, because the turn that
landed `SESSION 056` ended on prose instead of on `ScheduleWakeup`, and the
closing line then *asserted* the loop was armed.

**This is R17 exactly**, turned on the one system that was never checked: every
green build got "no witness, no belief" all night; the scheduler got a claim.
The dropped call is a slip. The asserted state without a check is the defect.

Neither existing guard covers it. `provenance_lint` types mathematical inputs;
`claims_gate` catches exactness language, and *"the loop is armed"* has none —
it is a plain factual claim about live state.

**FIXED (2026-08-15, Joop's suggestion): the loop is a cron heartbeat, not a
self-rearming wakeup.** Job `e05114b3`, `23,53 * * * *`, off the crowded
:00/:30 marks. The structural point is that it fires whether or not the operator
remembers — the failure mode was that `ScheduleWakeup` made the operator the
single point of failure, and the fix is to move the timer outside the thing that
failed. Joop's framing: *ADHD tricks*. Limits, stated rather than assumed:
session-only (dies with the session, survives forgetfulness but not a restart)
and auto-expiring after 7 days.

The heartbeat prompt also carries a clause the self-paced loop lacked — *"if
nothing is worth a cycle, say so in one line and do nothing"*. The old loop had
a standing incentive to produce work on every wake, which is plausibly part of
why cycles 8–12 drifted into auditing the audits (R20).

**Residual, not yet built:** any statement about the loop's liveness must
cite the `ScheduleWakeup` return (which prints the scheduled time) in the same
turn, or say nothing. That is the two-slot discipline of `claims_gate` applied
to state claims rather than exactness claims — forward slot: the tool result.

Filed as `SURPRISES` S28. Found by Joop in three words.
