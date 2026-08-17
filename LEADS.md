# LEADS — the cutting-room floor


## `SESSION 181` — the profile dictionary, completed for the ledger and open for one quantity

Every ledger quantity now has a profile reading: `N`, `Noff`, `N⊛`, `Nsc`,
`NscStd` (the original five), `oddAtoms`, `atomCount` (`180`) and
**`hauntedCount`** (`181`, axiom-free). The last two were definitional
connections nobody had written down, and `hauntedCount`'s absence mattered — it
is the quantity `HauntedDensity`, the ladder and the off-line exchange all
consume, so had it not been a profile functional the blindness analysis would
have had a hole exactly where this project's own coined quantity lives.

**One quantity appears NOT to be a profile functional, and this is an argument,
not a theorem.** `ZeroData.distinctZeros` (introduced at `167` for the Wu
dictionary) counts distinct *points*; a profile entry `(m, o)` records `o` units
of off-line **mass**, not how that mass splits into distinct points. Two
configurations with profile `(4, 4)` — one ordinate with two off-line pairs at
distinct `β`, versus one pair at doubled multiplicity — should share a profile and
differ in `distinctZeros`.

**Not proved here.** Building the doubled-multiplicity witness needs a
construction the file does not have, and `175`/`176` are the record of what
happens when a plausible structural claim is written as though established. Filed
as the shape of an explanation for why `167`/`168`'s dictionary had to be an
*inequality* (`atomCount ≤ distinctZeros`) rather than an identity.

> **`SESSION 182` — attempted, and the witness pair is now named rather than
> sketched.** The construction exists and needs nothing new:
>
>     A = configAt 0 0 2 a                              -- one pair, doubled
>     B = superpose (configAt 0 0 1 a) (configAt 0 0 1 b)   -- two distinct pairs
>
> with `a, b ≠ 1/2`, `a ≠ b`, `a ≠ 1 − b`.  `superpose` imposes no disjointness,
> so both stack four off-line zeros at ordinate `0`: `H = 4`, `offAt = 4`,
> profile `{(4, 4)}` for both, while `distinctZeros` is `2` and `4`.
>
> **The profile half is easy** — `H_superpose` and `offAt_superpose` are additive
> and `configAt_H` / `configAt_offAt` give the values. **The `distinctZeros` half
> did not close**: it needs `Finset` cardinalities over multiset literals
> (`toFinset_add`, `toFinset_replicate`, pairwise distinctness of four points in
> `ℝ × ℝ`), and the attempt was reverted rather than left half-built.
>
> So the claim is **still unproved**, but it is now a specified obligation with a
> named witness pair and a known hard half, rather than an argument.

> ✅ **PROVED, `SESSION 184`.** `Blindness.distinctZeros_not_profile_functional`
> (axiom-free): same profile `{(4,4)}`, and
> `distinctZeros A < distinctZeros B`. The route that worked avoids computing
> `distinctZeros B` at all — `A`'s support is contained in `B`'s and `(b, 0)` is
> in `B` and not in `A`, so `Finset.card_lt_card` gives the strict inequality.
> Three attempts: `182` and `183` both tried to *count* `B`.
>
> **`SESSION 183` — second attempt; half closes, and the working proof is
> recorded here so a third does not rediscover it.** The lemma name `182` guessed
> wrong is `Finset.card_insert_of_notMem` (capital `M`). With it, the *easy* side
> compiles:
>
> ```lean
> example {a : ℝ} (ha : a ≠ 1/2) : distinctZeros (configAt 0 0 2 a) = 2 := by
>   classical
>   have hane : a ≠ 1 - a := fun h => ha (by linarith [h])
>   show (Multiset.toFinset (Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
>       + (Multiset.replicate 2 (a, (0:ℝ))
>         + Multiset.replicate 2 ((1 - a : ℝ), (0:ℝ))))).card = 2
>   rw [Multiset.toFinset_add, Multiset.toFinset_add, Multiset.toFinset_replicate,
>     Multiset.toFinset_replicate, Multiset.toFinset_replicate]
>   norm_num
>   rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hane])]
>   simp
> ```
>
> **The four-point side still does not.** `simp` leaves one membership goal
> (`¬b = 1 − b`) that its own hypothesis should discharge, and forcing it with a
> structured `refine`/`simp_all` hits `maximum recursion depth`. Two attempts,
> stopped by a kill condition set before the second began. The obligation is
> unchanged: **`distinctZeros (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)) = 4`**,
> everything else in the argument being in hand.


## `SESSION 159` — a simplicity route that consumes *location* rather than multiplicity

Read from displayed statements in Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh,
arXiv:2306.04799 (fetched and read, **not** `[RECALL]`):

* **Theorem 2.** If every zero with `T^{3/8} < γ ≤ T` lies in the thin box
  `|β − 1/2| < 1/(2 log T)`, then for sufficiently large `T` at least **61.7%**
  of the nontrivial zeros are **simple**.
* **Theorem 3.** The same `61.7%` from a strong zero-density hypothesis:
  `N(σ,T) = o(T^{2(1−σ)})` for `1/2 + 1/(2 log T) ≤ σ ≤ 25/32 + η`.
* The paper's own remark: the method *"neither requires nor provides any
  information on whether any of these zeros are on or not on the critical line."*

**Why this belongs in the registers.** Every rung of `PRICES.md`'s menu is a
hypothesis about **multiplicity** (`NoSmallHaunted m`, `H ≤ M`). These two are
hypotheses about **location** — a thin box, and a density bound — and they buy a
simple-zero proportion without touching the line question. That is a *third axis*,
and the project has priced nothing on it.

✅ **Dictionary written, `SESSION 160`, and the axis dies on it.** Their `simple`
is multiplicity-one over *all* nontrivial zeros — the paper's own remark is that
the method says nothing about location — whereas **both** our notions demand
`p.1 = 1/2` (`Basic.lean`: `Nsc` and `NscStd` each filter on it). So theirs is a
**third, weaker quantity**, now named `ZeroData.NscAny`, and
`ZeroData.NscStd_le_NscAny` (axiom-free) is the entry that makes the numbers
comparable.

The consequence: our certified `NscStd/Nz ≥ 0.6725` transfers to *their* quantity
at the same constant, so the project already holds **67.25% on the very thing
they bound**, against their conditional `61.7%`, and without the thin-box or
zero-density hypothesis. ⚠️ **OVERCLAIMED — corrected `SESSION 163`.** What follows is true of
**arXiv:2306.04799's simple-zero theorems**, and I wrote it about *the location
axis*. The axis is wider than that instance. `Program.routeIII_with_narrowBox`
consumes a **narrow-box** hypothesis — location, not a ledger row — and
`conjectural_routeIII` delivers the `Nsc` row at `2/3 − ε`, i.e. **+15.79
points**, at a cone of **one** axiom. It was in the repo the whole time, in the
`Conjectural` section, and I never put it on the menu. See `PRICES.md`.

**That instance of the third axis buys nothing the ledger does not
already have, and it is aimed at a weaker row than the menu operates on.**

✅ **`SESSION 161` — and the reverse direction is walled, at every strength.**
`ZeroData.NscAny_le_NscStd_add_Noff` (axiom-free) is the exchange rate the other
way: `NscStd ≥ NscAny − Noff`. So a lower bound `NscAny ≥ κ·N` yields
`NscStd/N ≥ κ − 0.3275`, and beating `0.6725` needs `κ > 1` while
`NscAny ≤ N` (`NscAny_le_N`) caps `κ` at `1`. In exact rationals:

| `NscAny/N ≥` | gives `NscStd/N ≥` | beats `0.6725`? |
|---|---|---|
| `0.617` (their theorem) | `0.28950` | no |
| `0.900` | `0.57250` | no |
| `1.000` (every zero simple) | `0.67250` | **exact tie** |

**And the tie is not a coincidence — it is circularity.** The only off-line bound
we hold is `certified_offline`, which is `offLineImport_of_proportionStd
certified_std`, i.e. `β = 1 − κ` derived from the row being improved. The route
returns exactly what it consumed. `provenance_lint`'s **Rule 1** shape, on a
chain nobody had drawn.

**So no result of this genre can move the ledger through this route at any
strength, on the unconditional off-line bound.** What would break the wall is an
*independent* `β < 1 − κ`. `offline_via_xiPrime` **is** such a bound
(`β = 0.14162`, giving `0.85838` at `κ = 1`) — but it is `1 − κ'` minted from the
ξ′ row instead, and carries ξ′'s two hypotheses and two extra axioms. The
circularity moves rather than disappearing.

*Original note, superseded above:* that `61.7%` is comparable to any row of our
menu was **not claimed** until the dictionary existed. Their `simple` is
multiplicity-one over all nontrivial zeros; our rows are `Nsc` (`H = 1` at an
ordinate) against `Nz`.

*Also noted, not chased:* the paper attributes to PRZZ "more than **41.7%**"
simple, where this project records `0.4162`. Either a rounding of the same
result or a slightly weaker transcription; it carries no weight, since `147`
established the figure is redundant and `233` deleted the axiom that carried it.

> **`SESSION 246`.** This paragraph cited `Assumptions.baseline_przz`, which
> `233` removed on Joop's ruling. The `0.4162` figure survives as the theorem
> `Riemann.przz_of_zeta23`, derived from `baseline_zeta23` by
> `Family.ProportionStd.mono`; the axiom does not.

From Addendum 2 (Joop, 2026-08-13). Pointers into the space, decoupled from
the validity of the arguments that surfaced them. Nothing here has been acted
on yet; promotions into the skeleton get a `SESSION.md` event.

| # | Lead | Verdict this session | Cost to pursue |
|---|---|---|---|
| L1 | Differentiation *is* the arithmetic heat flow: `ξ^(m)` as a discrete `t`, keeping the Euler product Tao's obstruction removes | **Promote.** It is the one lead that changes the *structure*: it merges Routes II and III, and Route II's derivative side is already unconditional (ISSUES #2). Concretely: does `DensityNearLine` for `ξ^(m)` have an `m`-uniform transfer to `ζ`? | medium (literature: Forum Math. 2020 on `ξ^(m)`, Ki's Farmer–Rhoades convergence) |
| L7-Fujii | Fujii/Tsang proved **all** `2k`-th moments of `S(t)` unconditionally; the skeleton uses only `k = 1` | **Promote, jointly highest.** This is existing *unconditional higher-moment* information — the shape [OPEN D] wants. If the Gallagher–Mueller identity has a `2k` analogue, `C` is not obviously capped at `4/3` | medium |
| L3 | Davenport–Heilbronn / Epstein as a **negative control**: every lemma that forces zeros onto the line must identifiably fail for D–H | **Adopt now as a standing rule.** Directly relevant to ISSUES #8: an abstract-`Family` bridge that "works" for arbitrary families would prove too much for D–H. Also gives *real* off-line zeros for numerics instead of synthetic perturbations | cheap, permanent |
| **L9** (supersedes L5) | Port the post-1974 extremal technology into the unconditional signature container. **Donor identified: Chirre–Gonçalves–de Laat [CGdL20]** (extremal functions via SDP), 0.679 "by Montgomery's method with an optimized test function" — *not* CCCM | **Architecturally possible** (code read below), and the donor's 0.679 sits exactly in the gap our λ-sweep predicted. Headroom proved: ≤ 0.6818287 | small–medium |
| **L10** (new) | de Laat–Rolen–Tripp–Wagner arXiv:1908.04876 bound `N*(T) ≤ (1.3208+o(1))N(T)` for Dedekind zeta, improving 1.3275. **Under RH their `N*` is our `N⊛`** — the SDP school has been optimising the master coordinate of (★) directly, for years. Their programs "interpolate between the pair-correlation bound and Cohn–Elkies sphere packing in dimension 1" | **Promote.** A systematic *window-generation engine* for the container, not a single optimum. Note `1.3275 = 2 − 0.6725` is literally our `Cbound_lt_record` threshold, and `1.3208 ↔ 0.6792` | medium |
| **L11** (new, **classified AH-sensitive — ISSUES #15**) | Conrey–Ghosh–Gonek 1998: under RH **+ Generalized Lindelöf**, ≥ 70.3704% simple (≥84.57% distinct) — **above** the bandwidth-one ceiling 0.68183, via mean values of Dirichlet series sampled at zeros, not pair correlation | **Study target for [OPEN D].** First known over-ceiling technique; an existence proof that the ceiling has a far side. Standing question: run the L8 AH-oracle on CGG98's *mechanism* — would it work in an AH-world? First classification of an over-ceiling method | cheap (analysis only) |
| L2 | F. Brown: finite Li positivity ⟺ explicit zero-free regions; `λ_n` computable to `n > 20000` | Parked, interesting: it is a *different supplier* for the same interface as Doubt 3 / ISSUES #1 — and ISSUES #1's corrected form now asks for exactly a zero-free-region-flavoured input | one search + Arb numerics |
| L4 | Integral-operator form of the Bombieri/Yoshida functional | Background; relevant when the zeta-23 import is done for real (ISSUES #4) | low |
| L8 | **The AH oracle**: autopsy every failed/stalled attempt against the Alternative Hypothesis (BGST arXiv:2508.10857) — "would this mechanism have gone through in an AH-world?" `yes` → `correlated` (factors through pair information); `no/unclear` → `AH-sensitive`, escalate as an [OPEN D]-grade signal | **Adopt now, same tier as L3.** Together they make the three-column testbed (Odlyzko / Davenport–Heilbronn / AH-synthetic). The fingerprint across the three columns says what information a lemma *actually* consumes, independent of its prose; a mismatch is bin-3 | cheap, permanent |
| L6 | Crank-adjacency signal at the [OPEN A′] framing | Noted. Weak evidence that the A′ coordinate is natural. Do not cite | none |
| L7-NB | Nyman–Beurling–Báez-Duarte lower-bound machinery, dualised toward `N⊛` | one search's worth | tiny |
| L7-Res | Resonance method (Bondarenko–Seip) as a supplier for [OPEN 0′] close pairs | one search's worth | tiny |

## The three-column testbed (L3 + L8)

Every lemma that is supposed to force zeros onto the line gets three columns:

| column | what it is | expected verdict |
|---|---|---|
| Odlyzko zeros | the truth | passes |
| Davenport–Heilbronn | functional equation, **no Euler product**, real off-line zeros | **must fail**, and the failure point must be traceable to the missing Euler product |
| AH-synthetic | spacings locked near half-integer multiples of the mean gap (2508.10857's model) | passes ⟹ the lemma is pure pair information (`correlated`); fails ⟹ `AH-sensitive`, escalate |

Fingerprints go in `ISSUES.md`. **Jackpot branch:** any attempt that appears
to refute AH-configured zeros unconditionally — stop and write it up.

Retro-fingerprint of what exists today (claimed, not yet numerically tested):
`Basic`/`Transfer` are pure counting and pass **all three** columns — they
assume nothing about `ζ` beyond reflection symmetry, which is exactly why
`ZeroData` admits Davenport–Heilbronn-like families (ISSUES #8). `Fujii`'s
`Cbound` is second-moment input: `correlated` by construction, which is the
§5 ceiling restated. Nothing in the repo is yet `AH-sensitive` — consistent
with the claim that no route here passes `4/3`.

## L9: what the E2 code reading settles

`Zeta23/XiPrime/Defs.lean` makes the container **doubly parameterised**:

```
cWin D lam v := lam·(∫v)² / (∫v² + lam·jWin D lam v)
jWin D lam v := 2∫₀¹ D(lam·r)·(v⋆v)(r) dr
kappaXi lam v := 1 / cWin D1 lam v
```

* `D` is the **pair-correlation kernel**, a free parameter. `D(s) = s` is the
  ζ case (their own comment: "For D(s) = s this equals `Zeta23.ThmD.cFun`");
  `D₁` is the `ξ'` form factor — Farmer–Gonek's `F₁` minus its `T^{-2α}log T`
  term — given in **closed form** as a convergent series with a certified
  truncation (`D1trunc 9`, tail `ε₉ ≤ 3.43·10⁻⁷`).
* `v` is the **extremal window**, also free. `cert_of_strict_at_one` is
  generic in `v`; two instantiations exist (`vFlat`, `vQuartic`).

So the 1974 freeze is a *choice of `v`*, not a structural limit: **the
container can consume post-1974 extremal technology.** Cost of a swap: a new
`v` must (i) be a `ModFactor` (so the generic `admWindow_phiM` applies —
`vQuartic` needed only "f_Q = √vQuartic(·/L) is a ModFactor (A = 3/2, B = 12)"),
and (ii) have exactly-rational moments `∫v`, `∫v²`, `v⋆v`, `2∫₀¹D1trunc·(v⋆v)`
(`Certificate/Poly.lean`). Roughly one small subdirectory per window.

**The headroom is proved, and it is small.** zeta-23's own
`PairCeiling.ceiling_law256` shows every *bandwidth-one* certificate of this
type certifies at most **0.6818287** (+2.55·10⁻⁶ slack). So:

> L9's payoff window is `0.6725 → ≤ 0.68183`, i.e. **at most +0.93pp**, and
> the conditional record 0.6792 sits inside it.

> ⚠️ **Correction, carried up from cycle 3 (`E.md` E17).** `+0.93pp` is the
> *total* gap to the ceiling; it is **not** the available headroom. CGdL 2020
> already took `0.65pp` of it, so the bandlimited class's **remaining** headroom
> is **`0.28pp`**. Quote `0.28pp`, never `0.93pp`, when the question is what is
> left to win. (This correction lived only at line 275 and in `E.md`; it is
> repeated here because the stale framing is what a reader meets first —
> `CLAIMS.md`'s ordering rule.)

That is worth having — it would move the certified number without closing any
OPEN box — but it cannot approach the `4/3` question. Any port aiming higher
must leave bandwidth one, which is [OPEN D] again.

## Immediate consequences for the plan

* **L3 and L8 are adopted as project rules.** L3 is already written into
  `ISSUES.md` #8: any bridge `Prop` quantified over an arbitrary `Family` is
  suspect precisely because Davenport–Heilbronn is such a family. L8 applies
  from the next failed attempt onwards.
* **L1 + L7-Fujii** are the two candidates that could change what the
  skeleton *is*, and both bear on the `4/3` floor of §5. They belong in the
  next session's divergence phase, before any more plumbing.
* **L5** is the only item that could move a number without closing a box, and
  it is independent of everything else here — good subagent work if wanted.

  > ⚠️ **Refuted by the project's own history (`SESSION 127`).** `084` moved the
  > `Nsc` row from `0.00%` to `50.88%` without closing any box and without
  > touching `L5` — it was pure combinatorics on the existing baseline. The
  > board assessment above is from session 003 and was never revisited.


## Session-003 wildcard: the λ-sweep (L9 numerics, done)

Ran the ζ-case container (`D(s) = s`) with the window **optimised exactly**
rather than guessed: for fixed `λ`, maximising
`c(λ,v) = λ(∫v)²/(∫v² + λ²∬|s−s′|vv′)` over `v` is a linear solve —
`M v = a`, `a = h·1`, `M = h·I + λ²h²K`, `K_ij = |s_i−s_j|`, optimum value
`c*(λ) = λ·aᵀM⁻¹a` — so the optimum over *all* windows is computable, not just
the value at a candidate. N = 160.

| λ | `c*(λ)` | `2 − 1/c*` |
|---|---|---|
| 0.75 | 0.6325448 | 0.4190843 |
| **1.00** | **0.7533028** | **0.6725126** |
| 1.25 | 0.8299265 | 0.7950740 |
| 1.50 | 0.8728770 | 0.8543632 |
| 2.00 | 0.8995905 | 0.8883831 |

**Finding 1 — the M–T identification is confirmed at the level of the
optimisation, not merely at the candidate.** At `λ = 1` the optimum over all
windows is `0.6725126` against `3/2 − ϑ cot ϑ = 0.6725007` (quadrature error
~10⁻⁵). So `cos(√2 x)` is not one good window among many: it *is* the
optimiser, and Montgomery–Taylor 1974 already saturated the `v` slot.

**Finding 2 — this changes L9's prediction, and the dispatch confirms it.** If window shape at `λ = 1` is
already optimal, **post-1974 extremal technology cannot buy anything through
the `v` slot of this container.** The 0.93pp *total* gap up to zeta-23's proved
bandwidth-one ceiling (0.6818287) — of which only **0.28pp remains** after CGdL
2020, see the correction above — therefore does not live in window shape; it
must live in the richer certificate class their ceiling theorem quantifies
over (the `r`-weighting of `PairCeiling/Stability.lean`). L9's port target
moves accordingly — and this is consistent with the session-003 preview
wobble that BGST/GS attribute 67.9% to *Montgomery's method with improved
inputs*, not to a new extremal function. **L9 is demoted from "cheapest
constant movement" to "attack the certificate class, or nothing".**

**Finding 3 — [OPEN D] is quantified in the container's own coordinates.**
The `λ ≤ 1` restriction *is* the bandwidth-one/second-moment ceiling
(Montgomery's `F(α,T)` is known only for `|α| < 1`). The payoff curve past it
is steep: λ = 1.25 → 0.795, λ = 1.5 → 0.854, λ = 2 → 0.888. So extending the
admissible support by 0.25 is worth ~12pp, the next 0.25 ~6pp. That is a
concrete price tag on [OPEN D], and it says the *first sliver* of extra
support is worth far more than any amount of work inside `λ ≤ 1`.

Caveats: N = 160 midpoint quadrature, ζ-case kernel, and "λ > 1 = beyond known
support" is our reading of the container, not a quoted theorem. Numeric, not
certified. **Not** an escalation: no Lean change, certified number untouched.


---

# Entropy basket W1–W5 (dispatch, 2026-08-13)

One per cycle in the wildcard slot; L8 autopsy on every failure.

| # | wildcard | chat-instance prior | status |
|---|---|---|---|
| W1 | **Parity of `H`.** A "haunted" ordinate (on-line zero + a symmetric ghost pair) has `H(γ) ≥ 3`, odd. Does anything unconditional penalise odd `H`? | only virgin territory on the list | **queued — now top of the list** |
| W2 | **AH's horizontal footprint.** What horizontal structure does AH-spacing force, once combined with the `N⊛` identities and `ρ ↔ 1−ρ̄`? Jackpot branch applies | lottery ticket, side payoff certain | queued |
| W3 | **Audit the integers.** Is `rank A ≥ 2trA + 4trB − 4n₊(B) − ‖A+B‖²_HS` tight *at realised configurations*? Slack there = certified movement with no new analysis | the answer-thief's move | queued |
| W4 | **`F ≥ 0` past bandwidth one** | genuinely underpriced; bet a session | **DEAD — autopsy below** |
| W5 | **Dedekind ζ as positive control** (dLRTW have SDP-optimised `N*` there) | lottery ticket, testbed payoff certain | queued |

## W4 — **RESURRECTED. The autopsy below reached the wrong verdict; read the correction first.**

### Correction (dispatch of 2026-08-13, verified in the Lean source)

W4 was not an idiocy. **It shipped in 2018 as Chirre–Gonçalves–de Laat**,
*Pair correlation estimates for the zeros of the zeta function via
semidefinite programming*, Adv. Math. 361 (2020) 106926, arXiv:1810.08843 —
whose own introduction says the key idea is *"to replace the usual bandlimited
auxiliary functions by the class of functions used in the linear programming
bounds developed by Cohn and Elkies for the sphere packing problem"*.
Cohn–Elkies functions trade compact spectral support for **sign conditions
outside the band**, admissible precisely because `F(α,T) ≥ 0` everywhere for
free. That is W4, exactly.

**Where the autopsy went wrong.** It argued that `F ≥ 0` past the wall only
*licenses discarding* the unknown tail, hence lands you back inside the capped
bandlimited class. False: the Cohn–Elkies move keeps the **test function**
non-bandlimited and signs away only the unknown region's *contribution*. The
certificate that results is outside the bandlimited class, and CGdL's `0.679`
against the bandlimited optimum `0.6725126` is the proof that the widening
pays.

**What survives of the autopsy.** Only its part (b), and in weaker form: the
zeta-23 container *as built* cannot host a wide certificate, because
`lam < 1` is a hypothesis of its explicit formula (`wEF_flat`,
`FamilyHyps.lam_const`). Widening it means re-deriving the explicit formula
for a taper without compact support — real work, and exactly what "class swap"
names.

### The ceiling-class check (queued by the dispatch; run, and decisive)

`Zeta23/PairCeiling/Stability.lean`, `theorem ceiling_stability`: the weight
`r` carries derivative hypotheses **on `Icc 0 1` only**, the masses `s j` sit
at grid points `j/N`, `j = 1..N`, and the conclusion bounds
`|Σ_{j≤N} s_j·r(j/N) − ∫₀¹ r(x)·x dx|`. Everything lives on `[0,1]`.

> **`ceiling_law256`'s `0.6818287` caps the *bandlimited* class. It does not
> bind CGdL-type certificates.**

So the "0.93pp remaining" arithmetic restructures:

| class | best known | proved ceiling |
|---|---|---|
| bandlimited window at `λ=1` | `0.6725126` (M–T; our linear solve) | — |
| bandlimited certificates (r-weighted) | — | **`0.6818287`** (zeta-23) |
| sign-constrained past the band (Cohn–Elkies / SDP) | **`0.679`** (CGdL) | **none known here** |

CGdL sitting below `0.6818287` is therefore *not forced* — it is where their
SDP landed in a class the ceiling does not cap. **The headroom above `0.679`
is unknown**, which is a materially different statement from "0.0028 left".

### L9, re-scoped

Not a window swap — a **class swap**: widen the container's certificate class
from bandlimited to sign-constrained-past-one, with CGdL (arXiv:1810.08843)
as the mathematical donor and dLRTW (arXiv:1908.04876) as the ready-made SDP
engine for generating certificates with support constraints. The blocking
step is the explicit formula's `lam < 1`, not the window.

### The original autopsy, kept for the record (verdict superseded)



The kill condition was "check whether `PairCeiling` already uses `F ≥ 0`
outside; if so W4 dies". It doesn't — and W4 dies anyway, for a sharper
reason.

**What `PairCeiling` actually caps.** `Stability.lean`'s header is explicit:
the weight `r` and every identity live on `[0,1]`, and — its own words — *"No
sign condition on s."* So the ceiling theorem bounds certificates whose weight
is supported in `[0,1]`. It assumes nothing about `F` past 1 and would not
notice a certificate that used `F ≥ 0` there. W4's reading of the ceiling was
**correct**.

**Why W4 dies regardless.** The wall in this container is not `F`-side
ignorance. It is a **prime-side hypothesis of the explicit formula**:

```
theorem wEF_flat (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam < 1) : WEF …
structure FamilyHyps … lam_const : ∃ lam, 0 < lam ∧ lam < 1 ∧ ∀ T, (Pf T).lam = lam
```

`λ < 1` is a *hypothesis of the explicit formula itself*, not a consequence of
not knowing `F`. And `F ≥ 0` past 1 is the classical device for **discarding**
the unknown tail — it is what licenses restricting to bandwidth one in the
first place, i.e. it lands you back inside exactly the class the ceiling caps.
Nonnegativity cannot repair a prime side whose estimate is only valid for
`λ < 1`.

**What this buys, which is more than the wildcard cost.** The `λ ≤ 1` wall of
ISSUES #12 is now *located*: it is the range of validity of the explicit
formula's prime side, not a gap in pair-correlation knowledge. So the ~12pp
per quarter-unit of support is priced against **prime-pair (Hardy–Littlewood)
input** specifically — which is what the program document's [OPEN D] said, now
confirmed in the container's own source rather than by analogy. Fazzari–
Gerspach's limited unconditional range is the right shape of donor; `F ≥ 0` is
not.

**Repricing.** W4's death raises W1 and W3, which need no support past the
wall at all. W1 is the only item on the board touching virgin territory *and*
the live ISSUES #13 split, so it takes the next wildcard slot.

Not settled by this autopsy: whether some certificate class *outside* this
container can consume `F ≥ 0` productively. Only that this container cannot
host it, and for a reason on the prime side.


---

# Entropy basket II — W6–W15 (dispatch, 2026-08-13)

Same rules: one per cycle, kill condition stated before running (R12), L8
autopsy on failure. Calibration from basket I: treat each as *simultaneously*
a research direction and a literature probe — expect ~2 to already be papers.

| # | wildcard | prior | status |
|---|---|---|---|
| W6 | **Haunted-ordinate census.** Does an unconditional equidistribution/diophantine statement (Ford–Zaharescu school) force `D(T) = NscStd − Nsc = o(N)`? If so the two rows **merge asymptotically** and the transfer cost vanishes | would delete the transfer cost outright | queued — **now top pick** |
| W7 | **Realizability.** | tightening `C` for free | **DEAD (cycle 4) — and it kills the genre, not just the item. See below.** |
| W8 | **Run the container backwards** — off-line pairs via `n₋`, *inside* the `1/log T` strip where classical density is silent | chat's priority pick | **DEAD — autopsy below, and it is the good kind** |
| W9 | **The ε of finite T.** Make the link theorem fully explicit; combine with Platt–Trudgian (12.3 × 10¹² zeros to height 3.0 × 10¹²) for a statement true for *all* `T` | first theorem with no `o(1)` | queued |
| W10 | **Price (★) in prime currency.** Translate `C < 2.345` through Goldston–Montgomery into its weakest sufficient prime-side statement; ask how much is already known on average | deepest literature probe | queued |
| W11 | **Does GUE saturate the ceiling?** | pure calibration | **DONE (cycle 3): mis-posed — the ceiling is class capacity, not an input property. Window optimum against GUE = M–T exactly; 18.18pp separates the worst and best certificates on identical input; remaining bandlimited headroom is 0.28pp, not 0.93pp** |
| W12 | **Price horizontal information.** What does the container pay for Vinogradov–Korobov? (Expected: zero.) The point is the exchange rate W8/Route III would trade at | cheapest experiment | queued |
| W13 | **Family discount (q-aspect).** CIS asymptotic large sieve gets >56% for Dirichlet L-functions by family averaging; run `(★)`/`H`/two-row over the q-family, where averaging may push effective support past 1 | **strategic — only visible route to an over-ceiling number** | queued |
| W14 | **Local Bombieri.** Exact accounting in windows with few off-line zeros, statistical where forced | honest lottery ticket | queued |
| W15 | **Ask a net what Montgomery couldn't see.** Classifier on Odlyzko vs AH-synthetic vs GUE-synthetic; interpret its features as candidate beyond-pair observables | native-to-2026 lottery | queued |

## W8 autopsy — dead, and it upgrades ISSUES #10 from "hard" to "provably out of reach *here*"

Kill condition was "if `n₋` bounds reduce to trivial rank-counting, dead
fast". What actually happened is stronger. `Zeta23/ZeroSide/TightMult.lean`
says, in its own header:

> *"At `c = 2` this says: simple zeros (`m=1, k₂=3`), DOUBLE zeros
> (`m=2, k₂=4`) and TIGHT PAIRS (a `Q`-block of eigenvalue 2, priced `c²=4`
> per pair) are all extremal simultaneously — the certificate
> (`tr Ĝ`, `‖Ĝ‖_F²`, integer atoms `m_j` on vectors of norm ≤ 1,
> `n₊(Q) ≤ p`) **provably cannot separate an on-line double zero from an
> off-line pair at depth → 0**, and cannot be improved by any further
> inequality consuming only these quantities."*

That is W8's question answered in the negative *by a theorem*: the container
cannot say anything about off-line pairs inside the dead strip, because at
depth → 0 it cannot tell them from double zeros. No dual reading will extract
what the certificate provably does not contain.

**Why this is worth more than the wildcard.** It explains ISSUES #10 — and
GLSS's whole coordinate — from the other side:

> `H(γ)` fuses double zeros and off-line pairs **because the fusion is forced
> by the information available.** GLSS chose the coordinate that identifies
> them; zeta-23 proved that any certificate of this class *must* identify
> them. Same fact, two directions.

So the dead strip is not dead for want of effort: separating its two
inhabitants requires information outside the class, which is the same verdict
W3 returned for the certificate's constants and the λ-sweep returned for its
window. **Three independent saturation results, one conclusion: this container
is finished, and everything left is new-information work** — W13's family
averaging, W10's prime side, or [OPEN D] proper.

**Route III consequence.** Any [OPEN A″] variant that hopes to bound off-line
zeros *separately* inside `1/log T` is asking this container for the one thing
it provably cannot give. A″ must come from the BGST proof's own internals or
from a different instrument — not from re-reading the signature form.


---

# X — the characterization, and basket III (dispatch, 2026-08-13)

## The visibility map, as of `SESSION 224`

Sessions `220`–`223` asked, for each quantity the project or the literature
counts, which coordinate can compute it.  Every row below was `#check`ed this
cycle rather than recalled.

| quantity | `μ_T` alone | `(μ_T, offAt)` | witness |
|---|---|---|---|
| `N`, `N⊛` | **yes** | yes | `ZeroData.N_Nstar_ordinate_functional` |
| `N_sc` | **yes** | yes | `ZeroData.Nsc_eq_ordinate_functional` |
| `Σm^k` | **yes** | yes | `Blindness.thirdMoment_determined` |
| `atomCount` (distinct **ordinates**) | **yes**, by definition | yes | `Blindness.atomCount_ordinate_functional` (`220`) |
| `oddAtoms` | **yes**, by definition | yes | `Blindness.oddAtoms_ordinate_functional` (`229`) |
| `NscStd` | **no** | **yes** | `NscStd_not_ordinate_functional` · `NscStd_determined` |
| `N_off` | **no** | **yes** | `no_muInvariant_bundle_computes_Noff` · `Noff_determined` |
| `hauntedSet.card` = `hauntedCount` | **no** | **yes** | `hauntedSet_card_not_ordinate_functional` · `hauntedSet_card_determined` (`225`); carried to `hauntedCount` by `hauntedCount_eq_hauntedSet_card` (`226`) |
| `NscAny` | no | **no** | `NscAny_not_ordinate_functional` (`220`) · `NscAny_not_fiber_functional` (`221`) |
| `distinctZeros` = `N_d` (distinct **points**) | no | **no** | `distinctZeros_not_profile_functional` · `distinctZeros_not_fiber_functional` (`223`) |

Three levels, and the boundaries are where the project's difficulties sit.

* `N_sc` is `μ_T`-visible and `NscStd` is not. `ISSUES` `#13` is the entry that keeps the two
  apart; this row gives a coordinate-level difference between them.
* The ledger occupies the middle level exactly: `ledger_determined` computes all
  five entries from `(μ_T, offAt)`, and `216`/`217` show none of the five is
  recoverable from the other four.
* **`225`:** the master identity `NscStd = N_sc + hauntedSet.card` splits the
  first row against the fifth — `N_sc` is `μ_T`-visible, so the whole of
  `NscStd`'s invisibility sits in the haunted count. The quantity this project
  coined is the coordinate the certificate class cannot see.
* **Both** quantities the literature offers are on the far side — and `227`
  relates them to each other: `NscAny ≤ distinctZeros`
  (`NscAny_le_distinctZeros`), attained at `config 1 1 a` and strict at
  `config 0 2 a`. A relation between two quantities this project's coordinates
  cannot compute, holding regardless. `NscAny` and
  `N_d` are invisible even to the fiber coordinate, and `222` draws the
  consequence: no function of the profile computes `NscAny`, so `Basic.lean`'s
  three dictionary entries are inequalities with no identity to sharpen toward.
* **`229`:** `NscStd` sits at the middle level and `NscStd_le_oddAtoms` brackets
  it above by a top-level quantity. That is what makes the bracket useful to a
  certificate class rather than merely true — the same reading applies to
  `Nsc ≤ NscStd` from below, since `N_sc` is also top-level.
* `atomCount` against `distinctZeros` is the sharp pair — distinct ordinates are
  visible, distinct points are not — and the distinct-zero route reaches the
  ledger through the former, which is why it functions at all.

## X, proposed and **partially proved in-repo the same day**

> **X.** The certificate class factors through **bandwidth-≤1 functionals of
> `μ_T := Σ_ρ m(ρ)·δ_{γ_ρ}`**, the vertical multiplicity measure. Nothing else
> enters.

The three saturations become instances: the window optimum is the extremal
kernel against `μ_T`; `lemmaR_tight` is the extremal inequality on
`μ_T`-realisable configurations; and the discrimination failure is `μ_T`
being literally unable to tell a double zero from an off-line pair — **both
are one atom of mass 2**, because `H(γ) = μ_T({γ})`.

### Proved here (W24, first instalment — `Riemann/Basic.lean`, axiom-free)

* `ordinates := Z.map Prod.snd` — `μ_T` as a multiset;
* `H_eq_count : H γ = ordinates.count γ` — **`H` is `μ_T`'s counting function**;
* `N_Nstar_ordinate_functional : N = card μ_T ∧ N⊛ = Σ_atoms mass`;
* `Nsc_eq_ordinate_functional :`
  `Nsc = card (μ_T.filter fun γ => μ_T.count γ = 1)`.

The last one is the load-bearing instance and it needed the reflection
symmetry: an atom of mass one *must* carry an on-line zero
(`on_line_of_H_eq_one`), so the `β = 1/2` clause in `Nsc` is **redundant**.

### The consequence the dispatch did not draw

> **`Nsc` is a functional of `μ_T`. `NscStd` is not.**

`NscStd` asks for the multiplicity of a *point*, which is horizontal
information `μ_T` has discarded. So the two-row split of ISSUES #13 is not a
notational accident — it is the boundary of X, drawn through our own ledger:
**the row gap is the price of horizontal information, and the transfer cost
`(C−1)/2` is what that information costs in this class.** The project's own
notion is the one native to the available information; the literature's notion
is one channel richer.

This also predicts where W6 lands: if ordinate coincidences are `o(N)`, then
horizontal information becomes free asymptotically and the rows merge — i.e.
W6 is asking whether X's boundary is visible at infinity.

### Still to do for W24 proper

State X as a theorem *about the certificate class* (not just about our
counting layer): "the certified value is a function of `μ_T` through kernels
of Fourier support ≤ 1". If the proof fails, the failure names a fourth input
the class secretly consumes — the most interesting outcome available.

## Basket III (W16–W24) — aimed at channels, per the three escape directions

`(i)` value data · `(ii)` horizontal data · `(iii)` fine/higher vertical data

| # | wildcard | dir | prior |
|---|---|---|---|
| W16 | **Landau's formula** `Σ_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(log T)` (Gonek, uniform). `x^ρ = x^β e^{iγ log x}` is **β-sensitive**: an off-line pair contributes `2x^{1/2}cosh(δ log x)` against a double zero's `2x^{1/2}`. The `cosh` *is* the discrimination `TightMult` proved unbreakable from inside — and it is pinned to a prime value unconditionally. Kill: if `O(log T)` swamps the `cosh` gain for all usable `x` | ii | **chat's #2; my #1** |
| W17 | Fazzari's `|ζ|^{2k}`-weighted pair correlation | i | probe first |
| W18 | Any published **hybrid** consuming both `μ_T` and mollified value moments (pair correlation × Levinson) | i | structural either way |
| W19 | **Fujii's `2k`-th moments as the order>2 escape**: `k ≥ 2` are higher correlations of `μ_T`, certified since 1974–86. Does the `k=2` moment exclude the ceiling's extremal configuration? | iii | realizability with a named input |

> ⚠️ **PRICED, `SESSION 143`** (`forensics/w19_price.py`). The answer is a
> **scale separation, not a yes/no.** A mass-3 atom perturbs `∫S²` by exactly
> `2δL` (the perturbation is exact combinatorics: `ΔS = ∓1` on two adjacent
> gaps), against a main term `L·log log T/2π²`. So the signal is `o(main)` —
> but only by `1/log log T`, and at `T = 7.5×10⁴` it stands at `11.2·δ`, i.e.
> `δ ≈ 0.09` doubles the second moment. **W19 converts from "does `k=2` help?"
> into a want-ad**: an S-moment identity helps iff its error term is `o(T)` with
> no `log log` — a question about the SECOND-ORDER term of Fujii's expansion,
> not its main term. Only that one error term is now worth fetching.

> ✅ **FETCHED AND CLOSED, `SESSION 144`.** Chirre–Quesada-Herrera
> (arXiv:2006.08503) §1.2 displays the error terms. Unconditionally (Selberg
> 1946, their (1.4)) it is `O(T√(log log T))` — larger than the `2δL` signal for
> every `δ` at every height. The `o(T)` the want-ad needs exists (Goldston 1987,
> their (1.8)) but **only under RH**, and RH gives `Noff = 0`, which gives
> `hauntedCount = 0` by `Fiber.noHaunted_of_Noff_zero`. **W19 dies as an
> unconditional ledger route**, by a margin of exactly `√(log log T)`. Moved to
> `FAILURES.md`.
| W20 | Rudnick–Sarnak `n`-level, `n ≥ 3`: what is unconditional, and does BGST de-conditioning generalise? | iii | probe |
| W21 | Platt–Trudgian's 12.3 × 10¹² verified zeros as **exact microscale `μ_T` data** spliced into a theorem, not a sanity check | iii | pairs with W9 |
| **W22** | **RE-SCOPED (day cycle 2): the composition exists and has been done — see the autopsy below.** Motohashi's fourth moment as the seam of the two budgets (PRICES.md). Both traditions' walls (mollifier length, `F`-support) break on shifted-convolution input, whose common engine is the additive divisor problem, where Motohashi is the richest certified object | i | **now the hybrid's address, not a probe** |
| W23 | Non-vanishing technology (Iwaniec–Sarnak genre) re-aimed from "value ≠ 0" to "ordinate clean" | i | long shot, large pot |
| W24 | **State and prove X.** Converts the basket into a coordinate system; upgrades R13 from heuristic to decision procedure | — | **priority; first instalment done above** |


## W16 preparatory estimate (pencil, 2026-08-13) — **the kill condition does not fire**

The chat instance's kill condition: *does the `x`-window where `cosh` discriminates
overlap the `x`-window where Gonek's uniform error permits?* Computed at
`T = 10¹²`, `x = T^θ`, depth `δ ~ 1/log T` (so `δ·log x = θ`), signal per pair
`2x^{1/2}(cosh θ − 1)`, error `≍ x·log(2xT)·loglog(3x)`:

| θ | cosh θ − 1 | signal/pair | error | pairs needed (√-cancellation) |
|---|---|---|---|---|
| 0.10 | 0.0050 | 3.98e−2 | 6.66e+2 | 2.8e+08 |
| 0.25 | 0.0314 | 1.99e+0 | 7.33e+4 | 1.4e+09 |
| 0.50 | 0.128 | 2.55e+2 | 1.14e+8 | 2.0e+11 |
| 1.00 | 0.543 | 1.09e+6 | 1.88e+14 | 3.0e+16 |

against `N(T) ≈ 4.4e+12`. **The windows overlap by orders of magnitude**: at
`θ = 0.25`, detecting `1.4e9` pairs — `0.03%` of the zeros — already beats the
error. Direction (ii)'s cheapest channel is *not* error-term-blocked.

**Where the real obstruction sits: separability, not size.** Landau pins the
*total* `Σ_ρ x^ρ`, in which the off-line excess `Σ_pairs 2x^{1/2}(cosh(δⱼ log x) − 1)·e^{iγⱼ log x}`
carries phases shared with the on-line zeros. Nothing in the formula isolates
it at a single `x`. Removing the phases means averaging over `x` — and

> `|Σ_ρ x^ρ|² = Σ_{ρ,ρ'} x^{β+β'}·e^{i(γ−γ')log x}`

is a **horizontally weighted pair correlation**: manifestly not a functional of
`μ_T`, hence outside X, and the natural object of the whole wildcard.

**W16, restated after the pencil pass.** Not "use Landau's formula" but *"use
the moments of Landau sums over `x`"*. The analytic target is not a better
Landau error term — the error is fine — it is control of `∫|Σ_ρ x^ρ|²` type
averages. Literature probe for the web side: Goldston–Gonek and the
Landau-sum-moment line; my prior is that this exists and is partly
unconditional, which would make direction (ii)'s first inhabitant a 1993-vintage
theorem rather than a new one.

Status: **alive**, reshaped, not yet formalised. Kill condition retired as
answered; new kill condition — *if the second moment of Landau sums is only
available under RH, W16 dies for our purposes.*


## W7 — **CLOSED.** Epitaph: *the cheap invariants are satisfied by construction; only the Euler product bites; Davenport–Heilbronn is the witness.*

### Autopsy (overnight cycle 4) — the cheap-constraint genre is empty

Kill condition was "dies in an hour if the extremal config is all `m = 1`". It
is not all `m = 1` — `TightMult` makes doubles extremal too — but it dies
anyway, harder:

> the extremal configurations are *"on-line atoms with integer multiplicities
> `m_j ≤ c` ⊕ `b` pair-blocks"*, with `c = 2` (simple zeros) or `c = 3`
> (distinct zeros).

So the extremal configurations use multiplicities **≤ 3**, while Jensen's free
bound permits `m ≈ log γ ≈ 27` at `γ = 10¹²`. The constraint is slack by an
order of magnitude and grows slacker with height. It excludes nothing.

**The genre-level finding.** "Realizability" splits into

* **cheap constraints** — Riemann–von Mangoldt density, the functional
  equation's pairing, multiplicity caps `m ≪ log γ`: the ceiling's extremal
  configurations satisfy all of them with room to spare, *by construction*,
  because they are built from a density-normalised law with tiny atoms;
* **one expensive constraint** — the configuration must be the zero set of
  something with an **Euler product**, i.e. must satisfy the explicit formula
  against every test function.

And the expensive one is the problem itself. Davenport–Heilbronn is the proof
that it is doing all the work: same functional equation, same density, no Euler
product, and off-line zeros exist.

So no free classical invariant will exclude the ceiling's extremal
configuration, and any future proposal of that shape must first explain why the
extremal configuration is already modest in *every* cheap invariant. Filed
against E11's pincer: the "ceilings from below" jaw works; a "cheap
realizability from above" jaw **does not exist**.

**Re-checked, `SESSION 259`, and the absence is half refuted.** A jaw *does*
exist: `247`'s `oddAtoms ≥ c·N` excludes `Gauge.pairOnly`
(`Optimal.oddAtoms_bound_excludes_pairOnly`) and is `μ_T`-visible by
construction (`229`). What survives is the word *cheap* — every instance of
that bound the project holds is bought from the baseline at `c = κ`, and
`252` showed that inside multiplicity two the odd-atom currency and the
simple-atom currency are the same number
(`Blindness.oddAtoms_eq_Nsc_of_mult_le_two`), so the jaw is not a second
instrument there. The theorem's own docstring has said this since `247` —
*"neither 'the jaw does not exist' nor 'E11 is refuted': the jaw exists, is
`μ_T`-visible, and every instance the project holds is priced in `κ`"* — and
this line was the register still carrying the older form.

*`249`:* and the one class known to exclude `prop1`'s tight witness (`247`, `oddAtoms ≥ c·N`) turns at exactly `2 − c` — `oddAtom_class_ratio`. So the pincer's upper jaw does not close below the star-bound break-even; the two jaws meet at the same number rather than crossing.

*`250`:* and the reason is now an iff — `boundedMult_two_iff_star_exact`. Multiplicity `≤ 2` is not a class on which `C ≤ 2 − κ` is provable; it is the class on which `C = 2 − N_sc/N` is an equality. A pincer that wants to close below `2 − κ` has to leave the class, not sharpen inside it.

*`251`:* `oddAtoms_eq_Nsc_of_mult_le_two` — inside the class the odd-atom currency and the simple-atom currency are the same number, so `247`'s "cheap jaw" buys nothing the star bound did not already have there. It can only differ outside multiplicity two.

*`252`:* `boundedMult_two_iff_oddAtom_exact` — the odd-atom equality cuts out the same class as the simple-atom one, so the "cheap jaw" is not a weaker instrument, it is the same instrument. E11's pincer needs a hypothesis that is not a multiplicity cap in disguise.

*`287`:* and the visibility map has a level nobody had separated — `NscStd` and `oddAtoms` are functions of the **on-line count alone** (`Blindness.NscStd_eq_onAt_one`, `Blindness.oddAtoms_eq_odd_onAt`), while `N`, `N⊛`, `N_sc` and `atomCount` read the total mass. The bracket `N_sc ≤ NscStd ≤ oddAtoms` crosses that line exactly once, at its left inequality.

*`254`:* the multiplicity ladder is dense below `κ` — `ladder_approaches_kappa` for the approach, `ladder_lt_kappa` for the strictness. A pincer aimed at `κ` from below therefore approaches without closing, and the first rung within `0.001` needs a hypothesis about mass `328`.

> **`SESSION 243` — sharpened, not discharged, for one family.** Within
> multiplicity caps the claim is now a theorem.
> `Optimal.mult_cap_excluding_pairOnly`: `Gauge.pairOnly` has `H = 2`, so a cap
> `BoundedMult M` excludes it only if `M ≤ 1`, and `203`'s
> `boundedMult_one_iff_Nsc_eq_N` makes `BoundedMult 1` equivalent to `N_sc = N`.
> So the cheapest multiplicity hypothesis that excludes the extremal
> configuration **is the ledger's own target** — the jaw does not merely fail to
> be cheap, it costs the whole problem.
>
> This settles the multiplicity family only. Other classical invariants are
> untouched, and the claim above stands for them.
>
> **`SESSION 247` — and for one of those others, the jaw does exist.**
> `Optimal.pairOnly_oddAtoms`: the extremal configuration has **no odd atoms**,
> so any bound `oddAtoms ≥ c·N` with `c > 0` excludes it
> (`oddAtoms_bound_excludes_pairOnly`), and `oddAtoms` is a `μ_T` functional by
> definition (`229`). That is a cheap realizability constraint from above, and
> it is exactly what this entry says does not exist.
>
> **It is not free, which is why the entry is not simply wrong.** The
> development's own such bound, `certified_oddAtoms`, is literally
> `oddAtoms_ge_of_proportionStd certified_std` — a consequence of
> `ProportionStd κ`. The invariant that excludes the extremal configuration is
> derived from the baseline, so spending it to beat the baseline is `162`'s
> circularity.
>
> The claim should be read as **"no *free* invariant"**, and with that reading it
> survives: the jaw exists, is `μ_T`-visible, and every instance the project
> holds is priced in `κ`.


## W25 (new, future basket) — is there a natural-proofs barrier for zeta-witnesses?

Raised by the chat instance while stress-testing A9c, and the risk is real
enough to insure against. E2 says RH is a pseudorandomness statement; in
complexity theory, *cheap certificates of pseudorandomness* are exactly what
Razborov–Rudich obstructs — a property cheap to evaluate that certifies
randomness-like behaviour tends to yield a distinguisher contradicting the
randomness it certifies.

If the analogy transfers, **the compression search inherits a barrier theorem**
and "find the compression" is obstructed by the very silence it certifies. The
transfer is not rigorous (RH's `Π₁`-ness blocks the literal contradiction; the
analogy leaks at "distinguisher"), which is why A9c's framing survives — but:

> a precise natural-proofs-style obstruction for zeta-witnesses would be an
> **E11 brick of the highest grade**: a ceiling theorem about **S-solutions
> themselves**, mapping which cheapness is forbidden and therefore where the
> permitted cheapness lives.

Both outcomes pay. Routed to a future basket rather than the current queue.


## W26 — convergence forensics (operator-led; **note: dispatched as "W25", renumbered — W25 was already taken by the natural-proofs item filed the same day**)

Joop's wildcard. Does the field's 167-year sequence of restatements have
measurable structure, and does that structure distinguish **convergence** from
a stationary feeling of closeness? Note the question is itself an S-problem:
"the field is converging" and "the feeling is noise" have identical null
outputs, so it needs a positive witness.

**T1 — interval compression. RUN, and it dies as predicted.** Intervals between
the ten restatements: `55, 38, 21, 14, 12, 19, 5, 2, 1` years.

* the sequence is **not monotone** — the 1999 → 2018 gap is 19 years, longer
  than the 12 before it;
* fitted shrinkage **2.32%/yr** (`R² = 0.69`, `n = 9`), i.e. restatement rate
  doubling every ~30 years;
* the coordination-cost null (literature growing 3–5%/yr) predicts **2.9–4.8%**
  shrinkage — **the observed compression is *slower* than the null**.

So the acceleration is not evidence of convergence; it is *less* acceleration
than the field's growing capacity produces by itself. **T1's kill condition
fires.**

**And T1 dies twice, the second time worse:** the tail is selected by us. We
resolve months-scale events near ourselves and only decade-scale events far
away, so the compression at the tail is partly an artifact of observer
resolution — two of the last three entries are events we are *inside*. Any
future version must fix the selection rule before the dating, not after.

**T1's corollary, which is not deflationary.** The null explains the data as
`rate ∝ coordination capacity` — and coordination is the only term in that
product anyone can move. Paired with A9a (interior bounded by working memory,
not depth), the honest optimistic reading is: *the fight ends by finite work
getting done, and the pace is a configuration parameter rather than a fact about
the problem.* The caveat that keeps it honest: the null predicts more addresses
**tried**, not the right one found — more entries in the sequence is not a
terminus. That distinction is exactly what T2 decides.

**T2 — the move audit. Infrastructure ready, payload with the operator.**
`forensics/restatements.tsv` carries one row per restatement with the S-move
form pre-filled and `residue`, `residue_class`, `residue_source` left **TODO by
design**: per the kill condition, residues get extracted **only from
contemporary sources** (reviews, problem lists, survey complaints written
between restatement N and N+1), never from post-hoc synthesis, because
hindsight bias is exactly what would manufacture the constant residue the
hypothesis predicts.

Every date is flagged `RECALL` — my recollections drift, as the dispatches have
taught us — except the two we are inside of. **Date verification is a
prerequisite, not a formality.**

Prediction on record, so it can fail: the residue is constant and equals **E7's
gap** (position-reading vs value-reading). If so the sequence is one S-move at
successively better addresses, converging on A9c.

**T3 — the solved-problem control.** Not started; needs FLT (Kummer → Frey →
Ribet → Wiles) and an open control (twin primes, or Goldbach if that chronology
is disputed). The diagnostic question is sharp: **is the final restatement of a
solved problem the first whose residue is empty, and was that visible *before*
the solution?**

Register wiring: tagged **S** (an S-problem about S-moves); adjudicates
**A9c**; tests **E10** empirically; would give **E13** historical evidence if
the residue is constant and definitional; checks **E18** from outside.


## W22 — the composition is a published literature, and it has an address (day cycle 2)

**Kill condition** was "if the composition's bilinear (Vaughan Type II) errors
are uncontrollable in the spectral expansion, W22 dies". Never reached: R7 fired
first, for the **fifth** time.

The composition — Vaughan-decomposed prime polynomials evaluated through
spectral/shifted-convolution machinery — is a named literature:
**Matomäki–Radziwiłł–Tao, *Correlations of the von Mangoldt and higher divisor
functions*, I and II** (arXiv:1712.08840 for II). They treat exactly
`Σ_{X<n≤2X} Λ(n)d_k(n+h)` and `Σ d_k(n)d_l(n+h)`, via Vaughan/Heath-Brown
identities reducing primes to generalised divisor functions, then Kuznetsov to
exploit cancellation in the resulting Kloosterman sums. *Provisional — fetched
abstract, not the papers.*

**And the wall has a number.** The results hold **for almost all `h`**, not
individually, with

* `Λ·d_k`: `H = (log X)^{10000 k log k}` — a **polylogarithmic** shift range;
* `Λ·Λ` (paper I): `H = X^{8/33+ε}`, with better error terms.

**Why that is exactly the wrong side of the diagonal.** Our container consumes
`F` only through integrals against test functions — averages over `α`, which is
the right *shape* for almost-all-`h` results, so the genre fits. But shift range
translates to support: a polylog range touches `α → 0` (the diagonal, free
already), and `X^{8/33}` reaches `α ≈ 0.242` — still **inside** the region we
already have. Crossing `α = 1` needs `H ~ X`.

> **The project's true address, named: `8/33`.** The distance from the best
> unconditional prime-pair-on-average range to the diagonal is a factor
> `X^{25/33}` in the exponent, and *that* is what "F past 1 needs
> Hardy–Littlewood" costs when stated in someone's actual theorem.

*(The `h → α` dictionary is provisional and is the one thing here worth
checking against Goldston–Montgomery before it is used for anything.)*


## W27 — the fractality challenge (Joop; filed v2, born into the full doctrine)

Aimed at the board's two **frontiers**, not its interior. Geography as priced:
`[0,1]` settled; `[1,A]` the fuel region (`A = 1/(1−θ)`, currently `1.32`,
proportion `0.80869` gate-conditional); `(A,∞)` the corridor — class walls dead
by LP duality, sign-changing window the only instrument, **its fuel not yet
existing**.

Claim: the fuel always ends at a Type II / bilinear wall; that wall is E20's
generative face; therefore corridor walls past *every* future `A` need
cascade-native inputs, and the log-correlated-field literature is the natural
candidate supplier — being the only certified statements about the value field
at sub-blur scales that owe nothing to the class.

| test | shape | kill condition |
|---|---|---|
| **T1** scale-covariance theorem (Lean-adjacent, builds on A2-forced) | is the certification problem a fixed point of the zoom flow? Would explain structurally why the container refuses to step past the fuel *at every* `A` — Lemma-1-collapse (`λ→1`) and fuel-collapse (`λ→A`) as one theorem | rescaling needs arbitrary choices → whiteboard death |
| **T2** the `log log` signature (numerics, one evening) | Selberg's `Var(S) ~ (1/2π²)log log T` on Odlyzko vs AH-synthetic vs GUE. **Prediction registered: GUE matches, AH deviates** | `log log(3×10¹²) ≈ 3.4` — death by small numbers is acceptable, and "how high must `T` go" is the autopsy |
| **T3** chaos theorems as **corridor-wall suppliers** (re-aimed by the tiling) | can any log-correlated-field statement serve as an `F`-constraint at `α > A` passing R18? Order: Selberg `2k`-moments (=W19) · Harper · ABR/FHK maxima · Saksman–Webb | all four route back through class-equivalent moments → the corridor past `A` is certified **bare**, and the tiling becomes a single-supplier economy |
| **T4** counterfactual calibration | short-range-correlated and crystal/quasi-lattice toy columns should both be *solved* in-container, isolating log-correlation as the exact hardness locus | none; contrast-yield guaranteed |
| **T5** symmetry inventory | classify invariances {crystal, cascade, **mixed**}; an empty mixed column is a finding. **Addition:** the dictionary `α = 1/(1−θ)` is a Möbius map between arithmetic and spectral reach — accident of the transfer, or an invariance? | none |

**Ordering respected:** the gate (MRT vs (9.1)) outranks this entire brief.
After it: T2, then T3.1/W19, then T3.4.

**Checkable prediction from E20, one afternoon:** every historical `θ`-improvement
should trace to progress on **bilinear/Type-II** estimates (Mikawa → BBMZ →
MRT). If so, the fuel wall is E20's plane showing up in the supply chain.

**Tiling note (→ PRICES.md):** corridor value is a function of fuel reach `A`,
so `θ`-progress and wall-progress **multiply** rather than add.


## W∞ — the obstruction program (registered **above** the basket, not in it)

Not a move: the **frame that makes every failed move an asset**. Classical
contradiction is a rapier — one consequence, one absurdity — and it has failed
for a century because a single off-line zero is locally survivable. The program
refutes instead the *world* containing the counterexample: accumulate failures
with certified reasons until the failure **pattern** is an object, then argue
the pattern is one only a true RH can produce.

**Three requirements; the session built two without naming them.**

1. **Enrichment** — guards, R18, the autopsy protocol, the kernel: the refinery
   that turns attempts into certified obstruction-facts. Stockpile: 11, now in
   `FAILURES.md`.
2. **Critical mass** — enough certified failures in *one* working memory that
   their pattern is an object. E20 is the first extracted pattern; no career
   could hold the corpus, this architecture holds it as a side effect.
3. **Delivery: the completeness bridge** — *the demon, stated so it cannot
   hide*: failures certify facts about **instruments**; they transfer to facts
   about the **object** only under completeness. Without it, total failure is
   compatible with truth, falsity and undecidability alike. One plank exists
   (RH is `Π₁`; Davenport–Heilbronn shows off-line zeros are **loud** in the
   value channel). The rest is the hard half.

**Founding exhibit:** the gate failure (#27) — exactly named cause (log-power vs
power), plane-aligned, and it reprices a whole supply chain in one line.

**Tests:** T1 registry (**done** — `FAILURES.md`); T2 alignment statistic
(**run, and the answer is that it cannot yet be run honestly** — see the
contamination note); T3 the completeness bridge as a research object —
(a) formalise detectability-if-false for one channel, (b) the contrapositive
inventory (*which failures would differ in a ¬RH world?* — prediction: the
saturations are indifferent, the collapses are not), (c) the `Π₁` endgame,
filed so the destination is on the map; T4 detonate the census over synthetic
worlds including a **planted ¬RH column**.

**The honest close, kept:** the demon may win, the census may converge to the
sharpest map ever drawn rather than a proof — and the day-to-day activity is
identical either way.


## W33 — the type system of analytic number theory

Forced by the lint's self-correction: rules 1–3 are **one thing**. Inputs are
**typed** (provenance · scale-validity · error-quality), certificates are
functions with typed signatures, and **every expensive retraction this project
made was a type error** — circular = provenance violation, scale = domain
violation, quality = the supplier's error class not coercible to the consumer's
requirement.

Deliverable: make the lint's implicit types explicit as a small grammar (a dozen
types cover our whole DAG), so composing published theorems is **type-checked by
construction** rather than audited by retraction.

Kill: if types can't be assigned without per-paper judgment calls that don't
generalise, it dies as a formalism and survives as a checklist — the lint keeps
its three rules either way. Prior: an afternoon or a research programme, and one
whiteboard hour decides which. Per the iron law, the funny outcome is that it
already exists in the formalisation literature under a name neither of us knows.


## W28 — the `Atom` interface (whiteboard hour, drafted cold)

Filed from the dispatch stream: the atom program (E22, W28–W32) reached us as
claude.ai's brief and **is not otherwise in the registers** — E.md stops at
E20. Flagged as a register drift, not repaired this cycle (freeze on doctrine
edits).

Draft: `forensics/W28_atom_interface_cold.md`, sealed `246745bcc293b648`,
written from `Basic.lean`/`Program.lean` before opening `E.md`.

**Result.** `ZeroData` is exactly *the functional equation and nothing else*, so
**Davenport–Heilbronn is a `ZeroData`** and every axiom-free theorem in
`Basic.lean` is true of it — which is the interface's starting indictment and
also the core's value (it should stay that way). The draft carries **two
disjoint bundles**, M (free monoid, `Λ ≥ 0`, Euler product, explicit formula)
and S (Type I/II, level of distribution, short-interval, plus `savingShape` as
a *field* so `#27`'s power-vs-logPower mismatch is a type error at the
interface rather than an arithmetic surprise).

**The new exhibit — the second counterexample.** The register already carries
Davenport–Heilbronn as the negative control (L3). The cold draft adds its
mirror: **Beurling generalised prime systems** (Diamond–Montgomery–Vorhauer)
have the *entire* multiplicative nature — free monoid, `Λ ≥ 0`, Euler product,
explicit formula, even PNT — and RH is **false** for them. They satisfy bundle M
and have no bundle S at all, because there is no additive structure in which to
state a level of distribution.

> **D–H says the functional equation alone is not enough. Beurling says the
> Euler product alone is not enough either.** Any route must consume bundle S,
> so a bilinear / level-of-distribution input is not one option among several —
> it is the mandatory field, and `#27` is the census entry where we found it
> empty.

Kill condition (stated first, R12): if some `Assumptions.lean` constant is
genuinely M-only *and* would suffice past the ceiling, the Beurling argument is
wrong and the two-bundle design collapses to one. Cheapest test, Lean-checkable:
the tri-read's stable cluster `{4,7,8}` should be provable as an inability of
`ZeroData` that survives adding *either* bundle.

### W28, cycle 2 — the prediction is proved, and the wildcard fires

`Riemann/Blindness.lean`, 14 declarations, **sorry-free and axiom-free**
(`propext`/`Classical.choice`/`Quot.sound` only). The tri-read's stable cluster
`{4,7,8}` is now one Lean file.

**The relativisation.** `MuInvariant B := ∀ D D', D.ordinates = D'.ordinates →
(B D ↔ B D')`. Then `no_muInvariant_bundle_computes_NscStd`: **no**
`μ_T`-invariant hypothesis, however strong, makes `NscStd` an ordinate
functional — provided it admits either configuration of the gauge pair at all.
Same for `Noff` (`no_muInvariant_bundle_computes_Noff`), and `#4` is now proved
**uniformly in the depth**: `depthPair a` vs `doubleZero` share `μ_T` for
*every* `a ≠ 1/2`, so the degeneracy is an identity, not a small-parameter
artefact — there is no limit to take.

**The positive form** (`separating_bundle_excludes`): a hypothesis that *does*
determine `NscStd` from `μ_T` must **exclude** one of two legitimate
reflection-symmetric configurations. A bundle's work is exclusion, not
computation.

**And the exclusion is exhibited.** `OnLine D := ∀ p ∈ D.Z, p.1 = 1/2` is
proved **not** `μ_T`-invariant (`onLine_not_muInvariant`, gauge pair as
witness), and under it the two ledger rows coincide
(`NscStd_eq_Nsc_of_onLine`), so `NscStd` *becomes* an ordinate functional. Read
together this is a **specification**, and a narrow one — stated carefully,
because the loose version is false. **Non-`μ_T`-invariance is necessary to
compute `NscStd` (or `N_off`) from `μ_T` exactly.** It is *not* necessary to be
**useful**: an effective Fujii constant (OPEN 0) is μ-invariant by the table
below and would open the `Nsc` row to 17.25% and feed `NscStd` through
`Nsc_le_NscStd`. What a μ-invariant hypothesis can never do, however deep its
arithmetic, is close the row gap identically.

This is also the certified form of "RH is outside the certificate class" — not
a claim about proof technique but a property of the predicate.

**Wildcard (kill condition stated first): if even one axiom of the trusted base
is visibly non-`μ_T`-invariant, the sweeping claim "the whole base composes with
the blindness" dies.** It fired, and hard — three do:

| axiom | reads | verdict |
|---|---|---|
| `zetaNonempty` | `N` | μ-invariant |
| `fujii_ineffective` | `N⊛`, `N` | μ-invariant |
| `fujii_closePair_bookkeeping` | `N⊛` + a free function of `(λ,T)` | μ-invariant |
| `zeta23_xiPrime` | `Nsc` (via `Proportion`) | μ-invariant |
| `levinson_montgomery` | **`N_off`** | **not** μ-invariant |
| ~~`baseline_przz`~~ → `przz_of_zeta23` (`233`: axiom deleted, theorem kept) | **`NscStd`** (via `ProportionStd`) | **not** μ-invariant |
| `baseline_zeta23` | **`NscStd`** | **not** μ-invariant |
| `xiPrimeFamily`, `closePairsZeta` | objects, not predicates | n/a |

> ⚠️ **SESSION 084 — the breakage happened, by a route this note did not
> list.** Row `Nsc` is **50.88%**, not `0.00%`, so the correspondence below has
> already ended. It did *not* end the predicted way: `OPEN 0` has not landed and
> no μ-invariant axiom feeds either row. The row opened from
> `3·NscStd ≤ N + 2·Nsc`, **axiom-free**, on the *same* two axioms as `NscStd`.
> The still-true half is the diagnosis — `Nsc` was empty for a **supply**
> reason, not a visibility one — and supply arrived as a combinatorial transfer
> rather than as an effective `C`. The stated breakage condition was sufficient
> and not necessary, which is the general shape of the error: a correctly
> identified contingency, with an under-imagined list of ways to discharge it.

**The ledger *used to* realise the split — contingently, not structurally.**
Row `NscStd` reads `67.25%` and every bit of it is carried by the three
non-μ-invariant imported axioms. Row `Nsc` *read* `0.00%` — but **not** for a
visibility reason: `Nsc` is the μ-*visible* quantity
(`Nsc_eq_ordinate_functional`), and its row was empty for a **supply** reason,
no effective `C`. So the correspondence has a stated breakage condition: **the
day OPEN 0 lands, a μ-invariant axiom feeds both rows and the accounting
coincidence ends** — happily, and without touching the theorem. Anyone reading
the coincidence as structural will mistake that day for a refutation.

**Consequence, scoped:** β-*equalities* are not μ-computable (that is the
theorem), and the current **nonzero certified proportion** on `NscStd` is
entirely bought from the literature. β-*inequalities* we manufacture routinely
— `on_line_of_H_eq_one` derives `β = 1/2` from ordinate data,
`odd_Hr_inhabited` extracts a critical zero from parity, `prop1` bounds an
on-line count by ordinate functionals. This program **is** a β-manufacturing
device, in inequality form, powered by `refl_inv`; what it cannot manufacture
is an identity.

*Flagged, not done (freeze):* `audit/Declarations.lean` should gain the eight
headline names from `Blindness.lean` so the existence audit covers them.


## W34 — the independence ladder

Filed from claude.ai (E23's derived idiocies: W34a–W34e). Queue discipline
unchanged — nothing here outranks the quarry or W19; W34a/W34d are filler
grade. **W34a is done and it was not decorative.**

### W34a — DONE, and it repaired a real gap in the ladder

The task was "restate rung 1 in the logicians' dialect, kill if the translation
is decorative." The translation was **not** decorative: it exposed a
discontinuity the ladder metaphor was hiding.

**Rungs 0–1 are *semantic* blindness results** — quantified over hypotheses
expressible in a language. **Rungs 2–ω are *proof-theoretic* independence** —
quantified over *proofs*. These are different notions. A statement "no
hypothesis of class `𝒞` decides `P`" only upgrades to independence if `𝒞` is
closed under deduction: otherwise a *consequence* of several `𝒞`-hypotheses
could decide `P` when no single one does.

**For the `μ_T`-invariant class it is closed, and that is now proved**
(`Riemann/Blindness.lean`, axiom-free): `MuInvariant.and`, `.or`, `.not`,
`.imp` — a Boolean subalgebra — and `MuInvariant.forall`, closure under
*arbitrary* conjunction, so a whole **theory** of μ-invariant axioms is itself a
μ-invariant hypothesis. Hence
`no_muInvariant_theory_computes_NscStd`: **no theory axiomatised by
`μ_T`-invariant sentences computes `NscStd` from `μ_T`** — not merely no single
axiom. Rung 1 is a genuine independence result, and the two models are
`Gauge.triple` and `Gauge.haunted`.

### The crowded-locus refinement, checked and proved

claude.ai's correction to the equality/inequality boundary was right and is now
formal (`Riemann/Fiber.lean`, 10 declarations, sorry-free, axiom-free):

* `config k j a` — the general fiber state over one atom: `k` on-line zeros,
  `j` mirror pairs at depth `|a − 1/2|`. `Gauge.triple = config 3 0`,
  `haunted = config 1 1`, `doubleZero = config 2 0`, `depthPair = config 0 1`.
* `config_ordinates_eq` — **the whole fiber over a mass is one gauge orbit.**
  `μ_T` sees `m = k + 2j` and nothing else, at any depths.
* `Noff_eq_zero_of_simple` — **sighted on the simple locus.** Where every atom
  has mass one, `N_off` is computed from `μ_T` alone (it is `0`).
* `blind_at_every_crowded_mass` — **blind at every mass `≥ 2`**, uniformly in
  the depth. So mass one is the **sharp threshold**, and the blindness is
  supported exactly on the crowded atoms — not approximately, exactly.
* `Discriminates Φ a := Φ (config 2 0 a) ≠ Φ (config 0 1 a)` — the acceptance
  test, mechanical. `not_discriminates_of_factors`: nothing factoring through
  `μ_T` passes, at any depth. `not_factors_of_discriminates`: passing it *is*
  failing to factor through `μ_T`.

**One sharpening back.** The dispatch describes the gauge pairs as "two fiber
states of **equal** parity", as though equal parity were a choice. It is
forced: `config_parity` gives `k ≡ m (mod 2)`, so *every* state in the fiber
over a fixed mass has the same on-line parity. There is no unequal-parity pair
to exhibit — which is why parity is the μ-visible part and `j` is the whole
residue.

### W34b–W34e — open, as filed

* **W34b** — bounded-arithmetic probe: what is known about RH-adjacent
  statements in weak systems; conservation results; any independence result for
  any nontrivial zeta statement from any arithmetic fragment. claude.ai-side
  read, on request.
* **W34c** — rung-2 target selection: weakest system × weakest zeta statement
  where a two-model argument might close. Kill: if every candidate needs
  consistency-strength machinery beyond the seam, park it with its price tag.
* **W34d** — ladder audit of the census: re-read each `FAILURES.md` entry as
  "an independence result for *which* class", stated uniformly. Filler grade.
  Note the interaction with the tri-read: only *object*-statements will re-index
  cleanly; *fate*-statements will not name a class.
* **W34e** — `METHOD.md`, naming the method honestly. **Now in flight** as part
  of the repository packaging (private GitHub, public later), so the polite
  translation ("generate-and-verify at volume, with certified-failure
  accumulation as the primary asset") is being written for external readers.

### W28/W34, cycle 3 — the acceptance test has a passing instance, and it is AM–GM

`Riemann/Fiber.lean`, axiom-free, sorry-free. claude.ai proposed
`landau_discriminates` as a one-session theorem. It was, and it is proved.

`landau x D := Σ_{ρ ∈ Z} x^β`, a finite sum with no analytic content. All
`config` zeros sit at ordinate `0`, so the oscillating factor is a common unit
and a real-valued functional suffices for the test. Then

* `landau x (config 2 0 a) = 2·x^(1/2)`
* `landau x (config 0 1 a) = x^a + x^(1−a)`

and `x^a + x^(1−a) > 2·x^(1/2)` for every `x > 1`, `a ≠ 1/2` — **strict AM–GM,
nothing more**. `landau_discriminates : ∀ x > 1, ∀ a ≠ 1/2, Discriminates
(landau x) a`.

Composed with `not_factors_of_discriminates`, the kernel checks end to end that
`landau 2` **does not factor through `μ_T`**. So the atom program's assignment —
one non-`μ_T`-invariant statement of our own — is discharged, by an inequality
older than the Hypothesis, with a proof a first-year can check.

**Honesty clause, kept at full size.** This certifies that the *functional*
discriminates. It does **not** certify that we can *evaluate* it on `ζ`'s zeros
to the needed precision — that is W16's separability problem, untouched
(`FAILURES.md` #1: phases shared with the on-line chorus, no separation at one
`x`). What changed is that the acceptance test now has a **known-passing
calibration input**, and every later candidate is measured against it.

E16's `cosh` is AM–GM's excess. That was never a metaphor.

### W34a, doctrine form (proposed, not adopted — freeze)

**A rung is not a blindness result; a rung is a blindness result *plus* a
closure certificate for its class.** Rung 1 now has both. Proposed as an R-rule
after the freeze lifts; escalated to Joop rather than executed.

And it specs rung 2 before W34c selects a target: for arithmetic fragments the
**closure is free** (theories are deductively closed by definition) but the
**models are not**. `triple` and `haunted` are configurations, not models of
arithmetic. Rung 2's whole difficulty is internalising the gauge-pair
construction — two models *of the fragment* whose arithmetic disagrees on the
target while agreeing on everything the fragment sees. That is the honest price
tag for W34c: the two-model move rebuilt one level down, where "configuration"
becomes "nonstandard model" and reflection needs an arithmetic avatar.
Paris–Harrington is the existence proof that the genre is nonempty; W34b should
look for model-theoretic independence proofs for `Π₁` arithmetic statements
specifically.

### W34d — registered prediction, pre-run

Before the ladder audit runs: **has-rung / no-rung will roughly reproduce the
crystal/cascade split**, because a *fate*-statement ("the bound was vacuous")
does not name a class to be independent of, while an *object*-statement does.
Registered here, timestamped, so the run can score against it. Schema gains a
rung column with value `none (fate)` where applicable.

### W34d — DONE. The ladder has one occupied rung above the ground, and the ground is borrowed

Audit in `FAILURES.md`. Criterion made **mechanical**: an entry has a rung iff a
machine-checked statement exists that no member of a named class decides the
target. Two genres separated — **two-model** (forcing shape) and **capacity**
(LP/extremal shape).

**Certified rungs: 4 of 11.** `#4`, `#7`, `#8` at **rung 1** (class:
`μ_T`-invariant hypotheses; certificates in `Blindness.lean`/`Fiber.lean`, all
built this week). `#6` at **rung 0** (class: bandwidth-one certificates;
certificate `Zeta23.PairCeiling.ceiling_law256`, verified axiom-free tonight in
the dependency).

**Registered prediction confirmed in direction:** all four certified rungs are
`crystal`; **no `cascade` entry has one**. No p-value — sample of 10 and the
class-naming half was done with the prediction in hand. The certificate half is
clean and carries the direction. `#9` defects again, as it did in the tri-read.

**Debt, filed:** `#10`'s rung 0 — the one the ladder brief listed as *owned* —
is **prose**. No Lean statement says `{F on [0,1], F ≥ 0}` + positivity fails to
decide the target. The argument may be right; it is not a rung by this audit's
criterion. **The only capacity certificate we can run came in with zeta-23.**
Recorded as `SURPRISES` S19.

> ⚠️ **Stale since `Capacity.lean` (`SESSION 128` found it in two registers at
> once).** `Riemann/Capacity.lean` carries eleven capacity theorems of our own,
> axiom-free and audited — `pinned_value_is_floor`, `value_eq_pinned`,
> `no_gain_past_known`, `unbounded_below_of_neg_outside`, their integral forms,
> and `reweighting_worst_case`. The "next rung-0 item, and it is cheap" named
> below **was done**: that is exactly what `no_gain_past_known` states. So
> `ceiling_law256` is no longer the only runnable capacity certificate, nor the
> only one we can *own*.


**Next rung-0 item, and it is cheap:** formalise the LP-duality collapse enough
to state "no `F` supported in `[0,1]` with `F ≥ 0` yields more than Montgomery's
`2/3`". That is a capacity statement about a convex program, not a theorem about
`ζ`, so it is Lean-reachable without any arithmetic input — the same shape as
`Basic.lean`'s combinatorial core.

### X characterised from the other side (night cycle 13)

`Blindness.lean` gives **necessity**: `μ_T` alone does not determine `NscStd`,
and no theory axiomatised by `μ_T`-invariant sentences does either. What was
never proved is **sufficiency** — that the fiber coordinate is the *whole*
residue.

`Riemann/Fiber.lean` now supplies the pointwise half, axiom-free:

* `onAt D γ` / `offAt D γ` — the on-line (`k`) and off-line (`2j`) parts of the
  mass at `γ`;
* `H_eq_onAt_add_offAt : H γ = onAt γ + offAt γ` — the fiber decomposition;
* `count_eq_onAt` — on the critical line a zero's *multiplicity* **is** the
  on-line count at its ordinate, because all on-line zeros sharing an ordinate
  are literally the same point;
* **`NscStd_eq_onAt_functional`** — `NscStd` is computed from `onAt` alone;
* `Nsc_reads_total` — `Nsc` is computed from `H` alone.

**So the two ledger rows differ by exactly which part of the fiber
decomposition they consult.** `Nsc` reads the total mass, which `μ_T` supplies;
`NscStd` reads the on-line part, which it does not. That is the two-row gap
(ISSUES #13) explained rather than merely priced.

**Kill condition** — that `NscStd` might need some further feature of the
configuration — **did not fire**: `onAt` suffices.

**UPDATE (night cycle 14): the packaged form is proved.**
`NscStd_determined : D.ordinates = D'.ordinates → (∀ γ, offAt D γ = offAt D' γ)
→ D.NscStd = D'.NscStd`, axiom-free, **with exactly those two hypotheses** — no
nodup, no finiteness, nothing beyond `(μ_T, offAt)`. The route was the on-line
ordinate multiset `onOrd`, whose multiplicity at `γ` is `onAt γ`
(`count_onOrd`); `NscStd` is a functional of it
(`NscStd_eq_onOrd_functional`), and a multiset is determined by its counts.

**So sufficiency is global, not pointwise, and X is bracketed:**

> **Withhold the fiber coordinate and no `μ_T`-invariant theory recovers the
> target (`Blindness.no_muInvariant_theory_computes_NscStd`); supply it and the
> target is determined (`Fiber.NscStd_determined`).**

The kill condition — that the counting step might need a hypothesis beyond
`(μ_T, offAt)`, which would mean the residue is larger than `j` — **did not
fire**.

**UPDATE (night cycle 15): extended to the whole ledger.**
`ledger_determined` proves that `(μ_T, offAt)` determines **`N`, `N⊛`, `Nsc`,
`NscStd` and `N_off`** — every quantity the project counts. `N`, `N⊛`, `Nsc`
need only `μ_T`; `NscStd` and `N_off` need the fiber coordinate too, and nothing
beyond it (`Noff_determined` goes through `card_onOrd_add_Noff`, the on-line /
off-line partition).

⚠️ **Correction (night cycle 16), stated here because this is where the claim
lives.** I wrote that this is *the exact statement* of what the certificate
class is missing. **It is an upper bound, not a tight one.**
`offAt_not_minimal` exhibits two configurations with the **same ledger** and
**different `offAt`** — the swap pair, one atom of mass two in each state at two
distinct heights, exchanged. So `(μ_T, offAt)` suffices, but some coarsening of
`offAt` would also suffice, and the minimal residue is **not yet identified**.

The same pair also settles the evaluation question negatively
(`landau_cannot_determine_offAt`): the real Landau weight agrees on it at
*every* `x`, so no amount of sampling `Σ_ρ x^β` recovers `offAt`. What
distinguishes the pair is *which ordinate carries the crowd* — precisely what
the phase `e^{iγ log x}` carries and the real weight discards. That is census
`#1`'s separability problem as a determination failure, and it is consistent
with `forensics/w16_price.py`: the binding constraint is the phase.

### The residue, narrowed once (night cycle 17)

**Kill condition:** *if relabelling ordinates can change any ledger quantity,
the residue genuinely depends on ordinate identity and the profile idea dies.*
**It did not fire.**

`ledger_relabel_invariant` (axiom-free): for **any injective** `σ : ℝ → ℝ`,
relabelling the ordinates leaves `N`, `N⊛`, `Nsc`, `NscStd` and `N_off`
unchanged. The swap pair of `offAt_not_minimal` is one instance — the
relabelling that exchanges two heights.

**So ordinate names are provably not part of the residue.** Whatever the minimal
information is, it is invariant under relabelling.

**Stated precisely, and deliberately not further —** because overclaiming this
exact result is what `SURPRISES` S26 records from last cycle. What is proved is
*invariance*. What is **not** proved is that the **profile** (the multiset of
`(mass, off-line mass)` pairs) **determines** the ledger; that needs the profile
construction and a separate argument. Two configurations can share a profile
without being related by a relabelling, so invariance does not give it.

**UPDATE (2026-08-15): the profile determines the ledger.** All five quantities
are functionals of `profile D` — the multiset of `(H γ, offAt γ)` pairs, one per
distinct ordinate, **heights discarded**: `N_from_profile`,
`Nstar_from_profile`, `Nsc_from_profile`, `NscStd_from_profile`,
`Noff_from_profile`, all axiom-free. The regrouping is
`Finset.sum_multiset_map_count`, needing only `DecidableEq`; no hypothesis
beyond `ZeroData`'s own finiteness was required, so the stated kill condition did
not fire.

So the residue is **at most the profile**, which is strictly coarser than
`(μ_T, offAt)` — `ledger_relabel_invariant` and the swap pair show the heights
carry nothing.

**Whether the profile is minimal is not proved and is not claimed.** A coarser
sufficient statistic may exist; nothing here rules one out.

> ⚠️ **Settled both ways, and the answers live further down this file
> (`SESSION 127` moved the pointer here).** A coarser sufficient statistic
> **does** exist — the ledger itself — so `Fiber.profile_not_minimal` refutes
> minimality outright (`075`); and `Fiber.profile_minimal_among_local` proves
> minimality among ordinate-local statistics (`077`). The paragraph above was
> correct when written and has been superseded for fifty cycles, with its
> replacement filed in a later section rather than here. That is `SURPRISES` S36
> repeating at register scale.

## W35 — the third moment IS the level-3 diagonal (entropy, new angle)

**Not previously connected in the registers**, and the witness for that claim is
a grep over every `.md` in the repo: `Σ m³` appears in four places as what
`prop1` needs, `n`-level correlation appears once (W20), and no entry joins
them.

**The identification.** `N⊛ = Σ_γ H(γ)²` — proved in-repo
(`N_Nstar_ordinate_functional`, `Nstar_from_profile`) — is the count of
**coincident pairs**, i.e. the coincidence-diagonal of the 2-level correlation.
Then `Σ_γ H(γ)³` is the count of **coincident triples**: the same diagonal one
level up. The level-2 half is witnessed; the level-3 statement is a definition
here, not yet a theorem.

> **SCOPED, `SESSION 200`.** "Requires leaving the two-moment world" holds for
> a bound asserted over **every** configuration, which is what `LinearBound`
> says. `prop1_LP_optimal` uses that hypothesis at two configurations, `single`
> and `Gauge.pairOnly`, and `Optimal.prop1_LP_optimal_needs_the_witnesses` shows
> the conclusion is false over a class omitting them.
>
> The second witness is a mass-two atom — a multiple zero. Whether `ζ` has one
> is not known, so a two-moment bound asserted only where `ζ`'s own
> configuration lives is not covered by `prop1_LP_optimal`. This does **not**
> say such a bound exists or would be better; it says the optimality theorem
> does not rule one out, and the register should not read as though it did.

**Why it is on the critical path.** `Optimal.prop1_LP_optimal` says improving
Proposition 1 requires leaving the two-moment world, and `ISSUES` #20 names the
missing object as `Σ m³`. If that object is the level-3 diagonal, then the
question *"what does the third moment cost?"* becomes *"what does the known
support range give at level 3?"* — which is exactly the question the project
already answered at level 2, and which W20 was filed to probe and never run.

**The probe, with its kill condition first:** *if Rudnick–Sarnak-type `n`-level
results are known only for test-function support strictly inside the range
where the level-2 result already gives us nothing new, then level 3 inherits
level 2's corridor problem and buys nothing — and that inheritance is the
finding.* Needs literature not in the registers; every value must be
`[RECALL, UNVERIFIED]` until fetched.

## W36 — function fields as a numerical laboratory (entropy, new mode)

`W28`'s model check uses function fields as a *pass/fail* test for the atom
interface. Nothing in the registers uses them as a **source of data**.

Over `F_q`, the zeros of a curve's zeta function are Frobenius eigenvalues:
finite in number, computable exactly, and RH is Weil's theorem. So the `offAt`
coordinate is **identically zero** there — but `H` is not, because repeated
eigenvalues genuinely occur.

That is a world where the off-line side is empty and the mass side is alive:
the exact calibration our apparatus has never had. Concretely, it would let us
compute real `profile`s, check which certified inequalities (`prop1`,
`six_mul_NscStd_le`, `two_NscStd_le`) are ever tight on genuine arithmetic data,
and see how far `Nsc` and `NscStd` diverge when crowding is real rather than
constructed.

**Kill condition, first:** *if repeated Frobenius eigenvalues are too rare in
small genus to separate the inequalities, the laboratory is underpowered at
feasible `q` and that is the finding* — a `#27`-shaped answer, and worth knowing
before anyone builds the harness.

### W35, first result: the third moment is on the *visible* side

**Kill condition:** *if `Σ m³` is not `μ_T`-visible it sits on the blindness
side and the registers' framing stands as written.* **It did not fire.**

`thirdMoment_determined` and `moment_determined` (axiom-free): `H γ` is
`ordinates.count γ`, so **every** moment of the mass distribution is a
functional of `μ_T` alone.

**This is an addition to the registers, not a correction of them** — nothing on
file said otherwise; the distinction simply had not been drawn. Two open
directions were being carried close together and are now separated:

* **more moments of `μ_T`** (`Σ m³` and beyond, = W35's level-3 diagonal):
  inside the certificate class's *reach*. What is missing is a theorem supplying
  the value, not an ability to see it. `Blindness` does not obstruct this.
* **the fiber coordinate** (`offAt`): not a functional of `μ_T` at any order, so
  no amount of higher-moment information reaches it
  (`NscStd_not_ordinate_functional`).

**Consequence for the route table:** improving `prop1` does **not** require
breaking the blindness. Only one of the project's two open directions is an
impossibility result; the other is an ordinary missing theorem. Those had been
priced as though they were the same kind of thing.

### Minimality: the question was ill-posed, and the reframing is the result

**Kill condition:** *if the minimality question is trivially answered — the
ledger being a sufficient statistic for itself — it is ill-posed as asked and
the finding is the reframing.* **It fired.**

The ledger is five numbers. Any summary equal to it is trivially sufficient for
it, so the minimal sufficient statistic *is* the ledger and asking for it
teaches nothing. The question with content is what **shape** the ledger has as a
functional of the atom distribution.

Reading the five `_from_profile` theorems together: every ledger quantity is a
sum over atoms of one of five basis functions of `(m, j)` — mass `m`, off-line
mass `2j`:

| ledger | basis function | `μ_T`-visible? |
|---|---|---|
| `N` | `m` | yes |
| `N⊛` | `m²` | yes |
| `Nsc` | `[m = 1]` | yes |
| `NscStd` | `[m − 2j = 1]` | **no** |
| `N_off` | `2j` | **no** |

**The target is a five-dimensional linear image of the atom distribution, and
the visibility split is `3 : 2`.** Three basis functionals read `m` alone;
two require `j` and are provably outside `μ_T`.

`Fiber.ledger_visibility_split` assembles this, axiom-free. Every entry was
already proved — across `Basic.lean`, `Blindness.lean` and `Fiber.lean` — and
the assembly is the point: **this is the clearest single statement the
development has, and until now it was scattered over three files.**

## W20 — ANSWERED by claude.ai's read; W35 re-scoped

All literature values below are **[RECALL, UNVERIFIED]** — supplied by
claude.ai, not read here — and one carries a stronger flag.

**Rudnick–Sarnak 1996** (Duke 81; announced C.R. Acad. Sci. 319, 1994): the
`n`-level correlations of `ζ`'s zeros agree with `U(N)`'s for test functions
with **combined** Fourier support `Σⱼ|ξⱼ| < 2` — one budget shared across all
`n` variables. General automorphic `L`-functions need GRH-adjacent hypotheses.

> ⚠️ **[VERIFY BEFORE USE]** A RIMS survey of RS reportedly says of `ζ`:
> *"Although their main theorem does not assume the Riemann Hypothesis, here we
> assume it for simplicity."* If accurate, RS's `n`-level theorem for `ζ` is
> **unconditional** in the restricted-support regime — and W20's question
> *"does BGST de-conditioning generalise to `n ≥ 3`?"* is answered by **it never
> needed to**. This must be checked against the Duke paper's actual theorem
> statement before anything consumes it. Highest-priority small item.

**The kill condition on W35's probe did not fire, and the reason is precise.**
It asked whether level-3 information is known only where level 2 already gives
nothing. The answer is the good case: `Σ|ξ| < 2` at `n = 3` buys **no new
reach** — the corridor past `α = 1` is untouched — but it is **new information
relative to the two-moment LP**, and that is our own theorem, not a hope:
`Optimal.prop1_LP_optimal` says the two-moment world is exhausted, and the
level-3 coincidence-diagonal is a functional that world cannot express.

**So the offer was never new support. It is new *order* within the old
support.**

### The composition, named end to end

| role | named object | status |
|---|---|---|
| supplier | RS 1996, level-3 at `Σ|ξ| < 2` | `[RECALL]`, one `[VERIFY]` flag |
| dictionary | Conrey–Snaith, *In support of n-correlation* (arXiv:1212.5537) | `[RECALL]` |
| consumer | a three-moment LP over `Σm`, `Σm²`, `Σm³` | **not yet built — see below** |
| visibility | `Fiber.thirdMoment_determined` — the consumer can see the goods | **kernel-certified** |

### The step that needs no literature at all, and should come first

Before anyone fetches RS, **the three-moment LP can be solved in-repo exactly as
the two-moment one was.** `Optimal.lean` already carries `LinearBound a b` and
> **`SESSION 208`: `LinearBound3` now exists, and the extension is harder than
> this line suggests.** `Optimal.LinearBound3` is defined, `linearBound3_mass`
> gives the single-atom test at every mass, and
> `linearBound3_not_reducible_to_mass_two` shows `206`'s collapse to three
> inequalities has **no analogue** here: with `c ≤ 0` the mass-`m` constraint is
> `m·(a + b·m + c·m²)` and that quadratic is concave, so its maximum over
> `m ≥ 2` can sit strictly inside the range. `(−11, 7, −1)` passes the mass-`1`
> and mass-`2` tests and fails at mass `3`. How far the binding mass sits
> depends on `b/c`, so a three-moment characterisation needs more than a fixed
> finite set of tests.

`prop1_LP_optimal`; extending to `LinearBound3 a b c` over `(N, N⊛, Σm³)` and
finding its optimum is the same argument with one more coordinate and more test
configurations.

That prices the entire programme above **before** any paper is read: if the
three-moment optimum is still `2 − C`, the supplier is irrelevant and W35 dies
cheaply; if it beats `2 − C`, the value of RS's theorem is known in advance and
exactly. **This is the sensitivity curve `PRICES.md` asks for, and it is pure
in-repo work.** Queued as the next W35 item.

## W36 — endorsed, with its literature attached

Also `[RECALL, UNVERIFIED]`: Katz–Sarnak for the ensembles; **Faifman–Rudnick**,
*Statistics of the zeros of zeta functions in families of hyperelliptic curves
over a finite field* (Compositio 146, 2010); **Rudnick**, *Traces of high powers
of the Frobenius class in the hyperelliptic ensemble* (Acta Arith. 143, 2010).

W36's harness question — are repeated eigenvalues frequent enough at feasible
`q` to separate the inequalities — **plausibly has its answer already tabulated
there.** Read before building; that ordering is the whole lesson of `S27`.

### W35, priced — and the price could not be computed, which is the result

**Kill condition:** *if the three-moment optimum is still `2 − C`, the third
moment buys nothing and W35 dies cheaply.* **It neither fired nor was
answered.**

claude.ai registered a hand derivation before the run
(`[HAND DERIVATION, UNVERIFIED, the LP decides]`). **Its algebra is exactly
right**, verified in rationals: the family `(a,b,c) = (2−2s, 3s−1, −s)`
satisfies `a + mb + m²c = (2−m) − s(m−1)(m−2)`, feasible against every
single-atom test for all `s ≥ 0`, with value `(2−C) + s(3C − 2 − C₃)`.

**And following it through certifies `7/4` of the zeros simple** at `C = 3/2`,
`C₃ = C²`, `s = 5` — from a feasible point. A proportion above 1 is impossible,
so a hypothesis is wrong, and it is not the algebra.

**The wrong hypothesis is the realizable input region.** `(−2, 3, −1)` is a
recession direction of the single-atom constraint set, so the program is
unbounded whenever `3C − 2 > C₃`. `C₃ ≥ C²` (Cauchy–Schwarz) is *necessary* and
nowhere near sufficient over **integer** atom masses: equality forces every atom
to share one mass `C`, so `C = 3/2` is not realizable by any configuration at
all. The LP was pricing input pairs no configuration can present.

> **`SESSION 212`: the named next step is not needed, and `W35` is dead.**
> `Optimal.linearBoundK_no_gain_at_any_moment`: for `k ≥ 3`, a feasible `c` is
> non-positive (`linearBoundK_c_nonpos`), and `Blindness.moment_obstruction`
> puts every configuration's `C_k` at or above `A·C − (A−1)` with
> `A + 1 = 2^{k−1}`. Moving `C_k` up from that floor with `c ≤ 0` can only
> shrink the delivered bound, and the floor already gives `2 − C`.
>
> So the bound delivered at **any** admissible `C_k` is at most `2 − C`,
> whatever the realizable region turns out to be. The diagnosis below stands —
> the LP was pricing pairs no configuration presents — but mapping the region
> would not rescue the route, so it is not work worth doing.

**So W35 is neither alive nor dead, and the next step is named:** the realizable
region of `(C, C₃)` for integer masses. That is a **W7-shaped realizability
problem** — this project's own genre, and the one whose autopsy reads *"the
cheap invariants are satisfied by construction; only the Euler product bites."*

**What this does not touch:** `prop1_LP_optimal` is unaffected — it quantifies
over the two-moment class and is proved from two configurations that are both
realizable. The defect is in the *three*-moment program's inputs, not in
anything certified.

`forensics/three_moment_lp.py` carries the verification and the verdict.
Filed as `SURPRISES` S29.

### W35 — DEAD, with a certificate. The third moment cannot help.

**Kill condition:** *if the three-moment optimum is still `2 − C`, the third
moment buys nothing and W35 dies cheaply.* **It fired**, and the obstruction is
exact rather than circumstantial.

claude.ai's LP gives certified value `(2 − C) + s·(3C − 2 − C₃)`, so the third
moment helps **iff** `C₃ < 3C − 2`. That is never satisfiable, by an identity:

> `3N⊛ − 2N − Σm³ = − Σ_atoms m(m−1)(m−2)`, and `m(m−1)(m−2) ≥ 0` for every
> natural `m`.

Hence **`Σm³ ≥ 3N⊛ − 2N` for every configuration**
(`Fiber.three_Nstar_le_thirdMoment_add_two_N`, axiom-free), the improvement term
is `≤ 0` always, and the optimum sits at `s = 0` — `prop1` unchanged.

**This kills the route, not the probe's timing.** No supplier can change an
inequality true of all configurations: RS, Fujii, Tsang are all irrelevant to
it. **The pricing was worth doing precisely because it cost nothing and the
literature fetch it pre-empted would have cost a session.**

**What the obstruction is made of.** `m(m−1)(m−2)` vanishes at `m ≤ 2` and
equals `6` at `m = 3`. The third moment carries information about atoms of mass
`≥ 3` and nothing else, and it carries it in the direction that costs.

> WARNING **Correction (2026-08-15), at the location of the error.** I wrote
> that this and the `/6` census result are "two readings of one polynomial", and
> that the coincidence "is not a coincidence". **Both sentences were wrong.**
> `six_mul_card_le_Nstar_sub_N` runs on `N* - N = sum m(m-1)`; the third-moment
> obstruction runs on `sum m(m-1)(m-2)`. **These are different polynomials.**
> They agree at `m = 3` (`3*2 = 6` and `3*2*1 = 6`) and nowhere else: at `m = 2`
> they read `2` and `0`, at `m = 4` they read `12` and `24`.
>
> **The shared `6` is exactly the coincidence I declared it not to be.** What is
> true and survives: both bounds become active at `m = 3`, because that is where
> crowding starts. The *threshold* is shared; the polynomial is not.

**Live remainder:** the level-3 *correlation* may still matter elsewhere — this
kills its use as a third moment in a linear bound on `Nsc`, which is the only
consumer W35 named. Any other consumer needs its own pricing.


### W28 gains a third audit column: constitutive vs merely used (E24)

The interface's audit has asked two questions of each candidate axiom: does `ζ`
satisfy it, and does it help. E24 adds a third:

> **Is this axiom part of what `ζ` *is*?** Checkable against the Hamburger /
> Kaczorowski–Perelli shelf: *does dropping it admit known non-`ζ` satisfiers?*

D–H answers that question for the current `ZeroData` axioms — functional
equation plus counting admits D–H, so those axioms are **not** constitutive, and
`Blindness.lean` already says so in its opening indictment.

**And W32's result sharpens what this column can be worth.** The atom bundles
classify `3/11` of the census; the other eight are information, capacity and
logic limits. A constitutive axiom set would have to speak to the eight, and
nothing in M or S does. **The rigidity criterion is therefore not a refinement
of the bundles — it is a different demand on them**, and W28's whiteboard hour
should treat it as such rather than as an extra checkbox.

Cast members `[RECALL, UNVERIFIED]`: Hamburger 1921; Kaczorowski–Perelli on
Selberg-class low degree. A converse-theorem survey (Hecke, Weil converse
theorems, higher degree) is offered by claude.ai on request — the field's
existing rigidity inventory, never priced in our currency.

## W38 — the equivalence atlas (filed as briefed)

Origin: Joop, via the P=NP analogy — *are there very different-looking problems
likely equivalent?* — sharpened by the observation that the answer may be worth
more than RH.

**The object:** every **proven** RH-biconditional, classified by which face of
E20's plane its statement lives on, with the **crossings** as the payload.
Certified iff-theorems only; no analogies, no "morally equivalent".

Seed members, all `[RECALL, UNVERIFIED]` until source-verified: Nyman–Beurling
and Báez-Duarte; Lagarias 2002 and Robin; `Λ = 0` for de Bruijn–Newman (given
Rodgers–Tao's `Λ ≥ 0`); Li's criterion; Weil positivity / Bombieri's form;
Speiser; Franel–Landau; the Redheffer matrix criterion; von Koch's
`ψ(x) = x + O(x^{1/2+ε})` and the Mertens form — **the last flagged in the brief
itself as sufficient-but-check-necessity, so every arrow's direction is graded,
not just its membership.** Broughan's two volumes are the raw material.

**Face definitions are frozen before any entry is filed**, per R19, and the
crossing definition is the one that matters:

> a proven biconditional whose two sides lie on different faces **without
> routing through "zeros on the line" as the junction** — the classifier must
> check the **proof's route**, not the statement pair, because every atlas entry
> trivially "crosses" through RH itself.

**Blinding is in the design rather than appended after the first embarrassment**
— one instance classifies faces from hypothesis-neutral phrasings, the other
routes the proofs independently, Joop holds both sealed hashes. **Given
`SURPRISES`' two correlated misses (S5 shared priming, S6 anchoring on
disclosure), this is the first W-item designed against the failure mode the
seam has actually exhibited**, and that is the right lesson to have drawn.

**Both outcomes pay.** A crossing exists: someone has already built a certified
bridge over the cleavage and filed it as a curiosity — cross-plane certification
in theorem form. No crossing exists: **RH is the unique articulation point of
its own equivalence graph**, which is a finding about the *literature*
independent of anyone's opinion about `ζ`, and it hands the fourth approach its
sharpest constraint — **the constitutive axioms must BE the junction**, with the
atlas as acceptance suite.

**T4 connects it to W32's result:** the atom bundles classify `3/11` of our
census; the atlas is a second, harder exam **written by the field itself**.

The atlas cannot die — a verified classified table of proven equivalents is a
permanent asset at any outcome — so per R12 **the risk lives entirely in the
classification claims**, which is exactly where the blinding sits.

### The shadow measured: `⌊m/2⌋ + 1` configurations per atom

**Kill condition:** *if two distinct fiber states shared the same `N_off`, the
orbit would be smaller than claimed and the ambiguity count wrong.* **It did not
fire** — `N_off = 2j` separates them, so the indexing by `j` is faithful.

The registers have called the missing datum *"one bounded natural number per
crowded atom"* since W28 without ever saying **how** bounded. It is exactly
`⌊m/2⌋`: the fiber states over mass `m` are `(m − 2j, j)` for
`0 ≤ j ≤ ⌊m/2⌋`, all sharing one `μ_T`, all separated by `N_off`.

| mass `m` | states | alternatives the class cannot rule out |
|---|---|---|
| 1 | 1 | **0** |
| 2, 3 | 2 | 1 |
| 4, 5 | 3 | 2 |
| 6, 7 | 4 | 3 |

**`m = 1` giving orbit size 1 is the R17 witness** — the mass-one case must be
unambiguous, and `Noff_eq_zero_of_simple` says so independently. Two routes to
the same fact, one of them the formula's own boundary case.

`Fiber.gauge_orbit_size`, axiom-free. This is the quantitative form of the
qualitative claim, and it says the shadow grows **linearly in the mass**: a
crowded atom of mass `m` hides `⌊m/2⌋` alternatives, no more and no fewer.


## Minimality of the profile — answered in the negative, and re-posed

`profile_not_minimal` (axiom-free) exhibits two realisable configurations with
**distinct profiles and identical ledgers**: mass `4` carrying `2` off-line
beside a wholly on-line mass `2`, versus a wholly on-line mass `4` beside a
mass `2` carrying `2` off-line. Profiles `{(4,2),(2,0)}` and `{(4,0),(2,2)}`;
`N = 6`, `N⊛ = 20`, `Nsc = 0`, `NscStd = 0`, `N_off = 2` on both.

So `profile → ledger` is not injective and the profile is not minimal. But the
useful content is that **the question as posed is degenerate**: the ledger is
trivially its own minimal sufficient statistic, so "is `X` minimal for the
ledger" is only meaningful once the competitors are restricted. Two restricted
forms worth asking, neither yet attempted:

1. **Minimal among `μ_T`-augmentations.** `(μ_T, offAt)` is sufficient
   (`ledger_determined`) and not minimal (`offAt_not_minimal`). Is there a
   *smallest* `f` with `(μ_T, f)` sufficient, and is the profile it?
2. **Minimal among ordinate-local statistics** — statistics of the form
   "a function of the per-ordinate data, aggregated". The profile is local in
   this sense; the ledger is not (it is the aggregate itself). Under locality
   the counterexample above is unavailable, because it exchanges data *between*
   ordinates.

   > ✅ **ANSWERED next cycle, in the affirmative.**
   > `Fiber.profile_minimal_among_local` (axiom-free): any per-atom coarsening
   > `g` whose value-multiset still determines `N` and `N_off` is **injective**
   > on realisable atoms. Two atoms sharing a `g`-value but differing in mass
   > are separated by `N`; sharing a mass but differing in off-line mass, by
   > `N_off`. Single-atom configurations are the whole witness set, so the
   > argument uses nothing about crowds. **The profile is minimal among
   > ordinate-local statistics**, and only two of the five ledger rows are
   > needed to force it — `N⊛`, `Nsc` and `NscStd` are not used.

Filed as the honest successor to the queued question, not as a claim that
either restricted form has an answer.


## Tightness of the `NscStd` bracket — done on one family, open in general

`Fiber.bracket_tight_two_atoms` (axiom-free) attains all of `[0, 2]` on two
atoms of mass `3` at one `μ_T`. The mechanism generalises transparently: an odd
atom of mass `m ≥ 3` is an **independent binary choice** — put its off-line pair
in (`k = 1`, contributes `1`) or leave it wholly on-line (`k = m`, contributes
`0`) — while mass-`1` atoms are forced to contribute and even atoms are forced
not to. So the attainable set should be exactly

> `{ Nsc + t : 0 ≤ t ≤ #{odd atoms of mass ≥ 3} } = [Nsc, #{odd atoms}]`

with **every** value hit, because the choices are independent.

> ✅ **BUILT next cycle.** `Fiber.chain` is the arbitrary-arity builder,
> `chain_profile` reads its profile, and `bracket_tight_chain` attains every
> `t ≤ n` on `n` atoms of mass `3` at a `t`-independent `μ_T`. The reusable core
> is `profile_superpose_disjoint`, and the kill condition asked exactly the right
> question: **disjointness of the ordinate supports is the only hypothesis
> needed.** The paragraph below records what was wanted; it is now supplied.

**What the general theorem needs, and why it was not attempted this cycle.** A
builder taking a multiset of ordinates plus a per-atom on/off choice to a
`ZeroData` — a fold of `superpose` over `configAt` at distinct heights — plus a
lemma that the profile of such a fold is the multiset of the chosen pairs. That
is the same shape as `twoAtom_profile` but at arbitrary arity, and it needs
injectivity of `(· : ℕ → ℝ)` to keep the heights distinct. Filed as the next
Lean-shaped item in this thread; nothing about it is conjectural, only unbuilt.


## After `S084`: what could still improve the `Nsc` row

`bridge_optimal` closes the shape `c·NscStd ≤ N + d·Nsc` at `(3, 2)`, so
`(3κ − 1)/2 = 0.50875` is the most that shape yields from the baseline. Three
directions remain, in increasing order of cost:

1. **A bridge using more `μ_T`-visible data.** The proof of `(3,2)` throws away
   the fact that a *non*-contributing even atom has mass `≥ 2`. A bound in
   `(NscStd, N, Nsc, oddAtoms)` — all four visible — is not excluded by
   `bridge_optimal`, whose scope is the triple. **This is the cheapest item on
   the board and it is pure combinatorics.**

   > ❌ **RUN THE SAME CYCLE, and it does not move the row.**
   > `Fiber.two_mul_atomCount_add_oddAtoms_le`: `2·A + #{odd atoms} ≤ N + 2·Nsc`,
   > where `A` is the atom count — strictly finer, tight at masses `1, 2, 3`.
   > But `A ≥ NscStd` and `#{odd atoms} ≥ NscStd`, and substituting recovers
   > `3·NscStd ≤ N + 2·Nsc` **exactly** (`three_mul_NscStd_le_of_four`). The
   > literature input supplies a proportion for `NscStd` and nothing for `A` or
   > `#{odd atoms}`, so the finer bound has nothing to spend. It becomes useful
   > only alongside a lower bound on the *atom count* — i.e. an upper bound on
   > average multiplicity, which is `N⊛` territory and therefore back to `(★)`.
2. **A better `κ`.** The row is `(3κ − 1)/2`, so every point of `ProportionStd`
   is worth `1.5` points of `Nsc`. Improving the literature input is now
   *leveraged*, which it was not when the row was believed closed.
3. **A star bound**, which now has to *beat* `0.50875` rather than open the row:
   Proposition 1 needs `C < 1.49125`, the `/6` bridge `C < 1.9825`. Both are far
   inside what any current route offers, so this direction became **less**
   attractive, not more.


## Where `(★)`'s constant lives — two walls, certified (SESSION 092)

`N⊛/N = Σ H² / Σ H` (`Blindness.Nstar_eq_sum_H_sq`): the **size-biased mean
multiplicity**. Two certified walls now locate it.

* **Below:** a proportion of *simple* zeros cannot reach it at any constant.
  `no_starBound_from_proportionStd` — `3m` simple atoms beside one atom of mass
  `m` hold the proportion at `3/4` while `N⊛/N = (3+m)/4` runs away.
* **Above:** a multiplicity *supremum* `M` reaches it, at constant `M`
  (`starBound_of_multiplicity_le`) — and `prop1` needs `C < 2`, so over the
  naturals that is `M ≤ 1`: every zero simple, the conclusion rather than a
  hypothesis.

**So `(★)` asks for control of a size-biased mean**, which is strictly weaker
than a supremum and strictly stronger than a proportion of simple zeros. Every
route in the program is an attempt to supply exactly that, and the two walls say
neither of the project's cheap neighbours will substitute.

> ⚠️ **Narrowed the next cycle.** The obvious candidate family is dead:
> `no_starBound_from_lowMult` kills *every* threshold `k`, not just `k = 1`. Any
> statistic that survives must therefore say something about how the
> **non-good** zeros are arranged, not merely how many there are — a proportion
> of any low-multiplicity class is blind to a single unboundedly crowded
> ordinate.

*Open, and now sharply posed:* is there a `μ_T`-visible statistic strictly
between "proportion of simple zeros" and "size-biased mean multiplicity" that the
literature does supply? The blindness results say `μ_T` sees `H` entirely, so
this is not an information question — it is a question about which functionals of
`H` the analytic methods reach.


## The multiplicity criterion, with its tolerance (SESSION 099)

`Fiber.Nstar_add_pred_mul_Nsc_le_except`:

> `N⊛ + (M−1)·Nsc ≤ M·N + E²`

for any decidable set of exceptional ordinates, where `E` counts the zeros
sitting at them and `H ≤ M` holds outside. So the sufficient condition for `(★)`
is not "no zero has multiplicity `> M`" but

> **"`H ≤ M` outside a set carrying `o(√N)` zeros".**

**The `E²` is attained, so the tolerance is not an artifact of the proof.** Put
all `E` exceptional zeros at one ordinate: `Nstar_from_profile` on a single atom
of mass `E` gives exactly `E²`. Hence an exceptional set of size `c√N` shifts `C`
by `c²`, which is not `o(1)`, and `√N` is the true boundary rather than a
convenient one.

*Scope: the `√N` statement is the asymptotic reading of the inequality, and the
attainment is arithmetic on `Nstar_from_profile` for a one-atom configuration —
not a separate theorem. The inequality itself is certified.*

**Why this matters for the route table.** Every route so far has needed control
of *all* zeros. This is the first criterion in the registers with a genuine
exceptional-set allowance, which is the form analytic number theory actually
delivers — zero-density results are always "outside an exceptional set". The
allowance is small (`√N`, not `εN`), and that smallness is the honest news.


---

# The multiplicity criterion — consolidated (SESSION 100)

Cycles `096`–`099` produced four results that supersede one another. **This is
the current statement; everything below it is history.**

## The one theorem

`Fiber.Nstar_add_pred_mul_Nsc_le_except` — axiom-free, and the others are its
specialisations (`Nstar_add_pred_mul_Nsc_le_of_except` proves that in Lean, not
in prose):

> Let `M ≥ 1`, let `exc` be any decidable set of ordinates, suppose `H γ ≤ M` for
> every `γ ∉ exc`, and let `E` be the number of zeros at exceptional ordinates.
> Then `N⊛ + (M−1)·Nsc ≤ M·N + E²`.

Dividing by `N`: **`C ≤ M − (M−1)·κ + E²/N`**, where `κ` is a certified lower
bound on `Nsc/N`.

Per-atom it is `H² + (M−1)·[H = 1] ≤ M·H`, tight at `H = 1` **and** at `H = M`;
the exceptional term is `E²` because the worst case puts all `E` zeros at one
ordinate, and that case is attained.

## The one extra ingredient

`Fiber.Nsc_eq_NscStd_of_mult_le_two` — **under `M ≤ 2`, `Nsc = NscStd`.** This is
what lets the *standard* baseline `0.6725` be used as `κ` instead of the
project's `0.50875`, and it is the whole reason `M ≤ 2` is so much stronger than
`M ≤ 3`.

## What it yields

| hypothesis | usable `κ` | star constant | `Nsc` row via `prop1` |
|---|---|---|---|
| `M ≤ 2`, no exceptions | `0.6725` (`Nsc = NscStd`) | **`1.3275`** — below Route III's `4/3` | **`0.6725`** |
| `M ≤ 3`, no exceptions | `0.50875` | `1.9825` | `0.0175` |
| `M ≤ 4` | `0.50875` | `≥ 2` — fails | — |
| `M ≤ M₀` outside `o(√N)` zeros | as above | as above, `+o(1)` | as above |

`C < 2` iff `κ > 1 − 1/(M−1)`. The `M = 3` line clears by `0.00875` and exists
only because of `084`; at the pre-`084` row of `0` the criterion is empty for
every `M ≥ 2`.

*Re-checked in exact rationals, `SESSION 259`.* Every entry of the table above
reproduces: the `M = 3` margin is `407/800 − 1/2 = 7/800 = 0.00875`, its star
constant `3 − 2κ = 793/400 = 1.9825` and `prop1` image `7/400 = 0.0175`; `M = 4`
gives `1979/800 = 2.47375`, which is `≥ 2` and so carries nothing; and at `κ = 0`
the criterion `0 > 1 − 1/(M−1)` needs `M < 2`, so it is empty for every `M ≥ 2`
as stated.

## Superseded, and why kept

* `096`'s `Nstar_add_mul_Nsc_le` — weaker by exactly `N − Nsc`. Annotated at its
  location.
* `096`'s `starBound_of_multiplicity_two` (`C ≤ 1.9825` from `M ≤ 2`) — the same
  hypothesis now gives `1.3275`. Annotated at its location.
* `092`'s "a multiplicity supremum is useless" — true of the **bare** supremum,
  false once the `Nsc` row is available. Annotated at its location.

**Nothing here asserts any multiplicity hypothesis.** All are carried as
hypotheses; the ledger is unchanged at `NscStd 67.25% / Nsc 50.88%`.

## The criterion is one-way (SESSION 101)

`Fiber.starBound_allows_any_multiplicity`: for every `m` there is a configuration
with `N⊛ < 2·N` — `(★)` below `prop1`'s threshold — containing an atom of mass
`m` (`m²` simple atoms beside one atom of mass `m`). **So `(★)` tolerates any
fixed multiplicity**, and no multiplicity bound can be extracted from a star
bound. The implications run one way only:

> `multiplicity ≤ M` (+ a certified row) `⟹ (★)`,  and **not** conversely.

Recorded so that nobody spends a cycle trying to close the loop.


---

# The master identity (SESSION 109)

Everything in the `084`–`108` arc reduces to one equation and one inequality:

> **`NscStd = Nsc + hauntedCount`**  (identity — `NscStd_eq_Nsc_add_haunted`)
> **`Nsc + 3·hauntedCount ≤ N`**     (mass accounting — `Nsc_add_three_mul_haunted_le_N`)

From these alone:

| result | how it follows |
|---|---|
| `084`'s `3·NscStd ≤ N + 2·Nsc` | eliminate `hauntedCount` between the two |
| `NoHaunted ⟹ Proportion κ` (`107`) | `hauntedCount = 0` in the identity |
| `Nsc = NscStd ↔ NoHaunted` (`108`) | the identity with `hauntedCount = 0` |
| the ladder (`105`) | replace `3` in the mass accounting by `m` |
| the `Nsc` row's exact value | `Nsc/N = NscStd/N − hauntedCount/N` |

**The last line is the useful one.** The row is not approximately the baseline
minus something — it is *exactly* `κ` minus the haunted density. So any bound
`hauntedCount ≤ δ·N` gives `Proportion (κ − δ)` immediately, and the whole
conditional apparatus is a search for such a `δ`.

`0.50875 = 0.6725 − 0.16375`, and `0.16375` is the haunted density the trivial
mass accounting permits.


## The haunted count, canonically bounded (SESSION 110)

`109` reduced the row to `Nsc/N = NscStd/N − hauntedCount/N`. The bound on the
subtracted term is

> **`2·hauntedCount + NscStd ≤ N`**  (`two_mul_haunted_add_NscStd_le_N`)

— each haunted ordinate carries `≥ 2` off-line zeros, each standard-simple one
carries an on-line zero, and the collections are disjoint. Hence
`hauntedCount ≤ (N − NscStd)/2` and the certified row is
`0.6725 − (1 − 0.6725)/2 = 0.50875`, read off in one line.

**Three routes, one inequality.** The registers reached the haunted count three
ways — `083`'s coupling through `N_off`, `109`'s mass accounting, `090`'s
off-line density row — and all three give exactly this. That is worth recording
so a future cycle does not look for a fourth: within the counts
`(N, NscStd, Nsc, N_off)` there is nothing else to say.

**And it is attained** on `104`'s extremal family, mixtures of simple and haunted
mass-`3` atoms (`two_mul_haunted_add_NscStd_eq_iff`) — the same equality set,
which is the consistency check.

**So improving the row requires leaving these counts.** Any `δ < 0.16375` bound
on the haunted density must come from a fact about ζ that is not a relation among
its own counting functions — which is exactly what `087`'s ξ′ route and `105`'s
pattern-exclusion are, and why both are hypotheses rather than theorems.


## `NoHaunted` in the known hierarchy (SESSION 115, from claude.ai)

The hypothesis of the project's strongest conditional row sits below a standard
conjecture:

> **LI** (linear independence of the positive ordinates over `ℚ`; Wintner,
> Ingham 1942, the standing hypothesis of Rubinstein–Sarnak's bias work)
> **⟹ all ordinates distinct ⟹ no haunting.**

So `NoHaunted` is the **weakest** member of that chain — milder than what the
prime-race literature routinely assumes.

> ⚠️ **Sharpened in `SESSION 116`, and the sharpening matters more than the
> ordering.** Certifying the chain shows the middle member is far stronger than
> "mild": **all ordinates distinct forces `N_off = 0`**
> (`Fiber.Noff_eq_zero_of_allDistinct`) — the functional equation puts every
> off-line zero at its partner's height, so distinctness *is* RH-in-window.
> `LI` presupposes RH anyway.
>
> `NoHaunted` does **not** imply `N_off = 0`: a lone off-line pair is unhaunted
> (`noHaunted_not_imp_Noff_zero`). So it is not merely the weakest member of the
> chain — **it is the only member that is not already the conclusion.** A
> conditional row keyed to LI or to distinctness would be conditioning on RH; a
> row keyed to `NoHaunted` is not. A conditional row keyed to it asks less
than the field's own standard extra hypothesis. **[RECALL, UNVERIFIED]** on the
attributions; the implications themselves are immediate (distinct ordinates make
every atom mass one, so `hauntedCount = 0`).

**Empirically absent too:** the verified zeros to height `3×10¹²` have pairwise
distinct ordinates, so haunting — like off-line zeros — is empirically absent at
computed heights. Two absences, one instrument each.

**Why the quantity has no name.** claude.ai searched and reports none, with a
reason worth keeping: haunting only exists in the *unconditional* world. Under
RH it is vacuous;

> ⚠️ **`SESSION 145` — this sentence predicted `144`'s result, and I did not read
> it.** "Under RH it is vacuous" is exactly why `W19` died: the only S-moment
> identity precise enough (Goldston 1987, error `o(T)`) is RH-conditional, and
> RH empties `hauntedCount`. `143` wrote the want-ad and `144` spent a fetch
> confirming what was already three registers deep on disk. This is the `S27`
> shape — *check the registers before reconstructing* — applied not to a
> computation but to a **verdict**. The repair is mechanical rather than
> resolutional: `forensics/provenance_lint.py` Rule 4 (VACUITY) now refuses any
> chain pairing an RH-conditional input with `hauntedCount`, so the next time it
> is the guard that says this and not a paragraph nobody re-reads.

*(original note continues)* the classical unconditional quantities (`N`, `N_d`, `N⊛`) are
`μ_T`-visible and, by `Blindness`, provably cannot isolate it. The nearest named
object is the distinct-zeros deficit `N(T) − N_d(T)`, of which `hauntedCount` is
the cross-term nobody has had reason to separate. The unconditional regime where
it is live was opened recently; an unnamed inhabitant is expected.


## The chain, complete (SESSION 117)

> `LI` ⟹ all ordinates distinct ⟹ `N_off = 0` (RH-in-window) ⟹ `NoHaunted`

Certified links: `noHaunted_of_allDistinct`, `Noff_eq_zero_of_allDistinct`,
`noHaunted_of_Noff_zero`. **[RECALL, UNVERIFIED]** on `LI ⟹ distinct` only —
that is the attribution, not the arithmetic.

**The last link is strict** (`noHaunted_strictly_weaker_than_RH`): a lone
off-line pair is unhaunted with `N_off = 2`. So

> **the project's conditional row is keyed to a hypothesis strictly weaker than
> RH restricted to the window.**

That is the strongest available positioning statement, and it is now certified
rather than argued. Every other hypothesis in the neighbourhood — `LI`,
distinctness, RH itself — contains the conclusion; `NoHaunted` does not.


## The conditional row, in one statement (SESSION 118)

Every conditional result in the `084`–`117` arc is an instance of

> **`ProportionStd κ` + `hauntedCount ≤ δ·N` ⟹ `Proportion (κ − δ)`**
> (`proportion_of_hauntedDensity`)

because `109`'s identity makes the row a subtraction. The instances:

| `δ` | hypothesis | row at `κ = 0.6725` |
|---|---|---|
| `0` | `NoHaunted` (`107`) | `0.6725` |
| `β/2` | an off-line import at `β` (`087`) | `κ − β/2` |
| `0.16375` | the unconditional off-line row (`090`) | **`0.50875`** — the ledger |
| `(1 − κ)/(m − 1)` | the mass ladder (`105`), odd rungs | `κ − (1−κ)/(m−1)` |
| `(C − 1)/6` | a star bound `C` — the `/6` bridge (`Gaps`) | `κ − (C−1)/6` |

> The ladder's `δ` was written vaguely when this table was first drawn; `119`
> certified it as `(1 − κ)/(m − 1)` via
> `Fiber.pred_mul_haunted_add_NscStd_le_N`, which generalises `110`'s canonical
> bound to `(m−1)·hauntedCount + NscStd ≤ N`. At `m = 3` it is `0.16375`, at
> `m = 5` it is `0.081875`, and `0.6725 − 0.081875 = 0.590625` — `105`'s number
> exactly.

So there is one conditional instrument, not five, and the search is for a `δ`.
`111` caps what the counting can supply at `δ = 0.16375`; anything smaller must
come from outside.


## The three certified bounds on `hauntedCount` (SESSION 123)

Every conditional row is `hauntedCount ≤ δ·N`. There are exactly three certified
inequalities bounding that quantity, and they consume three different inputs:

| bound | consumes | source |
|---|---|---|
| `2·hauntedCount ≤ N_off` | the off-line count | `083`'s coupling |
| `2·hauntedCount + NscStd ≤ N` | the baseline alone | `110` |
| `6·hauntedCount + N ≤ N⊛` | **`(★)`** | `Basic.six_mul_NscStd_le` via `109`'s identity |
| `6·hauntedCount ≤ factMoment 3` | the third factorial moment | `124` — **nil value**, nothing bounds it |

> ⚠️ **`SESSION 125`: stop counting.** `123` said three, `124` found a fourth,
> and two more are one line each (`3·haunted ≤ N`, `haunted ≤ NscStd` —
> `Fiber.best_delta_is_from_110`). Bounds on this quantity are cheap; the table
> below lists the ones that are *sharpest on an input we hold*, which is the only
> property worth tabulating. **`δ = 0.16375` is the best the certified inputs
> support**, and `111` caps any baseline-only argument there.

> ⚠️ **"Exactly three" was wrong (`SESSION 124`).** There are four, and the
> fourth is the third-factorial-moment bound above. Its ledger value is nil —
> nothing certified bounds `factMoment 3`, and `Optimal.moment_route_walled`
> shows no moment inequality of order `≥ 3` can be made to bind
> [**corrected `SESSION 146`: `moment_route_walled` does NOT wall this bound.**
> Its two witnesses have masses `≤ 2`, so their `factMoment 3` and
> `hauntedCount` are both zero; it walls prop1's LP, not this inequality. The
> real obstruction is the scale separation priced in `forensics/w19_price.py`
> and the RH-vacuity that killed W19 in `144`. `Fiber.lean` was corrected at
> `144`; this copy was not, and that is the `142` shape again — one sentence,
> two documents, fixed in one] — which is why
> the enumeration missed it: I was listing bounds that *pay*, and wrote the
> sentence as if I had listed bounds that *exist*.

The third is the only one that consumes a star bound, and it is why the `/6`
bridge exists. With a star bound `C` it gives `δ = (C−1)/6`, which beats the
unconditional `0.16375` exactly when `C < 1.9825` — the threshold `098` recorded
from the other direction, and since `304` a theorem,
`Gaps.starBound_delta_beats_baseline`, rather than prose.

**So `(★)`'s entire contribution to the `Nsc` row is a bound on the haunted
count.** Route I and Route III exist to buy a `C`; what a `C` buys is `δ`.


## The genre, and where `NoHaunted` sits in it (SESSION 132, from claude.ai)

> ✅ **Three of four verified from the arXiv abstracts, `SESSION 136`** — the
> allowlist opened and I read them. **Abstracts, not proofs**: this discharges
> "does the paper claim this", not "is the claim correct", and the distinction is
> the whole of what a citation buys.

| cited as | arXiv | abstract says |
|---|---|---|
| Goldston–Suriajaya, PCC without RH | **2507.06823** (Goldston, **Lee, Schettler**, Suriajaya) | *"PCC … can be used to prove **without the assumption of RH** that asymptotically 100% of the zeros are both simple and on the critical line"*, plus an AH form ✓ |
| Aryan, `2/3` under a density hypothesis | **1902.05473** | *"at least two-thirds of the zeros … are simple under a **zero density hypothesis, which is weaker than the Riemann hypothesis**"* ✓ |
| BGST, location-shaped | **2501.14545** (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh) | pair correlation applied to the **horizontal distribution** of zeros ✓ |

**Declined:** the *"`1/3` simple-and-critical, unconditional"* figure attributed
to BGST-I. It is not in the abstract I read and I will not carry a number I have
not seen. **Still [RECALL, UNVERIFIED]:** the *Acta Arith.* 214 narrow-box
statement and its `61.7%`.

**And Aryan's mechanism is ours.** The paper is titled *"On an extension of the
Landau–Gonek formula"* — the `2/3` comes from **Landau–Gonek**, which is the
object `Fiber.landau` models and `landau_discriminates` proves separates the
off-line configurations. A member of the genre reaches its result through the
tool this project independently built as its discriminator. Filed as a lead, not
a claim: I have read an abstract, not a proof.

**[RECALL, UNVERIFIED]** for anything not in the table above.

| member | hypothesis shape | conclusion |
|---|---|---|
| BGST 2024 (*Acta Arith.* 214) | **location** — all zeros in `T^{3/8} < γ ≤ T` within `1/(2 log T)` of the line | `≥ 61.7%` simple |
| Goldston–Suriajaya 2025/26; GLSS arXiv:2507.06823 | **statistics** — PCC assumed *without* RH (and the AH variant) | `100%` simple and critical, asymptotically |
| Aryan arXiv:1902.05473 | **density** | `2/3` simple |
| **`NoHaunted`** (this project) | **coincidence** — one exact-height pattern absent | `0.6725` |

`NoHaunted` is not comparable to the narrow box: the box permits haunting inside
it. It is exact where PCC is asymptotic. And it is strictly weaker than
RH-in-window (`117`), which no other member is.

**The normal form is the contribution.** Every conclusion in the table factors
through `ProportionStd κ + hauntedCount ≤ δ·N ⟹ Proportion (κ − δ)`
(`proportion_of_hauntedDensity`), and the five in-repo instances are its
specialisations. A young genre with a zoo, given a normal form.


---

# The foreign-entropy harness and the data column (SESSION 133, from claude.ai via Joop)

**Received and filed. Nothing here outranks the standing queue.**

## The harness — six tasks

OpenCode on the VPS with free model families. The principle: for the divergent
slot **lineage distance beats capability**. Every cognitive component of this
project shares one ancestry; `T2` proved our blind passes are blind to context
but not to lineage. Free models are **entropy wells**, their outputs feedstock
tagged `[FOREIGN, family, UNVERIFIED]`, never conclusions.

1. **R19 blind classification, lineage-grade** — census/residue/atlas faces to a
   foreign model with hypothesis-language stripped. Agreement is finally
   *replication*; disagreement is their noise or our lineage-artifact.
2. **Collision beats** — two register entries, neutrally stated: "do these know
   each other?"
3. **Vocabulary probes** — a bare statement, "what is this called and who works
   on it?" A literature channel orthogonal to claude.ai's searches.
4. **Adversarial claim reading** — "find the sentence that claims more than its
   citation supports." Semantics-grade where `claims_gate` is a wordlist, and
   foreign readers lack our habituation to our own prose.
5. **Idiocy generation from neutral seeds** — plain-words statement of an open
   item, harvest approaches.
6. **Per-family calibration ledger** — every output scored hit/known/noise/harmful.
   Doubles as the first measurement of how independent the free lineages really
   are. (They all ate arXiv too.)

**Kill condition for the harness, pre-stated:** if after the calibration window
no family beats noise on any task type, the wells are dry and the harness retires
to a one-line `METHOD.md` note — which would itself be a finding about how much
of the free tier is one lineage in different wrappers.

## The data column — and it is blocked

Diagnosis: the reading phase was **skeleton-building**, and skeletons are what
literature supplies. The skeleton is load-tested; the flesh phase is due. Items:

| item | status |
|---|---|
| `W15` Odlyzko/AH/GUE classifier, foreign models as feature-proposers | never run |
| `W21`/`W9` the verified `12.3` trillion as load-bearing input | never run |
| `W36` function-field laboratory — `offAt ≡ 0` a theorem, ground truth attached | briefed, unbuilt |
| `T2`-of-`W27` log log signature on real zeros | briefed, unbuilt |
| **the haunted census, empirically** — near-hauntings, minimal vertical gaps | **new, cheapest, and nobody has looked** |

> ✅ **DISCHARGED (`SESSION 146`, and it had been discharged since `134`).**
> Joop widened the allowlist; `data/zeros1` carries 100 000 Odlyzko ordinates
> and sessions `138`–`143` all ran on it. The escalation below is answered and
> is retained as the record of the ask.
>
> **Why it stayed visible as an open escalation for twelve sessions:** the
> absence queue never listed it. Two independent settle-rules each hid it — the
> `⚠️` in its own banner, and `SESSION 139` appearing in the *unrelated heading*
> that follows it. Neither fix alone surfaces it; they masked each other. Both
> repaired in `forensics/absence_queue.py` this cycle.

**⚠️ ESCALATION — the data column cannot start on this VPS as configured.**
`find` over the repo returns **no numeric data of any kind**, and the sandbox's
network allowlist is `github.com` only. Odlyzko's tables and LMFDB are
unreachable. The cheapest item on the board — *"how close do heights ever come to
sharing?"* — is one afternoon's arithmetic and zero of it can begin until the
files are on the machine. **Joop: either widen the allowlist or drop the tables
in the repo.**


## The slow-convergence recall, tested (SESSION 139)

`135` measured the small-gap constant at `0.71×` GUE and marked slow convergence
`[RECALL, UNVERIFIED]`. Tested across twenty orders of magnitude in height:

| height | `obs/GUE` | gaps below `δ = 0.3` |
|---|---|---|
| `t ~ 10⁴` (`zeros1`) | `0.712 ± 0.016` | 2109 |
| `t ~ 2.7×10¹¹` (`zeros3`) | `0.885 ± 0.055` | 262 |
| `t ~ 1.4×10²⁰` (`zeros4`) | `0.868 ± 0.054` | 257 |

**The rise is real between `10⁴` and `10¹¹` (`3.0σ`)** and **unresolved between
`10¹¹` and `10²⁰` (`0.2σ`)**. So convergence toward GUE is visible in the data and
has largely happened by `t ~ 10¹¹`. Claiming monotonicity across all three would
be reading noise as signal, and the script says so in its own output.

`mean δ = 0.999986 / 1.000109 / 0.999970` in the three regimes — the
normalisation validates itself at each height, which is what makes the constants
comparable.

**The recall is now supported by measurement**, not discharged: I have confirmed
the *behaviour* the literature is said to report, not read the literature.

## Does the whole moment sequence determine `N_sc`? (SESSION 335, open)

> **Answered under a cap at `345`; the uncapped question is what remains.**
> `Nsc_from_moments` gives `(−1)^b · b! · N_sc` as a `ℤ`-combination of
> `momentK 0 … momentK b` whenever every mass is at most `b + 1`, and
> `Nsc_determined_by_moments_of_cap` is the determinacy statement this entry asks
> for, with the cap added: two capped configurations agreeing on those moments have
> equal `N_sc`. **Without a cap nothing here applies** — the coefficients depend on
> `b`, and there is no uniform combination. So this entry's question is now exactly
> the uncapped one.
>
> **Partly answered at `336`, and the answer is a cap rather than a limit.**
> Under a multiplicity cap the question is finite and positive: `two_mul_Nsc_eq_iff`
> gives `2·N_sc + 5·N = N⊛ + 6·atomCount` **iff** every mass is at most `3`, and
> `nine_mul_Nstar_add_atomCount_eq_iff` does the same at `4` with the third moment.
> So *three* moments compute `N_sc` on capped configurations, and the general
> uncapped question below is what remains — the limit statement, not the finite one.

`335` proved two things that leave a gap between them. Every `momentK D k` is a
functional of `D.ordinates` (`momentK_ordinate_functional`), and `N_sc` is *also*
an ordinate functional (`Nsc_eq_ordinate_functional`) — so the reduction that
kills `hauntedCount`, `oddAbove`, `evenOnAt`, `offLineOnly` and `NscStd` says
nothing against `N_sc`. And `single_momentK_not_determine_Nsc` shows one moment is
not enough, at any `k`.

**Open: is the full sequence enough?** The mathematical content is whether the
multiset of masses is recovered from its power sums — the classical answer is yes
(Newton's identities), which would give `N_sc` as the count of masses equal to
one. **What is not priced is the Lean route**: the identities are over a ring
while these are `ℕ`-valued sums over a `Multiset`, and no attempt has been made.

**Kill condition for whoever takes it:** *if recovering the mass multiset needs
the sequence at unboundedly many `k` with no `k` sufficing for a given
configuration, the statement is a limit statement and does not belong in the
`ℕ`-linear vocabulary the rest of the file uses — say so and stop.*
