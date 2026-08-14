# LEADS — the cutting-room floor

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
the `v` slot of this container.** The 0.93pp gap up to zeta-23's proved
bandwidth-one ceiling (0.6818287) therefore does not live in window shape; it
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
| `baseline_przz` | **`NscStd`** (via `ProportionStd`) | **not** μ-invariant |
| `baseline_zeta23` | **`NscStd`** | **not** μ-invariant |
| `xiPrimeFamily`, `closePairsZeta` | objects, not predicates | n/a |

**The ledger currently realises the split — contingently, not structurally.**
Row `NscStd` reads `67.25%` and every bit of it is carried by the three
non-μ-invariant imported axioms. Row `Nsc` reads `0.00%` — but **not** for a
visibility reason: `Nsc` is the μ-*visible* quantity
(`Nsc_eq_ordinate_functional`), and its row is empty for a **supply** reason,
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
