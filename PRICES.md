# PRICES — what each escape channel costs, in the project's own currency

X says the certificate class factors through bandwidth-≤1 functionals of
`μ_T = Σ_ρ m(ρ)·δ_{γ_ρ}`. Escaping it means buying information in one of three
directions. This file is the price list; a complete one **is** the quantitative
form of [OPEN D].

| direction | channel | price | priced by |
|---|---|---|---|
| **(ii) horizontal, depth-shaped** | zero-free regions (Vinogradov–Korobov), classical density theorems `N(σ,T)` | **exactly 0 — unspendable** (W12; see below) | `X`: `μ_T` has no depth coordinate |
| **(ii) horizontal** | one row-crossing of the ledger (`NscStd → Nsc`) | **`(C−1)/6`** (was `(C−1)/2`; the haunted-ordinate census, W6) | `nsc_of_nscStd` + `six_mul_NscStd_le` — proved |
| (ii), free | *parity* of an atom's mass — "an odd atom houses a critical zero" | **0** | `odd_mass_inhabited`, `card_odd_atoms_le_critical` — proved |
| **(iii) vertical, finer** | extra support in `F(α,T)` past `\|α\| = 1` | **≈ 12pp per quarter-unit** (0.6725 → 0.795 → 0.854 → 0.888 at λ = 1, 1.25, 1.5, 2) | the λ-sweep, ISSUES #12 — numeric, uncertified |
| **(i) value data** | *(no price yet)* | raw material: BHB13's `0.703704` sits `≈ 2.2pp` over the bandlimited ceiling `0.6818287` | needs the BHB13 mechanism read |

## Reading the list

* The two priced entries are in **different** directions and were computed by
  **different** means (a theorem; a numerical optimisation), which is the point
  — the list is not one calculation repeated.
* Direction (iii) is an order of magnitude cheaper per unit than direction (ii)
  at current constants, but nothing is known to be *purchasable* there; (ii)
  has a purchase mechanism (the imported baseline) but a steep price that only
  pays once `C < 2.345`.

> ⚠️ **STALE THRESHOLD (SESSION 084).** The `Nsc` row is **open at 50.875%** (`certified_nsc_unconditional`), so "the row opens at `C < …`" no longer describes the situation. A star-bound route now matters only if it *beats* `0.50875`: Proposition 1 needs `C < 1.49125`, the `/6` bridge needs `C < 1.9825`. The thresholds below are retained as correct arithmetic about *opening* a row that is no longer closed.

* **Certificate engineering is not a channel and is nearly exhausted.** On
  identical GUE input the certificate choice alone moves `0.5 → ≤0.6818287`
  (18.18pp), of which **0.28pp remains** in the bandlimited class (W11, cycle
  3). Do not confuse it with buying information: no entry in the table above
  changed.
* Direction (i) is unpriced and has the only certified over-ceiling result in
  the field attached to it (BHB13, on RH alone). That asymmetry is the
  strongest argument for reading BHB13's mechanism next.

## Direction (ii) admissibility criterion — screen before estimating

From W12's zero-price theorem read together with W16:

> **Horizontal information enters only through functionals uniform (continuous)
> at `δ = 0`. Anything with a depth threshold buys exactly nothing.**

Density theorems and zero-free regions fail by construction — they are
threshold-shaped. Landau's weights pass, because `cosh(δ log x)` is analytic
through the line. So candidate horizontal inputs get screened for `δ → 0`
uniformity **before** any estimate is attempted; this is a selection principle,
not a price.

Its consequence is a consolidation: the only admissible genre in direction (ii)
is value-shaped / exponential-sum-shaped input, which puts directions (i) and
(ii) on **the same live front**. W7's death points the same way — cheap
invariants are satisfied by construction and only the Euler product bites, so
everything remaining routes through value data.

## The cross-tradition seam — two budgets, one currency?

Both readings of the functional equation have hit a wall in their own
vocabulary:

* **position-readers**: `F(α)` support, capped at `|α| ≤ 1`;
* **value-readers**: **mollifier length** `θ` (Levinson `θ < 1/2` →
  Conrey `4/7` → PRZZ), which is literally a lossy compression of `1/ζ` whose
  length *is* the budget.

A9c's compression framing predicts these are **one barrier in two costumes**,
which makes the hybrid an arbitrage rather than a wish. The open question:
**what does a unit of mollifier length cost in units of `F`-support, and is the
exchange rate a theorem?**

**Currency, refined — and the refinement reverses the arbitrage.** Raw length
hides the wall. Montgomery–Vaughan gives every such mean value **free up to
total length `T`** — the diagonal — so the budget that matters is **excess past
the diagonal**:

| tradition | object | certified total length | **excess past diagonal** |
|---|---|---|---|
| position | `F(α)`: a prime polynomial of length `T^α`, known for `α < 1` | `T^1` | **0 — never crossed** |
| value | `∫\|ζ\|²\|M\|²`: total length `T^{1+θ}`, Conrey `θ = 4/7` | `T^{11/7}` | **`T^{4/7}`**, held since ~1989 |

So the value side is **not** behind — it is the only tradition that has ever
been past the wall, and the arbitrage runs the other way: **import the value
side's past-diagonal technology into position-side objects.**

**The one barrier, arithmetically.** Crossing the diagonal means evaluating
*shifted convolutions of the polynomial's coefficients*, and the traditions
differ only in which coefficients they carry: value-side `d(n)` (shifted
convolutions = the additive divisor problem, **theorems**, with Motohashi's
spectral expansion the exact evaluation) versus position-side `Λ(n)` (shifted
convolutions = **Hardy–Littlewood**). E18's one obstruction, in its arithmetic
core: *divisors correlate provably, primes conjecturally.*

**The translation layer exists and this project has already met it from the
other side:** Vaughan's identity decomposes `Λ` into `d`-like pieces plus
bilinear remainders — which is exactly how BHB13 removed GLH (LEADS L11).

**Where the rate would be a theorem.** Both barriers are broken by the *same
arithmetic input*: off-diagonal / shifted-convolution estimates — Conrey's
`4/7` came from Deshouillers–Iwaniec Kloosterman input, and support past
`|α| = 1` needs Hardy–Littlewood. Their common engine is the **additive divisor
problem**, and the richest certified object living there is **Motohashi's fourth
moment** — which is `LEADS` W22, previously filed as a "deep probe". W22 is
therefore promoted: it is not a probe, it is **the named seam of the two
budgets**.

*(Provisional throughout: the currency identification is a heuristic reading,
not a checked correspondence. The check that would settle it is whether the
mollifier-length and support barriers admit a common statement in
shifted-convolution terms.)*

## The `𝒩` crumb, priced (day cycle 1)

| route | verdict | distance |
|---|---|---|
| single identity | **circular** — one equation, two unknowns | ∞ |
| two λ's + monotonicity, exploiting `M_main`'s dip | **not circular; genuinely free** | needs `c₀ < 0.0463` vs proved floor `0.16` — **3.5×** |

The distance is entirely the error term's small-`λ` shape (`√log(2+λ)/λ`), since
`M_main`'s dip and the error's blow-up occupy the same region. Improving the
`λ → 0` dependence — not proving anything new about zeros — is what buys the
crumb.

## The sign check (day cycle 5) — **the container consumes an UPPER bound, and sieve strength suffices**

`κ = 1/λ + jWin`, `jWin = 2∫₀¹ D(λr)·(v⋆v)(r)dr`, proportion `= 2 − κ`. Since
`v⋆v ≥ 0`, a **larger** form factor gives a larger `κ` and a worse proportion —
so every certificate in this container consumes an **upper bound** on `D`, never
an asymptotic. That is the favourable sign, and it means *sieve* input converts.

Flat window, `D(s) = s` for `s ≤ 1` (the BGST-unconditional diagonal regime) and
only `D(s) ≤ K` past `1`:

| λ | K=1 (PCC) | K=2 | K=3 | K=4 |
|---|---|---|---|---|
| 1.20 | 0.7685 | **0.7407** | **0.7130** | **0.6852** |
| 1.60 | 0.8698 | 0.7292 | 0.5885 | 0.4479 |
| 2.00 | 0.9167 | 0.6667 | 0.4167 | 0.1667 |
| 4.00 | 0.9792 | 0.4167 | — | — |

> **A constant upper bound `K ≲ 4` on the form factor past support 1 beats the
> bandlimited ceiling `0.6818287`** — at `λ = 1.2`, with the *flat* window, no
> window optimisation at all. `K = 2` gives `0.741`, a 7pp jump over the record.

**Why this is the live front.** The best classical sieve upper bound for prime
pairs sits around `3.4` (Wu), i.e. **just inside** the `K ≲ 4.1` requirement —
so the arithmetic may already exist at the needed strength, and what is missing
is only the *transfer* of a sieve bound into `𝓕` past support 1, which is
precisely the weight-retaining move BGST already executed at support `≤ 1`.

### Corrected: averaged consumption, done properly (day cycle 6)

Abel summation converts an *averaged* bound into the same arithmetic as a
pointwise one. With `w(u) = 1 − u/λ` decreasing, `M(u) = ∫₁^u D`, and
`M(1) = w(λ) = 0`:

> `∫₁^λ D(u)w(u)du = (1/λ)∫₁^λ M(u)du ≤ (1/λ)∫₁^λ A(u)du`

so for `A(u) = c(u−1)` — CCLM's "`c` per unit of support" —

> `κ(λ,c) = 2/λ − 2/(3λ²) + c(λ−1)²/λ²`, and the averaged constant `c` enters
> **identically** to the pointwise `K`.

> ⚠️ **RETRACTED — read this before the two tables below.** These break-even
> constants and the `c`-sweep are the table `ISSUES` #24 found unsound (scale
> mismatch *and* circularity) and `ISSUES` #25 found **vacuous**: Lemma 1 makes
> unit-window mass `> 3` RH-*impossible*, so `c ≤ 7.995` and `c ≤ 9.532` sit
> entirely in impossible territory. The full retraction note is below at
> "RETRACTED as a bound"; it is repeated here because it used to sit *after* the
> numbers, where a reader could quote them without reaching it. **Do not cite any
> figure in the next two tables.**

**And optimising `λ` moves the thresholds a long way** (as `c` grows the optimum
slides toward `λ → 1`, buying only as much past-1 support as the constant
affords). Break-even constants:

| target | needs |
|---|---|
| bandlimited ceiling `0.6818287` | **`c ≤ 7.995`** |
| CGdL under RH, `0.6792` | `c ≤ 9.532` |
| BHB13, `0.7037` | `c ≤ 3.667` |

| `c` | best proportion | at `λ` |
|---|---|---|
| 1.4283 (CCLM, large `β`) | **0.8126** | 1.78 |
| 2 | 0.7500 | 1.33 |
| 4 | 0.7000 | 1.11 |
| 8 | ~0.6818 | 1.05 |
| **10.824** (pre-CCLM implicit) | **0.6776** | 1.03 |

**This corrects my own earlier `K ≲ 4`**, which came from a coarse `λ` scan: the
true requirement is `c ≲ 8`. Note what that does to the alarm — even the
*pre-CCLM* constant `10.824` lands only `0.4pp` below the ceiling, so the
composition dies only if the short-range constant exceeds the old implicit one.

**RETRACTED as a bound (ISSUES #24).** The Abel step needs the averaged bound
at *every* scale `u−1 ∈ (0, λ−1]`; the literature's constants are asymptotic in
the averaging length `ℓ`. And `1.3208` is an *output* of the same extremal
problem, so feeding it back is circular. The table stands only as a
**sensitivity curve** — what a genuinely new, correctly-scaled input would buy —
and the only input class passing both tests is **sieve bounds on prime pairs**
(pointwise in the shift, arithmetic rather than zero-side).

**Caveats, load-bearing:** the model `D ≤ K` constant past 1 is crude; the
dictionary from a twin-prime sieve constant to `K` is unchecked (this is the
Goldston–Montgomery item); the flat window is not optimised; and the transfer
past 1 is exactly the unbuilt span. The *sign*, however, is not a modelling
choice — it follows from `v⋆v ≥ 0`.

## Both walls, at once (day cycle 7)

The corridor's **width** is purchasable, not just its ceiling: a window with
sign-changing autocorrelation consumes `U` where `v⋆v > 0` and `L` where
`v⋆v < 0`. First measurement, `U = 2` with the GGOS floor: **0.804 versus 0.747
flat, +5.7pp**, optimum at `min(v⋆v) = −0.034`. See ISSUES #23; RH-conditional
and quarantined.

## The corridor's walls are primal–dual twins of one LP (named statement)

Upper and lower averaged `F`-bounds both fall out of EP1's duality — which is
why they share constants (`1/K_ν(0,0) = 1/2 + (1/√2)cot(1/√2)`, the M–T value)
and why **no certificate of any sign structure can extract net width from
them**: a certificate escaping the primal class still eats inputs manufactured
by the dual. Two-sidedness must enter through the **inputs**, and the only
inputs outside the program are **arithmetic**.

Confirmed numerically (#25): on class inputs at correct scale the container's
optimum is `λ = 1`, i.e. Montgomery's `2/3` — no support extension at all.

## RETRACTED: the fuel reach is `A = 1` (day cycle 11, ISSUES #27)

The MRT→bridge gate **fails by a power of `X`**: the weighted sum amplifies each
shift's error by `h`, so the bridge needs power savings and MRT gives log-power
savings. Fuel reaches only the band edge — already closed by the sieve — so the
priced `0.80869` is retracted and the corridor is **everything past `α = 1`**,
unfuelled. The named target is now *averaged HL with power saving* (survey (6.3)).

## The tiling (day cycle 10)

The two instruments do not compete, they **tile**: exact `F` on `[1, A]` from
arithmetic fuel (`A = 1/(1−θ)`), and the sign-changing window as the only tool
on the corridor `(A, ∞)`. Where `F` is *known* there is no corridor, so the
window contributes nothing below `A` — its payoff **grows with** `A`. Hence
`θ`-progress and corridor-wall progress **multiply**.

## Standing rule

Every future escape claim gets a row here, with the theorem or computation that
priced it. A channel with no price is a hope, not a lead.


## W12 (overnight cycle 6): depth-shaped information has price **exactly** zero

Not "approximately zero", and not because Vinogradov–Korobov is about the wrong
end of the strip. Because of X.

`N⊛ = Σ_ρ H(γ_ρ)` is **depth-blind**: a zero at `β = 0.9` and a zero at
`β = 0.5001` contribute *identically*, since `H` counts an ordinate's mass and
`μ_T` has no `β` coordinate at all. So a statement of the form "no zeros with
`β > σ`" cannot be spent in this container — it constrains a coordinate the
container does not read.

The exchange rate that follows, and it is the useful part:

> **Any horizontal input must be uniform down to `δ = 0`, or it buys nothing.**

Classical density theorems `N(σ,T)` fail that test by construction: they are
nontrivial only for `σ` bounded away from `1/2`, and the zeros that dominate
`N⊛` are those at `δ → 0`. This is a *stronger* statement than ISSUES #10 made.
#10 said the dead strip is where classical density theorems fall silent; W12
says depth-shaped information is unusable **at every depth**, because the cost
function has no depth argument. The silence in the strip is a symptom, not the
disease.

Which is why the two horizontal channels that *do* have finite prices —
parity (free) and the row-crossing (`(C−1)/6`) — are both **counting**
statements about atoms, not geometric statements about `β`.

## The evaluation column (W16, re-priced) — `forensics/w16_price.py`

`landau_discriminates` closed the **vision** half: the discriminating functional
exists, is elementary, and is kernel-certified. So the column that matters now
is **evaluation** — what does it cost to certify Landau-type values on `ζ`'s
actual zeros? Priced here for the first time, in the coordinate `x = T^c` with
depth `δ = 1/log T` (which makes `δ·log x = c` exactly).

**Wildcard, kill condition stated first:** *if the crossover `c` at a height
where zeros are known (`T ≲ 10^13`) is `≤ 1`, the unpaid range `c ∈ (1,2)` is
unaffordable at every feasible height and the Landau route is dead outright
rather than merely unpaid.* **It did not fire.**

### The signal is scale-free in this coordinate

Per-pair excess over the on-line chorus, exactly (`Fiber.lean` + AM–GM):
`x^a + x^{1−a} − 2x^{1/2} = 2x^{1/2}(cosh(δ log x) − 1)`. At `x = T^c` and
`δ = 1/log T` this is `2x^{1/2}(cosh c − 1)` — a **fixed fraction of the chorus
term, set by `c` alone**. The signal does not fade with `T`.

| `c` | 0.5 | 1.0 | 1.5 | 2.0 | 2.25 |
|---|---|---|---|---|---|
| `cosh c − 1` | 0.128 | 0.543 | 1.352 | 2.762 | 3.797 |

### The price, and where the affordable-but-unpaid window sits

Aggregate **unphased** excess `κ·N(T)·x^{1/2}(cosh c − 1)` against
Landau–Gonek's `E ≪ x log(2xT) loglog 3x` gives margin
`κ·T^{1−c/2}(cosh c − 1) / (2π(1+c)·loglog x)`. Crossover `c` (largest `c` still
clearing 1):

| `T` | `κ=1` | `κ=0.01` | `κ=10⁻⁴` |
|---|---|---|---|
| `10^6` | 1.482 | 0.665 | 0.010 |
| `10^12` | 1.744 | **1.386** | 1.021 |
| `10^24` | 1.870 | 1.698 | 1.525 |
| `10^50` | 1.936 | 1.855 | 1.774 |
| `10^100` | 1.967 | 1.927 | 1.887 |

At `T = 10^12`, `κ = 0.01`: the window is **`c ∈ (1, ≈1.39]`** — nonempty, at a
height where zeros have actually been computed. It **opens** at `T ≈ 10^7.6`
(`κ = 0.01`) or `T ≈ 10^3.4` (`κ = 1`), and widens to `(1,2)` as `T → ∞`.

### What is actually being bought

**The binding constraint is the phase, not the magnitude.** Every margin above
is for the **unphased** sum. Landau–Gonek supplies the **phased** one: each
excess arrives multiplied by `e^{iγ log x}`, one unknown per zero. Killing the
phase is what second moments in `x` do, and that device is paid only to the
diagonal. **So the price of the Landau route is the price of exactly one
phase-removal**, and every other line item on this page is affordable.

Census `#1` said this in words — *phases shared with the on-line chorus*. This
column says it with a number, and locates the unpaid stretch.

### And the asymptotics lie in the other direction this time

The exponent `1 − c/2` promises every `c < 2` eventually clears. At `T = 10^12`
the crossover is `1.39`; reaching `c = 1.9` needs `T ≳ 10^50`. `#27`'s
asymptotics were **crueller** than the numerics (invisibility radius `10^13`–`10^671`);
here they are **kinder**. Both times the honest statement required computing the
crossover rather than reading the exponent — which is the general lesson and
belongs beside `S`'s invisibility-radius entry.

### Caveat the conclusion leans on

Identifying "paid" with `c ≤ 1` assumes the correspondence between this
coordinate and the pair-correlation support parameter (`𝓕` known for support
`≤ 1`). That dictionary is **[RECALL, UNVERIFIED]** — the same `h ↔ α` check
already open in the registers. If the true correspondence is `c ≤ 2`, the unpaid
window is **empty** and this column's second reading collapses. Nothing else
here depends on it. **This is now the cheapest high-value verification on the
board.**


## Route II, priced in ledger currency (SESSION 087)

The `Nsc` row now has an exchange rate. `proportion_of_offLineImport`
(axiom-free): `ProportionStd κ` together with `N_off ≤ (β + o(1))·N` gives
`Proportion (κ − β/2)`. **Every point of off-line control is worth half a point
of the project's own row.** At `β = 1` — the trivial bound `N_off ≤ N` — this is
exactly `certified_nsc_unconditional`'s `0.50875`.

**What Route II would pay.** `offLineImport_of_derivative`: a `Proportion κ'`
for the derivative family gives `β = 1 − κ'`, because the derivative's simple
on-line zeros crowd out its off-line ones (`Blindness.Nsc_add_Noff_le_N`). With
zeta-23's `ξ'` value `κ' = 0.85838`, `β = 0.14162` and the row would read

> `0.6725 − 0.07081 = 0.60169`

**a gain of 9.29 points, from results the project already holds.**

> ### `SESSION 162` — the off-line genre has one shape, and it loses
>
> Enumerated mechanically: **four** declarations in the development conclude in
> `OffLineImport`, and every one of them carries `β = 1 − κ`:
>
> | declaration | `β` |
> |---|---|
> | `offLineImport_of_proportionStd` | `1 − κ` |
> | `offLineImport_of_derivative` | `1 − κ'` |
> | `certified_offline` | `1 − 0.6725 = 0.3275` |
> | `offline_via_xiPrime` | `1 − 0.85838 = 0.14162` |
>
> So `161`'s circularity is **structural, not incidental**: the machinery has no
> way to make an off-line bound that is not one minus somebody's proportion.
> ⚠️ **`SESSION 166` — and this is true of `OffLineImport` only.** Classifying
> the *inputs* of the `HauntedDensity` producers, two of the three accept
> something the off-line shelf cannot supply:
>
> | producer | input | circular? |
> |---|---|---|
> | `hauntedDensity_of_offLineImport` | `OffLineImport β` | yes — `β` is structurally `1 − κ` |
> | `hauntedDensity_of_starBound` | `StarBound C` | **no** — `StarBound` has independent producers (`routeIII_with_narrowBox`, `starBound_of_multiplicity_le`) |
> | `hauntedDensity_of_distinctZeros` | a raw `atomCount ≥ c·Nz` bound | **no** — takes any distinct-zeros lower bound |
>
> So the transfer layer has **two open channels**, and the project has fed
> neither anything but the baseline: `certified_haunted_via_distinctZeros`
> instantiates `c = 0.6725` from `certified_atomCount`, which is the baseline
> again. **The want-ad is a distinct-zeros bound `c > 0.6725` from the
> Cheer–Goldston literature the docstring already names** — an input the
> machinery can accept and has never been given.
>
> ⚠️ **`SESSION 167` — fetched, and it does not fill the want-ad, for two
> independent reasons.** Wu, *Distinct zeros of the Riemann zeta-function*
> (arXiv:1206.3737), **Theorem 1**: `N_d(T) ≥ 0.66036·N(T)`, unconditional — the
> best in that line (Farmer 1995 had `63.9%`).
>
> 1. `0.66036 < 0.6725`, so it is **below** what `certified_atomCount` already
>    supplies from the baseline.
> 2. More basically, **it is the wrong quantity.** Wu's `N_d` counts distinct
>    *zeros* — displayed there as `|{ρ = β + iγ : …}|` — while `atomCount` counts
>    distinct **ordinates**. `Blindness.atomCount_le_distinctZeros` (axiom-free)
>    shows the collapse runs `atomCount ≤ N_d`, so a **lower** bound on `N_d`
>    does not lower-bound `atomCount`. Under RH they coincide; unconditionally
>    the gap between them is precisely the off-line structure.
>
> The channel stays open and the want-ad stands, now dated against a primary
> source rather than carried as `[RECALL]`.
>
> ✅ **`SESSION 168` — completed in the reverse direction, and it is `161`'s wall
> again.** `Blindness.distinctZeros_le_atomCount_add_Noff` (axiom-free) gives
> `atomCount ≥ distinctZeros − Noff`, so Wu's theorem *can* be pointed at our
> quantity after all. The arithmetic then decides it:
>
> * `0.66036 − 0.3275 = 0.33286`, against the baseline's `0.6725` — so the route
>   halves what we hold, and `δ ≤ 0.33357` against `certified_haunted`'s
>   `0.16375`.
> * And it can **never** win: beating `κ` needs `N_d/N > κ + (1 − κ) = 1`, while
>   `distinctZeros ≤ N` always. **Tie at `N_d = N`, never exceeded.**
>
> That is the identical wall `161` found for `NscAny`, from the identical cause —
> the `Noff` it pays with is `1 − κ`, minted from the row being raised. **Third
> instance.** The distinct-zeros channel is open in form and closed in
> arithmetic, exactly like the other two, until an independent off-line bound
> exists.
>
> ✅ **`SESSION 169` — and `β = 1 − κ` is optimal, not just what our producers
> emit.** `Noff_add_NscStd_le_N` gives `Noff ≤ N − NscStd ≤ (1 − κ)·N` directly,
> so no rearrangement of the same information does better; and
> `Blindness.offLine_bound_attained` (axiom-free) exhibits equality — one
> ordinate with a single critical zero and one off-line pair, `N = 3`,
> `Noff = 2`, `NscStd = 1`. **There is no slack to recover.**
>
> So the want-ad below is for **new arithmetic information**, not for a cleverer
> derivation: any `β < 1 − κ` must consume something `ProportionStd κ` does not
> contain.
>
> ⚠️ **`SESSION 170` — and the narrow box does not supply it either, so the shelf
> has TWO open problems, not one.** `Gaps.NarrowBox` — Route III's hypothesis —
> bounds how *far* a zero sits from the line. `Noff` counts how *many* sit off
> it, and `Blindness.offLine_count_not_bounded_by_proximity` (axiom-free) shows
> the two are unrelated: for every `ε > 0` there is a configuration whose zeros
> all lie within `ε` of the line and whose off-line count is **all of them**.
>
> **This corrects `168`'s "one thing, not three".** There are two channels into
> the `Nsc` row and only one is walled:
>
> | channel | route | walled by `β = 1 − κ`? |
> |---|---|---|
> | `ProportionStd` → off-line / haunted exchange | the ladder, ξ′, `NscAny`, distinct-zeros | **yes** |
> | `StarBound` → `Proportion (2 − C)` | **Route III**, `starBound_of_mult_le` | **no** |
>
> That is why Route III's cone is `1` axiom and why it was never subject to the
> wall — it does not pass through the off-line exchange at all.
>
> ✅ **`SESSION 171` — the unwalled channel enumerated, and it holds no new
> supply.** All eight `StarBound` producers are guarded in
> `forensics/board.py`. Two are **axiom-free**:
>
> | producer | pays | verdict |
> |---|---|---|
> | `starBound_of_multiplicity_le` | `Proportion (2 − M)`, beating `0.50875` only at `M = 1` | `M = 1` is *every zero simple* — the target, not a route |
> | `routeIII_with_narrowBox` | `4/3 → 2/3` | already the menu's Route III row |
>
> The ζ-level instances (`starBound_of_multiplicity_two`,
> `starBound_of_mult_le_two_zeta`) carry `baseline_zeta23` in their cones despite
> proportion-free *statements* — they instantiate with the certified row inside
> their proofs. **So the second channel is genuinely unwalled and genuinely
> empty of anything the menu does not already list.**
>
> ✅ **`SESSION 175` — and the multiplicity producer has no slack either.**
> `Blindness.Nstar_bound_attained` (axiom-free): a single ordinate of mass `M`
> gives `Nstar = M² = M·N`, so `StarBound M` is **optimal** given `H ≤ M`, just
> as `169` showed `β = 1 − κ` optimal on the off-line channel. Combined with
> `171`'s arithmetic — `Proportion (2 − M)` beats the certified row only at
> `M = 1` — the multiplicity producer on this channel is now closed on both
> sides: **its constant cannot be improved and its payout is empty above
> `M = 1`.**
>
> **Tightness map, both channels complete:**
>
> | channel | producer | constant optimal? | payout |
> |---|---|---|---|
> | off-line / haunted | `ProportionStd κ` | **yes** (`169`, attained) | walled — needs input exceeding 1 |
> | `StarBound` | multiplicity `H ≤ M` | **yes** (`175`, attained) | empty above `M = 1` |
> | `StarBound` | narrow box | not asked — the constant is BGST's, imported | Route III, `+15.79` |
>
> ⚠️ **`SESSION 176` — the sentence that stood here was an unscoped absolute and
> is withdrawn.** It read *"every derivation the project owns is now known to be
> tight"*. Counted mechanically: the development has **99** inequality-concluding
> theorems and about **21** tightness or attainment witnesses. Most of its
> inequalities have never been shown tight, and nothing here established that
> they are.
>
> **What `169` and `175` actually established** is narrower and is the part that
> matters: the two **exchange constants** by which every route reaches the ledger
> are optimal and attained —
>
> * off-line channel: `β = 1 − κ` (`offLine_bound_attained`);
> * `StarBound` channel: `C = M` from `H ≤ M` (`Nstar_bound_attained`).
>
> So no route on the board is losing points to a sharpenable exchange rate. That
> is the claim; "every derivation is tight" is not. What remains open is still
> entirely **imported** — Route III's `BGSTNarrowBox` and the menu's
> hypotheses — and that part stands.
> Fed back through `proportion_of_offLineImport`, that returns `(3κ − 1)/2`,
> which `offline_roundtrip_loses` (axiom-free) shows is `< κ` for every `κ < 1`,
> with equality exactly at `κ = 1` (`offline_roundtrip_eq_iff`).
>
> **And `084`'s number is this loop.** `(3·0.6725 − 1)/2 = 0.50875` is the
> baseline having gone once around it — which is why `111`/`112` find the row
> unimprovable from the baseline alone. The two facts were filed separately and
> are one.

> ⚠️ **`SESSION 147` — the arithmetic above is now a theorem, and the price was
> understated.** `Riemann.certified_nsc_via_xiPrime` proves
> `Proportion 0.60169` from the two hypotheses, so nothing here is a
> docstring calculation any more. But `#print axioms` on it returns **four**
> project axioms — `baseline_zeta23, xiPrimeFamily, zeta23_xiPrime,
> zetaNonempty` — against the certified row's **two**. So the route costs *two
> hypotheses **and** two extra axioms*, and adopting it would move the ledger's
> `axioms:` field from 2 to 4. Every entry below that prices this route as "two
> `Prop`s" is pricing half of it.

**Why it is not claimed.** Two hypotheses, both carried as `Prop`s and neither
an axiom, per `Assumptions.lean`'s own rule:

1. `OffTransfer` — `levinson_montgomery` gives `|N_off' − N_off| ≤ c·log T`;
   absorbing the `log T` into `o(N)` needs Riemann–von Mangoldt, which is not in
   the registers.
2. `NzComparable` — `xiPrimeFamily` is an **opaque axiom** with no stated
   relation to `zetaFamily`; nothing in the development connects their zero
   counts. The consistency model even sets the two families equal.

Both are classical and neither is deep. **This is now the cheapest 9 points on
the board**, and unlike a better `κ` it does not need a new theorem about `ζ` —
only the plumbing that says `ξ'` has about as many zeros as `ζ`.

*Ruling for Joop: adding these as axioms would raise the certified proportion by
assumption, which `Assumptions.lean` forbids and `SESSION.md` must flag. They
should be discharged, not assumed — most plausibly by extending the zeta-23
import, which already reasons about both families.*


## The exhaustive axiom audit (SESSION 088)

Two route lists in four cycles turned out to be short (`S34`, and `087`'s Route II
pricing). The axiom list is **finite**, so this enumeration can be exhaustive by
construction rather than by assertion — which is the whole point of running it.

All nine declared axioms, each with its ledger value and the reason:

| axiom | ledger value | status |
|---|---|---|
| `zetaNonempty` | not a proportion input; supplies positivity | **realised** |
| `xiPrimeFamily` | an opaque `Family` constant, not a claim | nil alone; carrier for `zeta23_xiPrime` |
| `closePairsZeta` | an opaque function constant | nil alone |
| `fujii_ineffective` | `∃ c₀, ∀ λ, StarBound (Cbound c₀ λ)`. `Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀√(log(2+λ))/λ` grows with `c₀` and has no `c₀`-uniform minimum over `λ`, so **no numerical `C` is extractable** | nil until `c₀` is effective — checked by reading `Cbound`, not by trusting the note |
| `fujii_closePair_bookkeeping` | conditional on `EffectiveFujii` **and** `ClosePairLowerBound` | nil until both |
| `zeta23_xiPrime` `0.85838` | **9.29 points**, blocked on `OffTransfer` + `NzComparable` | ⚠️ **`SESSION 150`: no longer "the one live item"** — see the axiom-cost comparison below (`087`) |
| `levinson_montgomery` | an input to that route | realised in `087`'s pricing |
| ~~`baseline_przz`~~ `0.4162` | **none — it is a theorem** (`przz_of_zeta23`) | **DELETED, `SESSION 233`** on Joop's ruling 3; declared surface `9 → 8` |
| `baseline_zeta23` `0.6725` | the `NscStd` row, and via `084` the `Nsc` row | **realised twice** |

**Kill condition, filed first:** *if every axiom's ledger value is already
realised or provably nil, the audit yields nothing and I say so.* **On its own
terms it fired** — no new ledger value exists in the axiom list. The audit still
returned something, and it is assumption-surface rather than proportion:

> **`baseline_przz` is redundant.** `Family.ProportionStd.mono` (new,
> axiom-free): `ProportionStd` is monotone in its constant. Since
> `0.4162 ≤ 0.6725`, `przz_of_zeta23` derives the PRZZ baseline from the zeta-23
> baseline, and `#print axioms` confirms it consumes only `baseline_zeta23`.
> Nothing in the development consumes `baseline_przz` today.

**Side effect worth naming.** `STATEMENTS.md` records `baseline_przz` as "stated
on `NscStd`", per Joop's `ISSUES #13` ruling. Whether PRZZ's `41.62%` is really
a *simple*-zero proportion or an on-line proportion is a literature question
**[RECALL, UNVERIFIED]** — and the redundancy makes it moot for the ledger,
because nothing rests on the axiom either way. Recorded so a future cycle does
not spend a literature probe on a question that cannot change a number.

> **ANSWERED, `SESSION 233`.** Joop ruled *delete*, and it was done with the
> ceremony the metric requires: the base statement hash moved
> `cd7a22e688df → c3b240548ad8`, `tools/proportion.go` refused a log line until
> `base.version` was bumped `2 → 3`, and declared axioms went `9 → 8`. No
> certified number moved. `Riemann.przz_of_zeta23` keeps the literature record
> as a theorem. The request below is closed.

*Ruling for Joop: delete `baseline_przz` (declared surface 9 → 8) or keep it as
the record of an independent literature result, which matters only if the
zeta-23 baseline is ever retracted. Not taken unilaterally.*


## `(★)` from multiplicity alone (SESSION 096)

`092` priced a multiplicity supremum `M` as worthless: it gives `StarBound M`,
and `prop1` needs `C < 2`, so `M ≤ 1` — simplicity, the conclusion.

**That pricing was for the bare supremum, and it is wrong for the combination.**
`Nstar_add_mul_Nsc_le` charges a simple atom `1` rather than `M`, so a certified
`Nsc` row buys the constant down:

> `C ≤ 1 + M·(1 − κ)`

At the ledger's `κ = 0.50875` this is `< 2` **as soon as `M = 2`**. So:

> **If no zero of `ζ` has multiplicity three or more, `(★)` holds** with
> `C ≤ 1.9825`, unconditionally otherwise.

**What it is worth, stated plainly.** Through `prop1` this yields
`Proportion 0.0175` — far worse than the `0.50875` already certified, so it buys
**nothing** on the headline row. Its value is that `(★)` is what Routes I and III
exist to produce, and `(★)` feeds `offline_le` and the narrow box, neither of
which the `Nsc` row reaches. A hypothesis strictly weaker than RH-simplicity now
closes the program's central gap.

**And the exchange rate is now explicit:** every point of the `Nsc` row buys `M`
points of star constant. At `κ = 2/3` the criterion would reach `M = 2` with room
to spare; at `κ → 1` it reaches any fixed `M`. So improving the `Nsc` row and
bounding multiplicities are the *same* purchase seen from two ends — which is a
connection the route table did not have.


## The haunted ladder (SESSION 105)

`104` proved the `Nsc` row's bound is tight **exactly** on mixtures of simple and
haunted-mass-`3` atoms. So the constant `3` is bought by one shape, and excluding
it raises the constant. The ladder:

> `NoSmallHaunted F m` (every haunted ordinate carries `≥ m` zeros)
> `⟹ Proportion ((m·κ − 1)/(m − 1))`.

At `κ = 0.6725`:

| `m` | hypothesis | `Nsc` row |
|---|---|---|
| `3` | vacuous — this is `084` | `0.50875` |
| `5` | no haunted ordinate of mass exactly `3` | **`0.590625`** |
| `7` | none of mass `3` or `5` | `0.617917` |
| `→ ∞` | no haunted ordinate at all | `0.6725` — the whole baseline |

⚠️ **Read only the odd rungs (SESSION 106).** Haunted ordinates carry **odd**
mass (`Fiber.haunted_odd`), so `NoSmallHaunted m` at even `m` is already the
hypothesis at `m + 1` (`noSmallHaunted_succ_of_even`) and the even rung
understates its own hypothesis — `m = 4` would report `0.5633` for a hypothesis
that actually delivers `0.590625`. At odd `m ≥ 3` the constant is **sharp**
(`ladder_sharp_at_odd`): the haunted atom of mass `m` forbids any larger one.

**The `m = 5` rung is the cheap one.** Its hypothesis is not "no off-line zeros";
it permits off-line pairs anywhere *except* shadowing a lone critical zero at
mass exactly `3`. That is a statement about one configuration, and it is worth
**8.2 points** — comparable to `087`'s ξ′ route (`9.29`) and asking for something
quite different.

*Both remain hypotheses. Neither is asserted, and the ledger stays at `50.88%`.*

> ## ⚠️ `SESSION 150` — the two routes were never compared in the currency that matters
>
> Both are now **theorems** at the ζ level (`147` closed the first, `150` the
> second), so `#print axioms` can price them in trusted base rather than in
> prose:
>
> | route | gain | hypotheses | **axiom cone** |
> |---|---|---|---|
> | ξ′ (`certified_nsc_via_xiPrime`) | **+9.294** → `0.60169` | `OffTransfer`, `NzComparable` — analytic, Conrey 1983, unread | **4** — adds `xiPrimeFamily`, `zeta23_xiPrime` |
> | `m = 5` ladder (`certified_nsc_via_noSmallHaunted`) | **+8.188** → `0.590625` | `NoSmallHaunted zetaFamily 5` — combinatorial, about ζ's own zeros | **2** — `baseline_zeta23`, `zetaNonempty`, i.e. **no increase at all** |
>
> **The cheaper route costs `1.106` points and buys back two axioms.** The
> register called the ξ′ route "the cheapest nine points on the board" and "the
> one live item"; in points that is right, and in *garbage height* (`R5`: every
> axiom raises the stack without being clearable) it is the more expensive of
> the two. Neither is asserted and the ledger stays at `50.88%`.
>
> ⚠️ **`SESSION 151` — I compared the wrong rung, and there is no trade-off at
> all.** The table above uses `m = 5` because `150` inherited the register's
> phrase "the `m = 5` rung is the cheap one". The ladder's own table two blocks
> up also lists **`m = 7` at `0.617917`**, now a theorem
> (`certified_nsc_via_noSmallHaunted_seven`, cone **2** axioms):
>
> | route | gain | axiom cone |
> |---|---|---|
> | ξ′ | `+9.294` | 4 |
> | `m = 5` | `+8.188` | 2 |
> | **`m = 7`** | **`+10.917`** | **2** |
>
> So ξ′ is **dominated in both currencies** — more proportion is available at
> fewer axioms. The only axis on which ξ′ can still win is **hypothesis
> strength**, and that is the axis a ruling should actually turn on. Two cycles
> priced this as a trade because both read "the cheap one" and neither looked one
> row further down the register's own table.
>
> ### `SESSION 152` — the complete menu, and the multiplicity route is dominated
>
> The multiplicity hypothesis looked like a second dial (`starBound_of_mult_le`
> is parameterised in `M`). It is not: stating it generally
> (`proportion_of_mult_le_zeta`) gives `2 − (M − (M−1)κ) = (M−1)(κ−1) + 1`,
> **strictly decreasing in `M`** for `κ < 1` (`mult_ladder_no_gain`, axiom-free).
> One live rung, at `M = 2`.
>
> And that rung is **dominated too**: `H ≤ 2 ⟹ NoHaunted`
> (`Blindness.noHaunted_of_mult_le_two`) and `NoHaunted` is *strictly weaker*
> (`noHaunted_not_mult_le_two`), while both return `0.6725`. So a stronger
> hypothesis buys the same number.
>
> | route | gain | axioms | hypothesis |
> |---|---|---|---|
> | `m = 5` haunted rung | `+8.188` | 2 | no haunted ordinate of mass `3` |
> | ξ′ | `+9.294` | **4** | two analytic `Prop`s, Conrey 1983, unread |
> | `m = 7` haunted rung | `+10.917` | 2 | none of mass `3` or `5` |
> | **`NoHaunted`** (`m → ∞`) | **`+16.375`** | 2 | no haunted ordinate at all |
> | `H ≤ 2` | `+16.375` | 2 | **strictly stronger than `NoHaunted`, same payout — dominated** |
>
> Nothing is asserted; every row is conditional and the ledger stays `50.88%`.
>
> ### ⚠️ `SESSION 163` — the menu was missing a row, and it is the cheapest one
>
> Enumerating every declaration concluding in a transfer predicate turned up a
> producer whose constant is **not** minted from a ledger row:
> `Program.routeIII_with_narrowBox` takes a narrow-box hypothesis to
> `StarBound (4/3 + ε)`, and `conjectural_routeIII` carries that to the `Nsc`
> row. In exact rationals:
>
> | route | `Nsc` row | gain | axiom cone | hypothesis |
> |---|---|---|---|---|
> | `m = 5` | `0.590625` | `+8.188` | 2 | multiplicity |
> | ξ′ | `0.60169` | `+9.294` | 4 | analytic, unread |
> | `m = 7` | `0.617917` | `+10.917` | 2 | multiplicity |
> | **Route III** | **`2/3 − ε`** | **`+15.79`** | **1** | **location (narrow box)** |
> | `NoHaunted` | `0.6725` | `+16.375` | 2 | multiplicity |
>
> Its cone is `zetaNonempty` **alone** — it does not even consume
> `baseline_zeta23`, because it reaches the row through `StarBound` rather than
> through the baseline. So it is the **cheapest row on the board in trusted
> base**, and second-highest in payout.
>
> ### ⚠️ `SESSION 164` — completing the sweep, and the menu was the cheap end of a longer board
>
> `163` added one row and stopped. The same sweep listed **28** declarations
> concluding in `Proportion`; finishing the enumeration found **two more** that
> beat the certified row, both at **one** axiom:
>
> | route | `Nsc` row | gain | axioms | hypothesis |
> |---|---|---|---|---|
> | `m = 5` | `0.590625` | `+8.188` | 2 | multiplicity |
> | ξ′ | `0.601690` | `+9.294` | 4 | analytic, unread |
> | `m = 7` | `0.617917` | `+10.917` | 2 | multiplicity |
> | **Route III** | `0.666667` | `+15.792` | **1** | location (narrow box) |
> | `NoHaunted` / `H ≤ 2` | `0.672500` | `+16.375` | 2 | multiplicity |
> | **Route I** | `> 0.6725` | `> +16.375` | **1** | effective Fujii `c₀ ≤ 0.33` |
> | **[OPEN D]** | `1 − ε` | `+49.125` | **1** | extended support |
>
> ✅ **`SESSION 165`: the board is now extracted, not recalled.**
> `forensics/board.py` lists every declaration concluding in a `zetaFamily`
> proportion and **exits 1 if that set changes**, so a row cannot appear or
> vanish unnoticed again. It found 13, and corrected the hand list on its first
> run. Fault-injected both directions.
>
> **The last row has been on every ledger line since the project began** — it is
> the `conjectural: 100.00% (OPEN D)` field. Nothing was hidden and nothing is
> new here except the comparison.
>
> **What this does and does not say about the ladder.** The `m`-rungs are real
> work: `147`–`158` built them and certified their ordering, strictness, limit
> and non-vacuity, none of which existed before. What was wrong was calling that
> collection *the board*. It is the **cheap-hypothesis end** of a board whose
> expensive end the project has tracked in a different field of its own metric
> the entire time.
>
> **Why it was missed:** it lives in `Proportion.lean`'s `Conjectural` section,
> filed as a *route* in the program's original sense, while the menu was built
> from the `HauntedDensity`/`OffLineImport` layer. Nothing was wrong with it; it
> was in a different drawer. Nothing here is asserted — `BGSTNarrowBox` and
> `NarrowBox` are hypotheses, exactly like the ladder rungs.
>
> ✅ **`SESSION 156` — the dial is certified to be a dial.** The menu presents
> `m = 5, 7, → ∞` as a scale, which needs the hypotheses to be comparable and
> the top row to be the chain's limit. Both are now theorems, **axiom-free**:
> `NoSmallHaunted.mono` (rung `m+1` implies rung `m`, so the rungs are nested)
> and `noHaunted_iff_forall_noSmallHaunted` (`NoHaunted ↔ ∀ m, NoSmallHaunted m`,
> so the top row is the chain's limit and not a separate item that happens to pay
> more).
>
> ✅ **`SESSION 157`: and the chain is strict.** `noSmallHaunted_strict` gives, at
> every rung, a configuration clearing it and failing the next — one ordinate with
> one critical zero and `j` off-line pairs, haunted of mass exactly `1 + 2j`. So
> **no two rows of this menu are the same hypothesis**, and the dial has a
> distinct detent at every odd mass. Axiom-free.
>
> ✅ **`SESSION 158`: and no row is secretly RH.** `144`'s lesson is that a
> hypothesis can be precise enough to look valuable and still empty what it would
> buy. The *top* row was checked at `108`/`116`
> (`noHaunted_strictly_weaker_than_RH`); the intermediate rows never were. They
> pass: `noSmallHaunted_admits_offline` shows every rung is satisfied by a
> configuration carrying `2j` off-line zeros, so **no rung forces `Noff = 0`**.
> Axiom-free. Every row of this menu is now a hypothesis that is strictly weaker
> than the previous one, strictly stronger than the next, and compatible with
> off-line mass.


## The ξ′ route's blocker has a citation (SESSION 115, from claude.ai)

`087` priced the ξ′ transfer at **+9.29 points** and blocked it on two
hypotheses. claude.ai supplies the literature for one of them:

* **`NzComparable`** — `N_{ξ'}(T) = N_ζ(T) + O(log T)`. **Conrey, "Zeros of
  derivatives of Riemann's ξ-function on the critical line," J. Number Theory 16
  (1983), 49–74**, which proves the counting for all `ξ^(m)`; ξ's zeros *are* ζ's
  nontrivial ones. For ζ-derivatives if ever needed instead: **Berndt, "The
  number of zeros for ζ^(k)(s)," J. London Math. Soc. (2) 2 (1970), 577–580**.
  **[RECALL, UNVERIFIED]** — neither paper has been read here; the citation is
  claude.ai's and is recorded as a pointer, not as a discharge.
* **`OffTransfer`** — still open; absorbing Levinson–Montgomery's `O(log T)` into
  `o(N)` needs Riemann–von Mangoldt, which the same shelf presumably supplies.

*Ruling for Joop, now with a concrete reference:* discharging `NzComparable`
means either extending the zeta-23 import or adding an axiom. `Assumptions.lean`
forbids raising the certified proportion by assumption, and this would do exactly
that (+9.29). My reading is that a **counting-function comparison is a different
kind of object from a proportion axiom** and might be admissible where a
proportion axiom is not — but that is a doctrine question and yours, not mine.

### The 4/7 audit: no free improvement

claude.ai flagged that Conrey 1983 gives `≥ 81.37%` of ξ′'s zeros on the critical
line, upgraded to `82.402%` by the `θ = 4/7` mollifier (arXiv:1206.3737), and
asked whether the repo's constant reflects the upgrade.

**It reflects neither, and is better than both.** `zeta23_xiPrime` asserts
`Proportion 0.85838` from zeta-23's `xiDeriv_simple_on_line` — and `Proportion`
is the **simple-and-on-line** count, a strictly stronger property than "on the
line". So the repo's constant exceeds `82.402%` on a stronger statement. No free
points; audit closed.

### Why the route pays, structurally

claude.ai's third pointer, recorded for the packaging: Farmer, *"Differentiation
evens out zero spacings"* (math/0310252), and Farmer–Gonek on the pair
correlation of ξ′'s zeros. Differentiation actively smooths the zero
distribution, so the ξ′ world is provably better behaved than ζ's — the
transfer's mechanism has a name and a literature. **[RECALL, UNVERIFIED]**.


## The haunted row, certified (SESSION 129)

`certified_haunted` — **`hauntedCount ≤ (0.16375 + o(1))·N`** for `ζ`, at the
same two axioms as every other row (`#print axioms`: `baseline_zeta23`,
`zetaNonempty`).

It is `certified_offline` halved: a haunted ordinate carries at least two
off-line zeros, so the off-line density row caps the haunted density at half its
value.

**And it is essentially attained.** `114`'s witness — `1000` simple atoms beside
`321` haunted mass-`3` atoms — has `hauntedCount = 321`, `N = 1963`, so a haunted
density of `321/1963 ≈ 0.16352`. The bound permits `321.44`. The slack is **less
than half a haunted ordinate**, which is the discretisation of `1000 : 321` and
not looseness in the argument.

**Why it matters for the price list.** Every conditional row in this project is
`Proportion (κ − δ)` for a bound `hauntedCount ≤ δ·N`. This is the certified
`δ`, and `111` proves nothing derived from the baseline alone can beat it. So the
price list now has its floor stated in the currency it trades in, rather than
only in the currency it reports.

*Not added to `tools/metric.json`: the ledger maximises over rows, and an upper
bound on a defect is not commensurate with a lower bound on simple zeros.*


## claude.ai's answers, wired in (SESSION 132)

**1. `OffTransfer` is Conrey 1983 too — the same paper.** Conrey, *J. Number
Theory* 16 (1983), 49–74 is the Riemann–von Mangoldt theorem **for `ξ^(m)`**: the
`N_m(T)` asymptotic with `O(log T)` error. So **both halves of the `+9.29` route
cite one 1983 paper**, and the cheapest nine points on the board are one
bibliography item. Berndt 1970 is needed only if the route ever switches to `ζ'`,
in which case Levinson–Montgomery 1974 (*Acta Math.* 133, 49–65) joins it.
**[RECALL, UNVERIFIED]** — unread here; a citation is a pointer, not a discharge.

*Ruling for Joop, unchanged in substance and sharper in cost:* discharging both
hypotheses is now **one paper**, and doing it by axiom would raise the certified
proportion by `+9.29`, which `Assumptions.lean` forbids.

**2. The genre exists, is two years old, and is active.** Conditioning
strictly-weaker-than-RH for simple-zero proportions is a current programme:
narrow box (BGST 2024, *Acta Arith.* 214 — a **horizontal-location** hypothesis);
pair correlation assumed without RH (Goldston–Suriajaya 2025/26, and GLSS
arXiv:2507.06823 for the AH variant — a **statistics** hypothesis); zero-density
type (Aryan, arXiv:1902.05473 — a **density** hypothesis). All
**[RECALL, UNVERIFIED]**.

**So the packaging headline is not "we invented a genre".** It is:

> the genre is young and its members are location-, statistics- and
> density-shaped; **`NoHaunted` is a member of a new kind — pure coincidence**,
> constraining neither where zeros are nor how they correlate, only that one
> exact-height pattern does not occur — and the genre's conclusions all factor
> through **one identity**, `ProportionStd κ + hauntedCount ≤ δ·N ⟹
> Proportion (κ − δ)`. The contribution is a **classification with a normal
> form**, not a new hypothesis.

**3. Coincidence has no literature, by oracle — and the convertible currency is
the distinct-zeros deficit.** `Fiber.two_mul_haunted_add_atomCount_le_N`: a
haunted ordinate contributes `≥ 2` to `N − N_d`, so a distinct-zeros proportion
`N_d ≥ c·N` gives `δ = (1−c)/2`.

**And the project already holds one.** `certified_atomCount` is
`N_d ≥ (0.6725 − o(1))·N` at the baseline tier, and it converts to
`δ = 0.16375` — `certified_haunted_via_distinctZeros`, the same number as the
off-line route. Two shelves, one price, and `111` caps both.

*Open check c.ai suggests, one cycle:* whether any **unconditional** distinct-zeros
proportion exists post-BGST. If none does, the repo's `δ = 0.16375` may be the
best haunting bound in existence — a packaging sentence, and one I will not write
until the search is done.

## Rung 0 — supplier 1 checked and exhausted (`SESSION 265`)

The open ruling asks how to pay for `ceiling_law256`: adopt `EnclOK` as a third
baseline-tier axiom, or obtain `cert_N256_blk_b128m.json`
(`sha256 cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`) and
redo its interval arithmetic. `claude.ai` proposed walking three suppliers before
touching the axiom. Supplier 1 — *the artifact may simply be published* — is now
checked and it fails.

* **At the pinned commit** (`3635e74`, vendored byte-identical at
  `vendor/zeta23`), the string occurs **once**, in a docstring in
  `Zeta23/PairCeiling/LawN256.lean`, citing the filename and its `sha256`. The
  file is not in the tree.
* **At upstream HEAD** (`github.com/anthropics/zeta-23-lean`), four plausible
  paths return `404` and the releases page carries no asset of that name.

**Scope of that check, stated so it is not over-read.** One commit, four guessed
paths, one releases page. `api.github.com` is outside this sandbox's allowlist,
so no exhaustive tree walk was possible and no claim of absence from the
repository is made — only that it is not where it would be if it were meant to
be re-verified by a reader.

So the live options are supplier 2 (price the regeneration from the paper's
stated parameters — one cycle, and the artifact would be ours hash-and-all) and
supplier 3 (ask the authors — Joop's call, and the request is small enough to be
a good first contact). Adopting `EnclOK` remains the option of last resort: the
base has gone `9 → 8 → 2` by discipline and it does not go back up for
convenience.

## Rung 0 — supplier 2 is blocked too, and the ask for supplier 3 is now small (`SESSION 266`)

Supplier 2 was *price regenerating the certificate from the paper's stated
parameters*. The header of `Zeta23/PairCeiling/LawN256.lean` states them
generously — `70`-digit interval arithmetic at scale `K = 2^140`, the form factor
`S(j) = (Σ_c w_c |Σ_i m_{c,i} e^{2πi j x_{c,i}/256}|²)/256`, weights `w_c ≥ 0`
summing to `1`, rational positions `x_{c,i} ∈ [0,256)`, marks `m_{c,i} ∈ {1,2}`
with `Σ_i m_{c,i} = 256`, `τ = 3/10^40`, `|D(1)| ≤ 82395317/10^8`, and `p₀` as an
exact rational.

**Kill condition, filed first:** *if the certificate's parameters are not
recoverable from the vendored source — if regeneration needs a number only the
missing file carries — then supplier 2 is blocked for the same reason as
supplier 1.* **It fired.** The header states the *shape* of the law; the law
itself — which weights, which positions, which marks — is in the JSON; a grep of
the vendored tree finds the filename and `sha256` in one docstring and no law.
Interval arithmetic wants its input, and that is the part that was not
published.

**But the table says how small the missing thing is**
(`forensics/lawN256_shape.py`, which checks this and fails if it stops being
true):

* `K = 2^140`, `256` enclosures, every interval exactly `1` ulp wide.
* For `j = 1 … 255`, `(lo_j, hi_j) = j·2^132 ± 1` — that is `S(j) = j/256` to one
  ulp, which is exactly what `RowCert.lean`'s `|256·S(j) − j| ≤ 3/10^40` already
  asserts. **Those 255 entries carry nothing the row certificate does not.**
* Only `j = 256` is off-pattern: it encloses `S(256) ≈ 211.432009142486`, the
  periodic value the row certificate is silent about.

**So the request to the authors is not "send us the certificate".** It is: *the
law behind `cert_N256_blk_b128m.json` — the weights, positions and marks.* That
is a small, citable, easily-granted object, and with it the enclosures are
recomputable here and `EnclOK` becomes a theorem rather than a third axiom.

Standing recommendation unchanged: adopt `EnclOK` last, not first. Supplier 3 is
now the live option and its ask has shrunk to one line.

## What it would cost to stop assuming what we already vendor (`SESSION 268`)

`267` found that `zeta23_xiPrime` is axiomatised while a sorry-free proof of the
same constant sits in the dependency. This prices the two candidate discharges.

**Kill condition, filed first:** *if their zero data cannot be assembled into a
`ZeroData` — a finite, reflection-symmetric multiset — without an additional
assumption of its own, then the axiom is not merely an unwritten bridge and I
report what the extra assumption is.* **It did not fire.** Everything the
construction needs exists in the vendored tree, sorry-free, and mirrors the ζ
bridge we already wrote in `Riemann/Zeta.lean`:

| what `ZeroData.ofMult` needs | ζ (we have it) | ξ′ (exists, unbuilt) |
|---|---|---|
| finite zero set | `Zeta23.zerosIn_finite` | `XiPrime.zerosIn_finite` |
| zero predicate | `IsNontrivialZero` | `IsXiDerivZero ρ := xiDeriv ρ = 0` |
| multiplicity | `zeroMult` | `xiDerivMult` |
| closed under `ρ ↦ 1 − ρ̄` | `zeta_reflect_zero` | `xiDeriv_reflect_eq_zero_iff` |
| multiplicity invariant | `zeta_mult_reflect` | `xiDerivMult_reflect` |

**The price is the build, and it is most of the dependency.**

| discharge | extra modules | extra lines |
|---|---|---|
| `zeta23_xiPrime` from `Zeta23.XiPrime.Final` | `247` | `82,256` |
| `baseline_zeta23` from `Zeta23.ThmD.Final` | `125` | `44,441` |

Neither area has ever been compiled here — the vendored `.lake` holds only what
our `17`-module closure needed, so `import Zeta23.XiPrime.Final` fails on a
missing `olean` rather than on any error.

**And `zeta23_xiPrime` is the wrong one to buy.** `RULING.md` already strikes ξ′
as dominated by the `m = 7` rung — fewer points *and* two more axioms. Paying
`82,256` lines of build to strengthen a struck row is a bad trade at any price.

**`baseline_zeta23` is the interesting one, and it carries a second cost that
went unpriced until now.** Their theorem states `2 − 1/c₁* = HD 1 = 3/2 − cot(1/√2)/√2` in
closed form; `ThmD/Final.lean` says in as many words that *"decimals are not
formalized; the constant is exact"*. Our axiom asserts the decimal `0.6725`. So discharging it needs
the build **and** a proof that `0.6725 ≤ 3/2 − cot(1/√2)/√2`.

In double precision that constant is `0.672500703679…`, so the decimal is a
**safe** rounding with slack `7.04 × 10⁻⁷` — the axiom is not asserting more than
their theorem gives. That is a floating-point check and not a proof; what it
establishes is the direction of the rounding, which is the thing that would have
been alarming the other way.

> **Re-check, `SESSION 297` (2026-08-17).** The recommendation below closes on
> *"one cycle to measure and has not been measured"*. **It was measured, in
> `281`**, and the numbers are in this file's own table further down: `ThmD.Final`
> is `18m12s` = `1092s` one-time, and `15.4s` per elaboration (`15.6`, `17.3`,
> `13.3`) against a `9.3s` baseline — about `+6s` recurring. `282` then added
> `ThmD.Mult`, the correct supplier, at `+2m18s`. `absence_queue` carried this
> obligation for sixteen cycles because the answer was filed at the table and not
> here; that is `S36`'s shape, and the fix is this paragraph's position.
>
> The recommendation's *substance* stands: the wall-clock is cheap, so the reason
> not to discharge is no longer cost. It is Joop's ruling, and it is open.

**Recommendation.** Neither discharge now. Of the two, the `44,441`-line one is
worth revisiting, and only if the build turns out cheap in wall-clock — which is
one cycle to measure and has not been measured.

## A route with a rate and no supplier: odd atoms at `3/2` (`SESSION 303`)

`302` proved `3·oddAtoms ≤ N + 2·N_sc`, so `oddAtoms ≥ c·N` buys
`Proportion ((3c − 1)/2)`. That is `proportion_of_oddAtoms`, and the rate is
`3/2` — one point of odd atoms for one and a half of `N_sc`.

**It does not move the board, and the check is recorded rather than assumed.**
`R25`'s composite — kept as an unnamed `example` in `Gaps.lean` — typechecks and
returns
`(3κ − 1)/2`, which at `κ = 0.6725` is `0.50875`, exactly
`certified_nsc_unconditional`. Since `NscStd ≤ oddAtoms`, every `NscStd` supply
is already an `oddAtoms` supply, so routing through `ProportionStd` reproduces
the row the project already has.

**What would move it:** an `oddAtoms ≥ c·N` with `c > κ` that does not factor
through `NscStd`. Nothing on disk supplies one. `249` studied the odd-atom class
as an LP constraint and got `2 − c` in a different currency; `247` showed such a
bound excludes `Gauge.pairOnly`. Neither is a supplier.

Cost if a supplier appeared: **zero axioms** — `proportion_of_oddAtoms` is
axiom-free and the composite adds nothing.

## `baseline_zeta23`'s numeric step is not blocked on numerics (`SESSION 274`)

`268` recorded a second cost for this axiom: `ThmD` proves the exact
`2 − 1/c₁* = 3/2 − cot(1/√2)/√2` while we assert the decimal `0.6725`, so the
discharge needs a certified bound on a transcendental value — and `267` measured
this overlay as carrying no interval arithmetic at all.

**It needs none.** At `x = 1/√2` two identities hold with no approximation:
`x² = 1/2`, and `x·√2 = 1`. The cosine series has only even powers, so
`cos x = Σ (−1)^k (1/2)^k/(2k)!` is **rational**; the sine series is
`x·S` with `S = Σ (−1)^k (1/2)^k/(2k+1)!` also rational; and

    cot(x)/√2 = cos x / (sin x · √2) = C / (x · S · √2) = C / S

because `x·√2 = 1`. **The `√2` cancels and the target is rational arithmetic.**

Verified in exact rationals:

| terms | `3/2 − C/S` | `≥ 0.6725` |
|---|---|---|
| 5 | `0.672500695044` | yes |
| 6 | `0.672500703713` | yes |
| 8 | `0.672500703679` | yes |

At `8` terms the alternating-series tails are `|cos| ≤ (1/2)^8/16! ≈ 1.9·10⁻¹⁶`
and `|sin| ≤ (1/2)^8/17! ≈ 1.1·10⁻¹⁷`, against a required margin of
`7.04·10⁻⁷` — nine orders of room. Five terms already suffice.

**So the classification changes.** This is not "interval arithmetic, their whole
method, we have none"; it is an alternating-series bound in `ℚ` at a point where
the irrationality cancels. What remains is Lean work of a known genre — Taylor
partial sums with alternating remainder — and not a capability the project
lacks. The `44,441`-line build for `ThmD` stands unchanged and is still the
larger cost.

*Stated as a paper computation in `ℚ`; the bound is **not formalised** here and
this entry does not claim a Lean proof of it.*

## The `cot(1/√2)` step: route confirmed, order computed (`SESSION 275`)

`274` reduced the bound to rational arithmetic. This prices the Lean side.

**Kill condition, filed first:** *if Mathlib cannot deliver an alternating-series
bound for `cos`/`sin` at a specific point without new infrastructure, the
rational reduction stays a paper result and I report the Lean cost separately.*
It did not fire. `Complex.exp_bound` is exactly that infrastructure and it is
general in the order:

    ‖exp x − Σ_{m<n} xᵐ/m!‖ ≤ ‖x‖ⁿ · (n+1)/(n!·n)      for ‖x‖ ≤ 1

and Mathlib's own `Complex.cos_bound` is nothing but its `range 4` instance.

**The shipped bounds are far too coarse, measured rather than assumed.**

| bound | value at `x = 1/√2` | factor too coarse |
|---|---|---|
| `cos_bound`: `‖x‖⁴·5/96` | `1.302·10⁻²` | `43,711×` |
| `sin_bound`: `‖x‖⁵/100` | `1.768·10⁻³` | `5,934×` |

The requirement is `2.979·10⁻⁷` per function: from `cot = C/S`, an error `e` in
each moves `cot` by about `e·(1+cot)/S`, and the margin on `cot` is
`9.952·10⁻⁷`.

**`Complex.exp_bound` at `n = 9` suffices** (`1.353·10⁻⁷`); `n = 10` gives
`9.473·10⁻⁹`, an order of margin, and is the sensible target.

So the Lean work is: instantiate `exp_bound` at `n = 10` for `±x·I`, assemble
`cos` and `sin` bounds the way `Complex.cos_bound` assembles its own, and finish
in `ℚ` — `274` showed the `√2` cancels, so nothing irrational survives to the
arithmetic. **A page of Lean at a known pattern, not a new capability.**

*Route and order established by computation; no Lean proof of the bound exists
yet and this entry does not claim one.*

## The `cot(1/√2)` step, fully specified (`SESSION 277`)

`276` proved `cos_bound10`; `277` proves `sin_bound10`, its companion at the same
order and the same error. What is left is one rational inequality, and it is
written out here so the assembly is bookkeeping rather than discovery.

At `x = 1/√2` the two polynomials collapse to rationals, because `x² = 1/2`:

| quantity | exact value | decimal |
|---|---|---|
| `P` — the `cos` polynomial | `163483/215040` | `0.760244605655` |
| `R` — with `sin` polynomial `= x·R` | `5334193/5806080` | `0.918725370646` |
| `e` — the order-ten error, `|x|¹⁰·11/36288000` | `11/1161216000` | `9.473·10⁻⁹` |

The goal `0.6725 ≤ 3/2 − cot(x)/√2` is `cos x ≤ k·√2·sin x` with
`k = 3/2 − 0.6725 = 8275/10000`. Bounding `cos x ≤ P + e` and
`sin x ≥ x·R − e`, and using `√2·x = 1` so that `k·√2·(x·R − e) = k·(R − √2·e)`,
and finally `√2 ≤ 3/2` to keep everything rational, the whole thing reduces to

    882808211/1161216000  ≤  706247142277/928972800000

which holds with slack `191159/309657600000 ≈ 6.17·10⁻⁷`. **A `norm_num` call.**

So `baseline_zeta23`'s numeric step is: two theorems now on disk, plus one
rational comparison. The `44,441`-line `ThmD` build remains the real cost of that
axiom and is untouched by any of this.

*The two bounds are proved in Lean; the assembly above is arithmetic verified in
`ℚ` and is **not formalised** here.*

## Both builds measured, and `270`/`271`'s "standing tax" was wrong (`SESSION 281`)

`268` left `ThmD.Final`'s wall-clock unmeasured and `absence_queue` had been
carrying that as an obligation. Measured now, and measuring it exposed a
mistake in how both discharges were priced.

| | one-time build | recurring, per elaboration |
|---|---|---|
| `import Riemann` (today) | — | `9.3s` (3 runs: `9.7`, `9.3`, `8.8`) |
| `+ RvM.Statement + GammaFacts.Complete` | `7m32s` (`270`) | `9.0s` (`8.8`, `10.4`, `7.9`) |
| `+ ThmD.Final` | `18m12s` = `1092s` | `15.4s` (`15.6`, `17.3`, `13.3`) |

**`270` and `271` called the `zetaNonempty` import "a standing tax on every
`lake build`". That is wrong.** `lake` caches; the build happens once. The
recurring cost is olean loading, and for `RvM.Statement + GammaFacts.Complete`
it is **indistinguishable from the current baseline** — `9.0s` against `9.3s`,
with the samples overlapping.

`ThmD.Final` does cost about `+6s` per elaboration, which is real but is six
seconds, not eighteen minutes.

**What this does to the two rulings.** The `zetaNonempty` discharge costs one
build of seven and a half minutes and nothing measurable afterwards. The
`baseline_zeta23` discharge costs one build of eighteen minutes and about six
seconds per elaboration thereafter. Neither is a per-cycle tax in the sense the
escalation described, and the escalation should be re-read with these numbers.

*Wall-clock on this machine, three samples each; `ThmD` measured in two runs of
`570s` and `522s` because the tool budget is ten minutes.*
