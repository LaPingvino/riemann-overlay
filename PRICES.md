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
| `zeta23_xiPrime` `0.85838` | **9.29 points**, blocked on `OffTransfer` + `NzComparable` | **the one live item** (`087`) |
| `levinson_montgomery` | an input to that route | realised in `087`'s pricing |
| `baseline_przz` `0.4162` | **none — it is a theorem** (`przz_of_zeta23`) | **REDUNDANT, see below** |
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
