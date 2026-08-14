# STATEMENTS — the translation layer

Every formalized hypothesis, mapped to its source. Lean checks internal
consistency, not fidelity; this table is the part a human must audit.
Statements that formalized *easily* are marked ⚠ — per Doubt 5 they deserve
extra suspicion.

Toolchain: Lean `v4.24.0`, Mathlib tag `v4.24.0`
(`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`).
Note: zeta-23-lean is at `v4.33.0-rc2` — see ISSUES #4.

## Definitions (`Riemann/Basic.lean`)

| Lean | Meaning | Source | Convention chosen |
|---|---|---|---|
| `ZeroData.Z` | multiset of `(β, γ)` in a height window | GLSS §1 | **multiset with multiplicity**, i.e. a zero of order `m` appears `m` times. Chosen over `Σ ordᵨ` weights (the zeta-23 convention) — see ISSUES #5 |
| `ZeroData.refl_inv` | `Z.map (β,γ) ↦ (1-β,γ) = Z` | functional equation + conjugate symmetry | the *only* analytic input to §1. Not derived; assumed as a field |
| `ZeroData.H γ` | `#{ρ : γ_ρ = γ}` with multiplicity | GLSS, "horizontal multiplicity" | ⚠ literal reading of the definition |
| `ZeroData.Nstar` | `Σ_ρ H(γ_ρ)` | GLSS `N⊛(T)` | equals `#{(ρ,ρ') : γ = γ'}` = `Σ_{distinct γ} H(γ)²`. Diagonal pairs `ρ = ρ'` **included**, as in GLSS |
| `ZeroData.Nsc` | `#{ρ : β = 1/2 ∧ H(γ_ρ) = 1}` | GLSS `N_sc` | `H = 1` implies simple *and* on the line; that implication is `on_line_of_H_eq_one`, proved |
| `ZeroData.Noff` | `#{ρ : β ≠ 1/2}` | — | our own; used for the free zero-density corollary |
| `ZeroData.NscStd` | `#{ρ ∈ Z : β = 1/2 ∧ count ρ = 1}` | zeta-23 `N0simple`, GLSS `N_sc` | the **literature's** notion; `Nsc ≤ NscStd`, gap `≤ (N⊛−N)/2` |

## Proved, no axioms

| Lean | Statement | Source |
|---|---|---|
| `ZeroData.prop1` | `N_sc ≥ 2N - N⊛` | GLSS arXiv:2503.15449, Thm 2 (proof of) |
| `ZeroData.N_add_Noff_le_Nstar` | `N + N_off ≤ N⊛` | **new here** (elementary) |
| `ZeroData.N_le_Nstar` | `N ≤ N⊛` | trivial floor, GLSS "C ≥ 1" |
| `Counts.proportion_of_starBound` | `(★) with C` ⟹ proportion `2 - C` | GLSS §1 |
| `Counts.one_le_of_starBound` | any admissible `C` is `≥ 1` | consequence of the floor |
| `Family.offline_le` | `(★) with C` ⟹ `N_off ≤ (C-1+ε)N` | **new here** |
| `Cbound_lt_two`, `Cbound_lt_record`, `c0_lower_bound` | the numerical window for [OPEN 0] | **new here**, see below |
| `ZeroData.three_le_H_of_haunted` | a haunted ordinate has `H ≥ 3` | **new here** (the ghosts come in pairs) |
| `ZeroData.two_NscStd_le` | `2·NscStd ≤ 2·Nsc + (N⊛ − N)` | **new here**; the two-row bridge |
| `nsc_of_nscStd` | `(★) C` + `NscStd ≥ κN` ⟹ `Nsc ≥ (κ − (C−1)/2)N` | **new here**; beats Prop 1 for `C > 1.655` |

## Axioms (`Riemann/Assumptions.lean`) — the trusted base

Nine axioms, and **each speaks only about the fixed constants declared in that
file**. An axiom quantified over an arbitrary `Family` asserts a theorem about
`ζ` for adversarial toy models and is refutable — that mistake was made and
caught on 2026-08-13 (ISSUES #8). A consistency model for the whole base is
recorded in the `Assumptions.lean` header; extend it when adding an axiom.

| Lean | Source | Fidelity risk |
|---|---|---|
| `zetaFamily` | — | the interface to the real `ζ`. To discharge: build `ZeroData` from Mathlib `riemannZeta` + `analyticOrderAt` as in `zeta-23-lean/comparator/ChallengeDeps.lean`, plus `refl_inv` from the functional equation |
| `xiPrimeFamily` | — | ditto for `ξ'` |
| `closePairsZeta` | — | the functional `(2/λ)∫₀^λ 𝒩(α)dα`, declared not defined (needs `zetaFamily` first) |
| `fujii_ineffective` | Fujii, Trans. AMS 1974/1981; Gallagher–Mueller, Crelle 1978; assembled GLSS §5–6 | ⚠⚠ **highest risk**. The shape `Cbound c₀ λ` is our reading of GLSS (6.1)–(6.2), not a quoted theorem. See Doubt 1 / ISSUES #6 |
| `fujii_closePair_bookkeeping` | same identity, `𝒩`-term retained, **for the zeta family only** | ⚠ the `λ`-coupling is ours (ISSUES #3) |
| `zeta23_xiPrime` | zeta-23-lean, `Zeta23/XiPrime/Final.lean`, `xiDeriv_simple_on_line` | states the **proportion 0.85838** that the paper proves — nothing more. The `(★)` form for `ξ'` is *not* implied (Prop 1 bounds `N⊛` from below) and is carried as the hypothesis `UnconditionalFGL` (ISSUES #7) |
| `levinson_montgomery` | Levinson–Montgomery 1974 | off-line counts of `ζ` and `ξ'` agree to `O(log T)` |
| `baseline_przz` | Pratt–Robles–Zaharescu–Zeindler 2019 | 0.4162, **stated on `NscStd`** (ISSUES #13) |
| `baseline_zeta23` | zeta-23 Thm D | 0.6725, **stated on `NscStd`** = their `N0simple`, which is what they prove. Transfer to `Nsc` is `nsc_of_nscStd`, cost `(C−1)/2` |

**Formerly axioms, now hypotheses** (ISSUES #8): `fujii_with_closePairs` →
`ClosePairBookkeeping`, `farmer_ki` → `FarmerKiTransfer`,
`narrowBox_starBound` → `BGSTNarrowBox`. All three are false over arbitrary
families; one of them proved `False`
(`audit/regression/Boom_2026-08-13.lean`, which must never compile again).

## Open problems — `Prop`s, never assumed (`Riemann/Gaps.lean`)

| Lean | Gap | Note |
|---|---|---|
| `EffectiveFujii K c₀` | [OPEN 0] | the whole of Route I is a numeric question about `c₀`; see §"the window" below |
| `ClosePairLowerBound` | [OPEN 0′] | carries the `λ` at which the pairs appear — the prose does not |
| `DensityNearLine F M` | [OPEN A′] | the deliverable of [OPEN A]; [OPEN A] itself is not stated (needs `H_t`) |
| `NarrowBox`, `NarrowBoxExc` | BGST hypothesis, and the version with an exceptional set | the mismatch is ISSUES #1 |
| `LevinsonMontgomery` | Levinson–Montgomery 1974 | stated, unused so far |
| `UnconditionalFGL` | [OPEN B], `(★)` form | the derivative-side *proportion* is closed by `zeta23_xiPrime`; the `(★)` form needs the pair-correlation input directly (ISSUES #7) |
| `ClosePairBookkeeping`, `FarmerKiTransfer`, `BGSTNarrowBox` | literature bridges | demoted from axioms — ISSUES #8 |
| `LambdaUniformFarmerKi` | **[OPEN B″]** (Errata 1 E3) | replaces the retired [OPEN B]; composes (`routeII_via_B''`) |
| `NarrowBoxTolerant` | **[OPEN A″]** (Errata 1 E4) | sits *ahead* of [OPEN A′] on Route III; composes with a fitting condition (`routeIII_via_A''`) |
| `ExtendedSupport` | [OPEN D] | stated at the level of its consequence |

## The window for [OPEN 0] (new, proved in `Riemann/Fujii.lean`)

With `Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀·√log(2+λ)/λ`:

* `c0_lower_bound`: any admissible `c₀ ≥ 0.16`. (Otherwise `(★)` would assert
  `C < 1`, contradicting `N ≤ N⊛`. Evaluated at `λ = 0.462`.)
* `Cbound_lt_two`: `c₀ ≤ 0.8` ⟹ `C < 2` ⟹ a positive proportion. (`λ = 0.9`.)
* `Cbound_lt_record`: `c₀ ≤ 0.33` ⟹ `C < 1.3275` ⟹ beats 0.6725. (`λ = 0.61`.)

**E5 gate — materially cleared (2026-08-13, session 004 wildcard), pending a
30-second human eyeball.**

The gate no longer asks anyone to audit a Claude *reading*. The shape is a
**quotation of the paper's own displayed equation**, fetched from
`arxiv.org/html/2503.15449v4`:

> **(6.2)** `N⊛(T) + (2/λ)∫₀^λ 𝒩(α)dα = TL(λ + log(2+λ)/(π²λ) + O(√log(2+λ)/λ))`
>
> range: **(6.1)** *"imposing `0 < λ² ≤ L`"*; later *"For `0 < λ ≤ √L`"*
>
> **Proposition 2** `∫₀^T (Δ_U S(t))² dt = (T/π²)log(2+UL) + O(T√log(2+UL))`,
> for `0 < U ≤ 1`, and *"This result depends on an unconditional explicit
> formula of Selberg for `S(t)`."*

This matches `Riemann.Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀·√log(2+λ)/λ`
term for term, with `c₀` the implied constant of (6.2)'s error. The
`λ`-range is asymptotically permissive: every fixed `λ` used here
(`0.462, 0.61, 0.9`) satisfies `λ² ≤ L` for large `T`, and `U = λ/L → 0`
satisfies Fujii's `U ≤ 1`. `𝒩 ≥ 0` gives the inequality direction used.

**Human check now required, in full:** open 2503.15449v4, look at (6.2), and
confirm the four symbols. That is the whole task.

> *(unsigned — but see the independent derivation below, which is what a
> sceptic should attack instead)*

### Independent re-derivation (do not trust the fetch; check this instead)

Obtained here without reference to GLSS §6, from Riemann–von Mangoldt and
Fujii's Proposition 2 alone. If it agrees with (6.2), two independent routes
give the same shape.

Let `U > 0` and `D(t) := N(t+U) − N(t)`, the number of ordinates in `(t, t+U]`.

1. **Pair expansion.** `∫₀^T D(t)² dt = Σ_{γ,γ'} meas{t : γ, γ' ∈ (t,t+U]}
   = Σ_{|γ−γ'| < U} (U − |γ−γ'|) + O(edge)`.
2. **Diagonal.** The pairs with `γ = γ'` contribute `U` each, i.e. `U·N⊛(T)`
   — this is exactly where the horizontal multiplicity enters.
3. **Zero side.** `D(t) = UL + Δ_U S(t) + O(1/T)` (Riemann–von Mangoldt), so
   `∫₀^T D² = T U²L² + 2UL∫Δ_U S + ∫(Δ_U S)²`, and the cross term is lower
   order.
4. **Fujii.** `∫(Δ_U S)² = (T/π²)log(2+UL) + O(T√log(2+UL))` — unconditional.
5. **Normalise.** Divide by `U` and set `U = λ/L`:
   `N⊛(T) + (1/U)Σ_{0<|γ−γ'|<U}(U − |γ−γ'|)
    = TλL + (TL/π²λ)·log(2+λ) + O(TL·√log(2+λ)/λ)`,
   and the second left-hand term is `(2/λ)∫₀^λ 𝒩(α)dα`.

Step 5's right-hand side is `TL·(λ + log(2+λ)/(π²λ) + O(√log(2+λ)/λ))`, and
`TL ~ N(T)` by Riemann–von Mangoldt. **Agrees with (6.2).**

The one place a sceptic should press: step 3's cross term and the edge terms
of step 1 — both are `o` of the stated error for fixed `λ`, but neither is
proved here.

Exact optima with true logarithms (computed outside Lean, not certified):
`c₀ < 0.8550` and `c₀ < 0.3476`; forced lower bound `c₀ ≥ 0.1657`. The Lean
numbers are the weaker ones that survive the provable bound
`log(2+λ) ≤ log 2 + λ/2`.


## The Montgomery–Taylor identification (Addendum 4, L9) — verified numerically

**Claim.** zeta-23's constant `3/2 − (1/√2)cot(1/√2)` is the Montgomery–Taylor
1974 extremal value, with minimiser `ψ(x) = cos(√2 x)` on `[−1/2, 1/2]`.

**Check** (`λ = 1`, midpoint quadrature, N = 4000, error ≈ 2·10⁻⁸):

| quantity | value |
|---|---|
| `1/c` from `(∫ψ)² / (∫ψ² + ∬\|s−s′\|ψψ′)` | 1.3274992772 |
| `1/2 + ϑ·cot ϑ`, `ϑ = 1/√2` | 1.3274992963 |
| `2 − 1/c` | 0.6725007228 |
| `3/2 − ϑ·cot ϑ` | 0.6725007037 |
| `c` vs zeta-23's `c₁* = √2·tanϑ/(1+ϑ·tanϑ)` | 0.7532960787 vs 0.7532960679 |

**Verdict: the identification holds.** Addendum 4's consequence #1 stands —
the constant is not container-noise; the same extremal problem is being solved
in all three regimes. Note *why* `ϑ = 1/√2` appears: the minimiser is
`cos(√2 x)` and the window half-width is `1/2`, so the edge phase is
`√2 · 1/2 = 1/√2`. The constant is a statement about the **support**, which is
why the bandwidth-one ceiling below is its natural companion.

### The bandwidth-one crumb ladder (provenance, dispatch of 2026-08-13)

| value | source | note |
|---|---|---|
| 2/3 = 0.6667 | Montgomery 1973 [Mon73] | |
| **0.6725007** | **Montgomery–Taylor 1974 [Mon74]** | our numeric identification; also the *window optimum* at `λ=1` (ISSUES #12) |
| 0.672753 | Cheer–Goldston 1993 | combinatorial refinement of M–T |
| **0.679** | **Chirre–Gonçalves–de Laat [CGdL20]** | Montgomery's method, optimized test function — **L9's donor** |
| 0.6818287 | zeta-23 `PairCeiling.ceiling_law256` | proved ceiling for bandwidth-one certificates |
| 70.3704% | Conrey–Ghosh–Gonek 1998, **RH + GLH** | *above* the ceiling; different information channel (L11) |

Status: **numeric, not certified.** A Lean proof is not needed from scratch —
zeta-23 proves the corresponding statement in `Zeta23/ThmD/`; the identity to
record is that their `c₁*` equals the M–T extremal value. Reference to chase:
[Mon74] Montgomery, ICM Vancouver 1974, per BGST arXiv:2306.04799.
