# CLAIMS — every class-impossibility assertion, graded

This project's most valuable statements are of the form *"no member of class `C`
can do `X`"*. They are also the easiest kind to leave in a docstring, because
they feel settled once the argument is understood. Two were found living as
prose in three cycles (`FAILURES.md` `#10`'s rung 0, and `Gauge.lean`'s
LP-optimality), and both turned out to be true — so the risk was never that we
believed false things, but that a reader could not tell which beliefs they were
entitled to check.

This file is the inventory. **Anything cited as a bound must appear here with
grade A.**

## The three grades

* **A — certified.** A machine-checked statement quantified over the named
  class. Cite freely.
* **B — certifiable, but prose.** The class is well defined and a theorem could
  be stated; none exists yet. **This is the disease.** Cite only with the word
  "unformalised" attached.

  > ✅ **Grade B is empty — counted `SESSION 187`, and unchecked since `S22`
  > (session `044`) said so.** 89 rows at grade `A` (83 plain, 6 qualified), 6 at
  > `N` (computation or measurement), 1 at `C`, **0 at `B`**. The disease has not
  > recurred across ~140 cycles of additions.
* **C — class undefined.** The claim quantifies over something informal ("cheap
  invariants", "classical invariant"). Defining the class is the *prerequisite*
  for promotion — and per S23 that can be cheap, so C is **not** a life
  sentence. It is **not a bound** in the meantime; do not cite one as such.
* **N — class defined, evidence numerical.** The class is precise and the claim
  is checkable in principle, but what supports it is a computation, not a proof.
  Cite only with the word "numerically" attached. **Never as a bound.** A grade-N
  entry whose *code is not in the repo* is worse than unproved — it is
  unreproducible, and must say so.

## The inventory

| claim | class | certificate | grade |
|---|---|---|---|
| `μ_T` cannot see `β`; `NscStd` is not an ordinate functional | `μ_T`-invariant hypotheses (closed under deduction) | `Blindness.no_muInvariant_theory_computes_NscStd`, `NscStd_not_ordinate_functional` | **A** |
| `N⊛` is depth-blind; depth-shaped input has price zero | same | `Blindness.no_muInvariant_bundle_computes_Noff`, `Fiber.blind_at_every_crowded_mass` | **A** |
| Vertical blurring cannot separate a zero from its twin (A2) | smoothing at any radius `r ≥ 0` | `Blindness.two_le_Hr_of_off_line`, `Basic.on_line_of_Hr_eq_one` | **A** |
| The blindness is supported exactly on crowded atoms; mass one is sighted | same | `Fiber.Noff_eq_zero_of_simple` + `blind_at_every_crowded_mass` | **A** |
| No functional of `μ_T` discriminates the fiber coordinate; the Landau weight does | functionals factoring through `μ_T` | `Fiber.not_discriminates_of_factors`, `landau_discriminates` | **A** |
| `NscStd` reads the **on-line counts** and nothing else; `Nsc` reads the total mass | pointwise, over all `ZeroData` | `Fiber.NscStd_eq_onAt_functional`, `Nsc_reads_total`, `H_eq_onAt_add_offAt` | **A** |
| **`(μ_T, offAt)` determines the *entire ledger*** — `N`, `N⊛`, `Nsc`, `NscStd`, `N_off`. **Sufficient, not minimal** | all `ZeroData`, global | `Fiber.ledger_determined`; non-minimality by `Fiber.offAt_not_minimal` | **A** |
| **The profile determines the ledger** — all five quantities are functionals of the multiset of `(mass, off-line mass)` pairs, heights discarded. *Sufficient; minimality not claimed* | all `ZeroData` | `Fiber.N_from_profile`, `Nstar_from_profile`, `Nsc_from_profile`, `NscStd_from_profile`, `Noff_from_profile` | **A** |
| **…and at every proportion level below `1`** — for any rational `p/q < 1`, any goodness predicate accepting the simple atom, and any `B`, a configuration with at least `p/q` of its zeros good and `N⊛ > B·N` | every level `< 1`; the level `1` case is excluded and is RH-simplicity itself | `Fiber.no_starBound_from_goodness_at_any_level` | **A** |
| **No goodness proportion of ANY kind bounds `N⊛`** — for any predicate on atoms accepting the simple on-line atom, a configuration exists with ≥ 3/4 of zeros at good atoms and `N⊛ > B·N` | every local goodness predicate `good` with `good (1,0)` | `Fiber.no_starBound_from_goodness`, `lowMult_eq_goodCount` | **A** |
| **No low-multiplicity proportion bounds `N⊛`, at any threshold** — for every `k ≥ 1` and every `B` there is a configuration with three quarters of its zeros at simple ordinates and `N⊛ > B·N` | every threshold `k ≥ 1`; strictly generalises the `k = 1` case | `Fiber.no_starBound_from_lowMult` | **A** |
| **Selberg's `S(t)` normalisation measured (MIDPOINT sampling — see the caveat): mean `0.0000`, variance `0.443 → 0.496` rising across four height bands** — pre-registered as mean ≈ 0, variance below 1 and rising; both hold. The `(1/2π²)` constant is **verified** from arXiv:2403.19803's displayed density | Odlyzko `zeros1`, `t ≤ 74 921`; `arg ζ` sharing `log|ζ|`'s variance remains `[RECALL]`. **⚠️ `SESSION 146`: these figures are a MIDPOINT statistic and must not be quoted against a moment theorem** — `143` found the time-average `∫S²/L = 0.179` against the midpoint `0.056`, differing by the sawtooth's own `E[d³]/12`; `forensics/w19_price.py` | `forensics/selberg_S.py` | **N** (computation) |
| **The small-gap constant rises toward GUE with height, at `3.0σ`** — `0.712 ± 0.016` at `t ~ 10⁴`, `0.885 ± 0.055` at `2.7×10¹¹`, `0.868 ± 0.054` at `1.4×10²⁰`; the last two are `0.2σ` apart and not resolved | Odlyzko `zeros1/3/4`; Poisson errors on the sub-`δ` counts | `forensics/gap_scaling.py` | **N** (computation) |
| **Every certified bound holds in the verified region, with no violations** — six rows checked against `100 000` real zeros; all ordinates distinct at nine decimals, so `atomCount = N` observed against a certified `≥ 0.6725·N` | `t ≤ 74 921`; the two `N_off`/`haunted` rows read `0` off the RH verification, not off the table | `forensics/calibration.py` | **N** (computation) |
| **The Landau weight is minimised on the critical line**: `landau x D ≥ N·x^(1/2)` for `x > 0`, so the excess is a non-negative measure of off-line mass, each pair contributing `2√x(cosh((β−½)log x) − 1)` | all `ZeroData`, all `x > 0` | `Fiber.landau_ge_N_mul_sqrt` | **A** |
| **The on-line heights approach each other by a cubic law** — `100 000` zeros to `t ≈ 74 921`: smallest normalised gap `0.0219`, count below `δ` flat in `δ³` to ~3% over a factor of 8, at `0.71×` the GUE asymptotic constant | Odlyzko `zeros1`; resolution floor `1e-9`; says nothing about off-line zeros | `forensics/near_haunting.py` | **N** (computation) |
| **Crowding without haunting occurs in real arithmetic** — `y² = x⁵+2x` over `F₇` has `P(T) = (1+7T²)²`, a doubled Frobenius eigenvalue where Weil puts every root on the line; `12` of `195` genus-2 curves examined | genus-2 hyperelliptic over `F_5,7,11`; exact integer arithmetic | `forensics/function_field.py`, hand-verified witness | **N** (computation, not a Lean theorem) |
| **The distinct-zeros deficit is the convertible currency, at rate `1/2`** — `2·hauntedCount + atomCount ≤ N`, so `N_d ≥ c·N` gives `δ = (1−c)/2`; the project's own `N_d ≥ 0.6725·N` reproduces `δ = 0.16375` exactly | all families; ζ instance at baseline tier | `Fiber.two_mul_haunted_add_atomCount_le_N`, `hauntedDensity_of_distinctZeros`, `certified_haunted_via_distinctZeros` | **A** |
| **Mean vertical multiplicity of `ζ`'s zeros is at most `≈ 1.487`** — a **corollary** of the odd-ordinate row below, via `Fiber.oddAtoms_le_atomCount`; `130` listed the two as independent and they are not | `zetaFamily`, baseline tier | `certified_atomCount`, `Fiber.oddAtoms_le_atomCount` | **A** |
| **`claims_gate`'s flags on `ISSUES.md` are 97.4% noise** — all 39 triaged (`173` five, `174` the remaining 34): 1 true positive, the rest rhetorical "exactly", historical records with citations, directives, dated corrections, and two claims mechanically verified this cycle | full-register triage, not a sample | `forensics/claims_gate.py`; `SESSION 173`/`174` | **N** (measurement) |
| **`claims_gate`'s flags on `PRICES.md` are 92% noise** — all 27 triaged at `371`: **2 true positives in 25 judgeable**, both stale mechanical counts over our own tree rather than wrong mathematics; 2 excluded as not judgeable from the registers (`R17`). The register had never been triaged, and `QUEUE (1)` had been asking for `CLAIMS.md`, done at `076` and `342` | full-register triage, not a sample | `forensics/claims_gate.py`; `SESSION 371` | **N** (measurement) |
| **`session_gate`'s green is `13/16` earned and `3/16` unverified** — every roster entry has a reachable nonzero exit in source; `13` have been observed taking it (five drilled at `373`, eight red in the record). `forensics/surprises.py` survived two deliberate corruptions and is a tally, not a guard; `forensics/window_opt.py` reads no external input; `forensics/board.py` bare was not drilled | the sixteen roster entries, drilled or from the session record | `forensics/session_gate.py`; `SESSION 373`; `LOOP.md` banner row 26 | **N** (measurement) |
| **[`383`: BOTH NUMBERS WERE ALREADY ON DISK — `Gaps.starBound_delta_beats_baseline` (`304`) and `Gaps.starBound_exchange_crossover` (`191`). The row records a rediscovery.]** **The `Nsc` row's star route is priced at `793/400`** — *(`377`: this is a **second trade** in the currency `241` already priced; `Transfer.proportion_of_starBound` pays `2 − C` from the star bound alone. The two cross at `1393/1000`, both paying `607/1000`; `374`'s trade widens the currency's useful range from `C < 1193/800` to `C < 793/400`.)* — `ZeroData.six_mul_NscStd_le` (`275`) turns `N⊛ ≤ c·N` into `Nsc ≥ (κ − (c−1)/6)·N`, which beats the certified `(3κ−1)/2` exactly below `c = 4 − 3κ`; at `κ = 269/400` that is `793/400`, and the routes agree there at `407/800`, the value the row already carries. **A price, not a gain — no new proportion row** | every `κ` for the crossover; `ζ` at `269/400`; tight at the mass-`3` haunted atom | `Blindness.star_route_pointwise`, `star_route_beats_iff`, `star_route_threshold_zeta`, `star_route_attained`, `ZeroData.six_mul_NscStd_le` | **A** |
| **The star currency combines with the multiplicity ladder** — under `NoSmallHaunted m` a haunted ordinate costs `m(m−1)` into `N⊛ − N`, not the fixed `6`, so the star route beats the certified row below `1 + m(m−1)(1−κ)/2`: `793/400` at `m = 3`, `1710/400` at `5`, `3151/400` at `7`. **A combination, not a currency** — it needs both inputs and moves no row alone | all `ZeroData`, axiom-free; `κ = 269/400` for the numbers | `Riemann.hauntedDensity_of_starBound_at_rung` (family level, `383`), `Blindness.mass_card_le_Nstar_sub_N`, `haunted_rung_star`, `star_rung_threshold`, `star_rung_threshold_zeta` | **A** |
| **All three non-ladder haunted-density suppliers compose with the ladder** — off-line at `β/(m−1)`, star at `(C−1)/(m(m−1))`, distinct zeros at `(1−c)/(m−1)`. The star gains **quadratically** in the rung because a haunted ordinate's cost into `N⊛ − N` is quadratic in its mass while its cost into `N − atomCount` is linear | any `Family`, `2 ≤ m`; axiom-free | `Riemann.hauntedDensity_of_offLineImport_at_rung`, `Riemann.hauntedDensity_of_starBound_at_rung` (`383`), `Riemann.hauntedDensity_of_distinctZeros_at_rung` (`384`), `Blindness.haunted_rung_deficit` **Both coefficients are exact** (`385`): the mass-`m` haunted atom `configAt 0 1 j a`, `m = 1+2j`, makes each an equality | **A** |
| **The rung runs at every moment order, and one atom saturates all of them** — a haunted ordinate of mass `m` costs `m^k − m` into `momentK k − N`, and `configAt 0 1 j a` (`m = 1+2j`) makes each an equality for every `k ≥ 1`. So the multiplicity moments are **one currency wearing `k` hats**; a higher moment bound buys nothing the second did not price | all `ZeroData`, `1 ≤ k`; axiom-free | `Blindness.mass_card_le_momentK_sub_N`, `haunted_rung_momentK`, `rung_momentK_attained`, `pow_sub_self_mono` | **A** |
| **The rung's charge is exact at mass `m` and strict above it** (`k = 2`) — `c + m(m−1) = c·c` iff `c = m`, so `rung_coefficients_attained`'s atom is the unique tight mass, not one of several. **The general `k` is open**: it needs a strict form of `Blindness.pow_sub_self_mono` | `1 ≤ m ≤ c`; axiom-free | `Blindness.mass_cost_eq_iff` | **A** |
| **The on-line family cannot bound haunting at all** — a haunted ordinate has `onAt = 1`, exactly what a simple zero has, so `configAt 0 1 0 a` and `configAt 0 1 1 a` agree on every `onMoment` and on `NscStd` while `hauntedCount` is `0` against `1`. No `hauntedCount ≤ δ·N` follows from on-line data at any order | all `ZeroData`; the pair needs `a ≠ 1/2` | `Blindness.hauntedCount_not_determined_by_on_moments` | **A** |
| **The blindness apparatus is closed for the haunted bound** — five internal channels, all shut: multiplicity moments (one atom saturates every order), the on-line family (blind), the off-line coordinate (already spent), odd atoms (circular — `oddAtoms ≥ NscStd ≥ 269/400·N` forces any upper bound above the `δ = 131/800` in use), factorial moments (a `ℤ`-linear combination of the first) | all `ZeroData`; axiom-free | `Blindness.hauntedCount_le_oddAtoms`, `oddAtoms_bound_cannot_beat_baseline`, `factMoment_atom`, `rung_momentK_attained`, `hauntedCount_not_determined_by_on_moments` | **A** |
| **Route II lands `0.60169` from the inputs the source actually proves** — `ProportionStd 0.85838` (Remark 7.1's count) plus `NoHaunted F'`, the gap `283` named, with an **empty axiom cone**. **`ISSUES #7` is not closed**: `NoHaunted` for `ξ′` is unsupplied and nothing here asserts it | any `Family` `F'`; axiom-free | `Riemann.certified_nsc_via_derivative_std`, `Gaps.proportion_of_noHaunted` | **A** |
| **Two of the six declared axioms were consumed by nothing** — `levinson_montgomery` (a blocker that expired at `337`, bridged at `392`) and `fujii_ineffective` (strictly weaker than any consumer: they need `c₀ ≤ 0.33`, it gives existence with no bound, and the missing end **is `[OPEN 0]`**). The other four are load-bearing | the six axioms in `Riemann/Assumptions.lean`, consumers counted in Lean code outside that file | `Riemann.offTransfer_of_levinsonMontgomery`, `Riemann.fujii_ineffective_bracketed`, `Fujii.c0_lower_bound` | **N** (measurement) |
| **`LogSmall zetaFamily` is unconditional** — `log T = o(N(T))` for the zeta family, **axiom-free**, from the vendored Riemann–von Mangoldt main term `337` imported. With `levinson_montgomery` it gives `OffTransfer zetaFamily xiPrimeFamily`, a hypothesis on Route II's row — **not spent**: the discharge costs that axiom and the trade is Joop's | `zetaFamily`; the `OffTransfer` step also needs `xiPrimeFamily` | `Riemann.logSmall_of_rvm_main`, `logSmall_zeta`, `offTransfer_zeta_xiPrime` | **A** |
| **Proximity to the critical line places no bound on the off-line count** — for every `ε > 0` a configuration exists with all zeros within `ε` of the line and `Noff = N`, so `NarrowBox` supplies no `OffLineImport` | any `ZeroData`; axiom-free | `Blindness.offLine_count_not_bounded_by_proximity` | **A** |
| **The extremal configuration scales completely: ALL SIX route bounds are equalities at every `n`** — the chain of `n` haunted mass-`3` atoms has `N = 3n, N⊛ = 9n, Nsc = 0, NscStd = n, Noff = 2n, haunted = n, atomCount = n` | any `Family`; axiom-free | `Blindness.haunted_chain_attains`, `Blindness.haunted_chain_attains_star_and_atoms` | **A** |
| **The extremal configuration scales: four of the six route bounds are equalities at every `n`** — the chain of `n` haunted mass-`3` atoms has `N = 3n, NscStd = n, Nsc = 0, Noff = 2n, haunted = n`, so no route bound improves asymptotically. The `N⊛` and `atomCount` bounds are lifted only to `n = 1` | any `Family`; axiom-free | `Blindness.haunted_chain_attains` | **A** |
| **The exchange map is complete: one crossover, two identities** — enumerating every pair of exchanges consuming the same input, `ProportionStd` and `OffLineImport` each admit two routes that agree identically, `StarBound`'s two cross at `1.393`, and `atomCount` has one route | any `Family`; the identity is axiom-free | `proportionStd_exchange_identity`, `starBound_exchange_crossover` | **A** |
| **The two star-bound exchanges cross at `C = 1.393`** — direct (`2 − C`) is better below it, via-haunting (`κ − (C−1)/6`) above it; Route III's `C = 4/3` sits below, so its `2/3` is the right reading | any `Family`; the inequality is axiom-free | `starBound_exchange_crossover` | **A** |
| **The mass-`3` haunted atom is the minimal haunted configuration, and that is why it is extremal everywhere** — any `D` with `hauntedCount ≥ 1` has `N ≥ 3`, attained by `configAt 0 1 1 a`; every ledger bound mentioning `hauntedCount` is a per-haunted-ordinate cost, so each is tight where haunting is cheapest | any `ZeroData`; axiom-free | `Blindness.minimal_haunted_configuration`, `Blindness.minimal_haunted_attained` | **A** |
| **Both dictionary bounds `atomCount ≤ distinctZeros ≤ atomCount + Noff` are attained** — the lower by a single simple zero, the upper by the mass-`3` haunted atom (three distinct points: `3 = 1 + 2`), so the profile determines the literature's `N_d` to within exactly `Noff` and no better | any `ZeroData`; axiom-free | `Blindness.dictionary_bounds_attained` | **A** |
| **`distinctZeros` is not a profile functional** — two configurations with the same profile `{(4,4)}` and different distinct-zero counts, so `atomCount ≤ distinctZeros` cannot be strengthened to an identity and no profile-level argument bounds the literature's `N_d` | any `ZeroData`; axiom-free | `Blindness.distinctZeros_not_profile_functional` | **A** |
| **One configuration attains every route constant at once** — the haunted mass-`3` atom `configAt 0 1 1 a` has `N=3, N⊛=9, Nsc=0, NscStd=1, Noff=2, haunted=1, atomCount=1`, making all six route bounds equalities; so `176`'s `21/99` is a count dominated by plumbing | any `ZeroData`; axiom-free | `Blindness.mass_three_atom_attains_all` | **A** |
| **`StarBound M` is the optimal star bound derivable from `H ≤ M`** — a single ordinate of mass `M` gives `Nstar = M² = M·N`, so the multiplicity producer on the second channel has no slack | any `ZeroData`; axiom-free | `Blindness.Nstar_bound_attained`, `Blindness.Nstar_le_of_multiplicity_le` | **A** |
| **`β = 1 − κ` is the optimal off-line bound derivable from `ProportionStd κ`** — `Noff + NscStd ≤ N` gives it, and equality is attained by a single haunted mass-`3` atom, so no rearrangement of the same information improves it | any `ZeroData`; axiom-free | `Blindness.offLine_bound_attained`, `Blindness.Noff_add_NscStd_le_N` | **A** |
| **The literature's distinct-zeros bound does not feed our haunted route** — Wu (arXiv:1206.3737) proves `N_d ≥ 0.66036·N` for distinct *zeros*, but `atomCount` counts distinct *ordinates* and `atomCount ≤ N_d`, so the bound runs the wrong way; its constant is also below the baseline's `0.6725` | any `ZeroData`; the inequality is axiom-free | `Blindness.atomCount_le_distinctZeros`, `Blindness.distinctZeros` | **A** |
| **Route III is the cheapest row on the menu: `Nsc` at `2/3 − ε` (`+15.79` points) from a narrow-box hypothesis, cone `zetaNonempty` alone** — one axiom, against two for every multiplicity rung and four for ξ′; **`337` discharged `zetaNonempty`, so this cone is empty and the count comparison is now against `0`, `0` and `2`** | `zetaFamily`, two location hypotheses | `conjectural_routeIII`, `Program.routeIII_with_narrowBox` | **A** (conditional; ledger unmoved) |
| **The off-line round trip strictly loses below `κ = 1`** — every `OffLineImport` in the development carries `β = 1 − κ` (four declarations, enumerated), and feeding that back returns `(3κ−1)/2 < κ`; `084`'s `0.50875` is the baseline having gone once around this loop | any `Family`; the inequality is axiom-free | `offline_roundtrip_loses`, `offline_roundtrip_eq_iff` | **A** |
| **No `NscAny` lower bound can improve the `NscStd` row through the off-line exchange, at any strength** — `NscStd ≥ NscAny − Noff` with `NscAny ≤ N` and the only available `Noff` bound being `1 − κ`, so the route ties at `κ = 1` and never exceeds | `zetaFamily` for the numbers; both inequalities axiom-free | `ZeroData.NscAny_le_NscStd_add_Noff`, `ZeroData.NscAny_le_N`, `certified_offline` | **A** |
| **The `61.7%` of arXiv:2306.04799 is dominated by the certified `NscStd` row** — their `simple` counts multiplicity-one zeros *anywhere* (`NscAny`), ours additionally demands `p.1 = 1/2`, and `NscStd ≤ NscAny`, so `0.6725` transfers to their quantity and exceeds their conditional `0.617` | `zetaFamily` for the transfer; the inequality is axiom-free | `ZeroData.NscStd_le_NscAny`, `certified_std` | **A** |
| **No rung of the haunted ladder forces `Noff = 0`** — every rung is satisfied by a configuration carrying `2j` off-line zeros, so no row of the menu is RH-in-window in disguise | any `Family`; axiom-free | `noSmallHaunted_admits_offline`, `configAt_noSmallHaunted` | **A** |
| **The haunted ladder is a STRICT chain** — at every rung there is a configuration clearing it and failing the next, so no two rows of `PRICES.md`'s menu are the same hypothesis | any `Family`; axiom-free | `noSmallHaunted_strict`, `Blindness.configAt_H`, `Blindness.configAt_offAt` | **A** |
| **The haunted ladder is a chain and `NoHaunted` is its limit** — `NoSmallHaunted (m+1) → NoSmallHaunted m`, and `NoHaunted ↔ ∀ m, NoSmallHaunted m`; so `PRICES.md`'s menu is a scale, not a list of incomparable asks | any `Family`; axiom-free | `NoSmallHaunted.mono`, `noHaunted_iff_forall_noSmallHaunted` | **A** |
| **The `m = 7` ladder rung is worth `+10.917` points at NO axiom cost, dominating the ξ′ route in both currencies** — `Proportion 0.6179166`, cone `baseline_zeta23, zetaNonempty` — **`337`: both are theorems; `340` measured the cone empty with `board.py --cones`**; ξ′ gives `+9.294` at four | `zetaFamily`, baseline tier, one combinatorial `Prop` | `certified_nsc_via_noSmallHaunted_seven`, `certified_nsc_ladder` | **A** (conditional; ledger deliberately unmoved) |
| **The `m = 5` ladder rung is worth `+8.188` points at NO axiom cost** — `Proportion 0.590625` for `zetaFamily`, conditional on `NoSmallHaunted zetaFamily 5`; cone is `baseline_zeta23, zetaNonempty`, the same two as the certified row — **`337`: both are theorems; `340` measured the cone empty with `board.py --cones`** | `zetaFamily`, baseline tier, one combinatorial `Prop` | `certified_nsc_via_noSmallHaunted` | **A** (conditional; ledger deliberately unmoved) |
| **Route II is worth `+9.294` points and now exists as a theorem, not arithmetic** — `Proportion 0.60169` for `zetaFamily`, conditional on `OffTransfer` and `NzComparable`; its cone is **four** axioms against the certified row's two | `zetaFamily`, `ξ'` baseline tier, two carried `Prop`s | `certified_nsc_via_xiPrime`, `offline_via_xiPrime` | **A** (conditional; ledger deliberately unmoved) |
| **At least `67.25%` as many odd-mass ordinates as zeros** — every standard-simple ordinate has odd mass | `zetaFamily`, baseline tier | `certified_oddAtoms`, `Fiber.haunted_odd` | **A** |
| **At most `16.375%` as many haunted ordinates as zeros** — the first certified bound on the quantity the whole arc identified as central; same two axioms as the other rows — **`337`: none, both discharged** | `zetaFamily`; `#print axioms` was `baseline_zeta23`, `zetaNonempty`, and is now empty | `certified_haunted`, `hauntedDensity_of_offLineImport`, `certified_offline` | **A** |
| **Counting bounds on `hauntedCount` is the wrong operation** — two more are one line each (`3·haunted ≤ N`, `haunted ≤ NscStd`), both strictly weaker; the sharp statement is that `δ = 0.16375` is the best the certified inputs support, capped by `111` | all `ZeroData` | `Fiber.best_delta_is_from_110`, `three_mul_haunted_le_N`, `haunted_le_NscStd` | **A** |
| **A fourth bound on the haunted count: `6·hauntedCount ≤ factMoment 3`** — sharp at mass `3`, ledger value nil since nothing bounds the third factorial moment and `moment_route_walled` says nothing can | all `ZeroData` | `Fiber.six_mul_haunted_le_factMoment_three` | **A** |
| **The `/6` bridge is the density instrument at `δ = (C−1)/6`** — the fifth and last instance, and the only one that consumes `(★)`; `6·hauntedCount + N ≤ N⊛` is `Basic.six_mul_NscStd_le` read through the identity | all families | `hauntedDensity_of_starBound`, `Fiber.six_mul_haunted_add_N_le_Nstar` | **A** |
| **The mass ladder is the density instrument at `δ = (1−κ)/(m−1)`** — `(m−1)·hauntedCount + NscStd ≤ N` generalises `110`'s bound (the `m = 3` case), so every conditional result in the arc is one theorem | all families, all `m ≥ 2` | `hauntedDensity_of_noSmallHaunted`, `Fiber.pred_mul_haunted_add_NscStd_le_N` | **A** |
| **The canonical conditional row: `hauntedCount ≤ δ·N` gives `Proportion (κ − δ)`** — immediate from the identity; `NoHaunted` is `δ = 0`, and `087`'s off-line route is `δ = β/2` | all families | `proportion_of_hauntedDensity`, `hauntedDensity_of_offLineImport`, `certified_nsc_via_haunted` | **A** |
| **`NoHaunted` is strictly weaker than RH-in-window** — `N_off = 0 ⟹ NoHaunted`, and the converse fails on a lone off-line pair; so the conditional row is keyed to a hypothesis strictly below RH restricted to the window | all `ZeroData`; witness `configAt 0 0 1 a` | `Fiber.noHaunted_strictly_weaker_than_RH`, `noHaunted_of_Noff_zero` | **A** |
| **`NoHaunted` is the only member of the LI chain that does not assume RH-in-window** — distinct ordinates force `N_off = 0` (off-line zeros share their partner's height), while a lone off-line pair is unhaunted with `N_off = 2` | all `ZeroData`; witness `configAt 0 0 1 a` | `Fiber.Noff_eq_zero_of_allDistinct`, `noHaunted_not_imp_Noff_zero`, `noHaunted_of_allDistinct` | **A** |
| **The pair-correlation corpus provably cannot contain `105`'s hypothesis** — a haunted mass-`3` ordinate and an on-line triple are the same `μ_T` atom, so any `μ_T`-invariant statement excludes both or neither | `μ_T`-invariant statements only; says nothing about literature reading finer objects | `Fiber.haunted_indistinguishable_from_triple`, `config_ordinates_eq` | **A** |
| **The cap is robust: its witness satisfies every derived certified fact** — `N_off/N ≈ 0.32705` sits inside `certified_offline`'s `0.3275`, and it saturates both `N_off + NscStd ≤ N` and `2·hauntedCount + NscStd ≤ N` | the `1000 : 321` witness | `Fiber.cap_witness_respects_derived` | **A** |
| **The cap holds at `Family` level, where `Proportion` is defined** — a family satisfying `ProportionStd 0.6725` and failing `Proportion 0.50944`, so no theorem of that implication shape holds with `κ ≥ 0.50944` | all families | `baseline_cap_witness`, `baseline_cap`, `constFamily` | **A** |
| **The certified `Nsc` row is within `0.00068` of the best possible from the baseline alone** — `1000` simple plus `321` haunted mass-`3` atoms give `NscStd/N ≈ 0.67295 ≥ 0.6725` and `Nsc/N ≈ 0.50942`, so no argument from `ProportionStd 0.6725` can certify above `0.50943` | `zetaFamily`-independent; a `ZeroData` witness | `Fiber.row_essentially_optimal` | **A** |
| **The canonical haunted bound: `2·hauntedCount + NscStd ≤ N`**, attained exactly on `104`'s extremal family — every route the registers have tried to the haunted count lands here, and with the identity it *is* `084` | all `ZeroData` | `Fiber.two_mul_haunted_add_NscStd_le_N`, `two_mul_haunted_add_NscStd_eq_iff` | **A** |
| **`NscStd = Nsc + hauntedCount`, an identity** — the gap between the literature's count and the project's is *exactly* the number of haunted ordinates; with `Nsc + 3·haunted ≤ N` it re-derives `084` | all `ZeroData` | `Fiber.NscStd_eq_Nsc_add_haunted`, `Nsc_add_three_mul_haunted_le_N`, `three_mul_NscStd_le_of_identity` | **A** |
| **`NoHaunted` *is* "the two simplicity notions agree"** — `Nsc = NscStd` iff no ordinate is haunted; the hypothesis of the project's strongest conditional row is exactly `ISSUES #13`'s distinction, stated as an equation | all `ZeroData` | `Fiber.Nsc_eq_NscStd_iff_noHaunted` | **A** |
| **The ladder's limit is attained, and `097` assumed more than it needed** — `NoHaunted` alone transfers the full `κ = 0.6725` row; `H ≤ 2` implies it and is strictly stronger (mass-`4` all-on-line witness), buying the star bound `C ≤ 1.3275` that hauntedness alone does not | all families | `proportion_of_noHaunted_zeta`, `Fiber.Nsc_eq_NscStd_of_noHaunted`, `noHaunted_of_mult_le_two`, `noHaunted_not_mult_le_two` | **A** (conditional) |
| **The ladder is sharp at odd rungs and slack at even ones** — haunted ordinates carry odd mass, so `NoSmallHaunted m` for even `m` is already `NoSmallHaunted (m+1)`; at odd `m ≥ 3` the constant `m` cannot be improved | odd `m ≥ 3` sharp; even `m` reads up | `Fiber.ladder_sharp_at_odd`, `noSmallHaunted_succ_of_even`, `haunted_odd` | **A** |
| **The ladder: `m·NscStd ≤ N + (m−1)·Nsc` when every haunted ordinate carries `≥ m` zeros** — giving `Proportion ((mκ−1)/(m−1))`, which increases to `κ`; at `m = 5`, `0.590625` | all families, all `m ≥ 2`; hypothesis carried not assumed | `Fiber.mul_NscStd_le_N_add_pred_mul_Nsc`, `proportion_of_noSmallHaunted`, `proportion_of_noHaunted_three` | **A** (conditional) |
| **The extremal family of the `Nsc` row's bound, characterised exactly** — `3·NscStd = N + 2·Nsc` iff every ordinate carries one zero, or three with exactly one on the line; nothing else | all `ZeroData` | `Fiber.three_mul_NscStd_eq_iff` | **A** |
| **One three-element configuration attains equality in seven certified inequalities at once** — the haunted mass-`3` atom saturates the `(3,2)` bridge, the `2:1` coupling, the `M = 3` multiplicity bound, `N_off + NscStd ≤ N`, `N_off + #odd ≤ N`, `NscStd ≤ #odd`, and the four-quantity bridge | `configAt 0 1 1 a` | `Fiber.haunted_atom_saturates` | **A** |
| **`NscStd` cannot substitute for `Nsc` in the multiplicity criterion at `M ≥ 3`** — a haunted mass-`3` atom has `N⊛ = 9 = 3·N`, leaving no room for a positive coefficient; so the criterion must use the weaker row | `M = 3`, any positive coefficient | `Fiber.no_NscStd_coefficient_at_three` | **A** |
| **`(★)` does not imply bounded multiplicity** — for every `m` a configuration with `N⊛ < 2·N` contains an atom of mass `m`; the criterion is sufficient, never necessary | all `m ≥ 1` | `Fiber.starBound_allows_any_multiplicity` | **A** |
| **The multiplicity criterion tolerates exceptions, at cost `E²`** — `N⊛ + (M−1)·Nsc ≤ M·N + E²` where `E` is the number of zeros at exceptional ordinates; so `(★)` survives an exceptional set of size `o(√N)` | all families, all `M ≥ 1`, any decidable exceptional set | `Fiber.Nstar_add_pred_mul_Nsc_le_except` | **A** |
| **The sharp multiplicity criterion: `C ≤ M − (M−1)·κ`, tight at `H = 1` and `H = M`** — `< 2` iff `κ > 1 − 1/(M−1)`, so the certified `κ = 0.50875` reaches `M = 3` | all families, all `M ≥ 1` | `starBound_of_mult_le`, `Fiber.Nstar_add_pred_mul_Nsc_le`, `starBound_of_mult_le_three` | **A** |
| **Under multiplicity `≤ 2`: `Nsc = NscStd`, `C = 2 − Nsc/N` exactly, hence `C ≤ 1.3275` and `Proportion 0.6725`** — below Route III's `4/3` threshold, and the literature's row transfers whole | `zetaFamily`, multiplicity hypothesis carried not assumed | `proportion_of_mult_le_two`, `starBound_of_mult_le_two_zeta`, `Fiber.Nstar_add_Nsc_eq_two_mul_N`, `Nsc_eq_NscStd_of_mult_le_two` | **A** (conditional) |
| **`(★)` follows from "no zero has multiplicity ≥ 3"** — the supremum plus the certified `Nsc` row gives `C ≤ 1 + M(1−κ)`, which is `1.9825 < 2` at `M = 2`; the first sufficient condition for `(★)` in the registers that does not assume the conclusion | `zetaFamily`, multiplicity hypothesis carried not assumed | `starBound_of_multiplicity_two`, `starBound_of_multiplicity_and_proportion`, `Fiber.Nstar_add_mul_Nsc_le` | **A** (conditional) |
| **A multiplicity supremum `M` gives a star bound at constant `M`** — usable by `prop1` only when `M ≤ 1`, i.e. when every zero is already simple; so `(★)`'s constant is not a supremum | all families | `starBound_of_multiplicity_le`, `Fiber.Nstar_le_of_multiplicity_le` | **A** |
| **No `ProportionStd` yields a star bound** — for every `B` there is a configuration with standard-simple proportion `3/4` and `N⊛ > B·N`: `3m` simple atoms beside one atom of mass `m` | all constants `κ < 1` | `Fiber.no_starBound_from_proportionStd` | **A** |
| **The literature's row also caps mean vertical multiplicity** — `ProportionStd κ` forces at least `κ·N` distinct ordinates, so mean multiplicity `≤ 1/κ`; at the baseline, `≤ 1.487` | all families | `atomCount_ge_of_proportionStd`, `Fiber.NscStd_le_atomCount` | **A** |
| **At most 32.75% of the zeros of `ζ` are off the critical line** — unconditional at the baseline's own axiom tier, no star bound; the standard-simple zeros are on the line and disjoint from the off-line ones | `zetaFamily`; axioms `baseline_zeta23` + `zetaNonempty`, count unchanged — **`337`: both discharged, so this row is unconditional** | `certified_offline`, `offLineImport_of_proportionStd`, `Fiber.Noff_add_NscStd_le_N` | **A** |
| **The `Nsc` row has two independent derivations agreeing exactly** — via `3·NscStd ≤ N + 2·Nsc`, and via the off-line row plus the exchange rate; both give `0.50875` | `zetaFamily` | `certified_nsc_unconditional`, `certified_nsc_via_offline` | **A** |
| **`baseline_przz` was redundant, and is now deleted (`233`)** — `ProportionStd` is monotone in its constant, so `0.4162` follows from `0.6725`; `#print axioms` confirms `przz_of_zeta23` consumes only `baseline_zeta23` | the two `ProportionStd` baselines | `Family.ProportionStd.mono`, `przz_of_zeta23` | **A** |
| **Every point of off-line control is worth half a point of the `Nsc` row** — `ProportionStd κ` plus `N_off ≤ (β+o(1))·N` gives `Proportion (κ − β/2)`; and the derivative family's `Proportion κ'` supplies `β = 1 − κ'` *given two named transfer hypotheses* | all families; the transfer hypotheses are **not** discharged | `proportion_of_offLineImport`, `offLineImport_of_derivative`, `Fiber.Nsc_add_Noff_le_N` | **A** (the conditional; the ζ instantiation is **not** claimed) |
| **The four-quantity bridge exists and collapses** — `2·A + #{odd atoms} ≤ N + 2·Nsc` is strictly finer, but `A, #{odd atoms} ≥ NscStd` recovers `(3,2)` exactly, so it moves the row only given a lower bound on the atom count | all `ZeroData` | `Fiber.two_mul_atomCount_add_oddAtoms_le`, `three_mul_NscStd_le_of_four` | **A** |
| **`(3, 2)` is the optimal constant pair** — any bridge `c·NscStd ≤ N + d·Nsc` valid on all `ZeroData` has `c ≤ 3`, and `c = 3` forces `d ≥ 2`; so `(3κ−1)/2` cannot be improved *by an inequality of this shape*. A bridge using further `μ_T`-visible data is not excluded | bridges in the triple `(NscStd, N, Nsc)` only | `Fiber.bridge_optimal`, `haunted_atom_counts`, `simple_atom_counts` | **A** |
| **`3·NscStd ≤ N + 2·Nsc`, unconditional and axiom-free** — a haunted atom has even nonzero off-line part, hence mass `≥ 3`, so it costs three zeros and yields one `NscStd`; transported, `ProportionStd κ ⟹ Proportion (3κ−1)/2` with no star bound | all `ZeroData`, all families | `Fiber.three_mul_NscStd_le_N_add_two_mul_Nsc`, `proportion_of_proportionStd`, `certified_nsc_unconditional` | **A** |
| **The two invisible rows are coupled, sharply** — `2·(NscStd − Nsc) ≤ N_off`, with equality on `n` atoms of mass `3`; every haunted zero costs at least two off-line zeros | all `ZeroData`; sharpness on the mass-`3` family | `Fiber.two_mul_NscStd_le_Noff_add_two_mul_Nsc`, `coupling_tight` | **A** |
| **The other invisible row is bracketed too** — `N_off` is even and `N_off + #{odd atoms} ≤ N`, both endpoints `μ_T` functionals, and every parity-admissible value is attained | all `ZeroData`; attainment on `n` atoms of mass `3` | `Fiber.Noff_even`, `Noff_add_oddAtoms_le_N`, `Noff_tight_chain` | **A** |
| **The bracket is attained at every value, at every width** — for all `t ≤ n`, `n` atoms of mass `3` realise `NscStd = t` with `Nsc = 0`, `#{odd atoms} = n`, and a `t`-independent `μ_T` | all `n`, all `t ≤ n` | `Fiber.bracket_tight_chain`, `chain_profile`, `profile_superpose_disjoint` | **A** |
| **The bracket is attained at every value** — on the two-atom mass-3 family both endpoints and the interior point are realised by configurations sharing one `μ_T` | two atoms of mass `3`; **not** proved for arbitrary `μ_T` | `Fiber.bracket_tight_two_atoms`, `oddAtoms_from_profile` | **A** |
| **The class computes an interval for `NscStd`, not a point** — `Nsc ≤ NscStd ≤ #{odd atoms}`, and both endpoints are functionals of `μ_T` alone | all `ZeroData` | `Fiber.NscStd_bracketed`, `NscStd_le_oddAtoms`, `bracket_muInvariant`, `Basic.Nsc_le_NscStd` | **A** |
| **The moment family adds nothing to `μ_T`'s reach** — every `momentK D k` is a functional of `D.ordinates` with the functional exhibited, so no function of the whole sequence computes `hauntedCount`, `oddAbove`, `evenOnAt`, `offLineOnly` or `NscStd`; and no single `k` determines `N_sc` | all `ZeroData` for the five negatives; the single-`k` separation is witnessed at every `k` by one mass-`2` atom against `2^k` simple ones | `Fiber.momentK_ordinate_functional`, `not_momentK_computable_of_not_ordinate_functional`, the five `_not_momentK_computable`, `single_momentK_not_determine_Nsc` | **A** |
| **A multiplicity cap does not bound `N_sc`, it computes it** — `2·N_sc + 5·N ≤ N⊛ + 6·atomCount` for every configuration, with equality **iff** every mass is at most `3`; and `9·N⊛ + 24·atomCount ≤ 6·N_sc + Σm³ + 26·N` with equality **iff** every mass is at most `4`. Composing the first with `334` makes the moment family's equality set exactly the set where three moments compute `N_sc` | all `ZeroData`; the caps at `3` and `4` only — no general-`m` statement | `Fiber.two_mul_Nsc_add_five_mul_N_le`, `two_mul_Nsc_eq_iff`, `momentK_charges_eq_iff_Nsc_computed`, `nine_mul_Nstar_add_atomCount_le`, `nine_mul_Nstar_add_atomCount_eq_iff` | **A** |
| **The distinct-zeros route is dominated at every input constant** — zeta-23's unconditional point-count proportions (`3/4`, and `GD 1 = 0.83625`) convert through the only dictionary on disk to at most `c − 0.3275` for `atomCount`, so `0.83625` gives `0.50875` and even `c = 1` only ties the `0.6725` already held | all `ZeroData`; the point-count proportion is a **hypothesis**, since no bridge from `distinctZeros` to `Zeta23.Ndist` is proved | `distinctZeros_route_dominated`, `distinctZeros_route_ties_at_one`, `Blindness.atomCount_of_distinctZeros_and_Noff`, `zeta23_GD_eq_of_HD` | **A** |
| **The point/ordinate gap is entirely off the line** — `onLineOrdinates` is also the count of distinct on-line *zeros* (`p ↦ p.2` is a bijection, since a zero on the line is `(1/2, γ)`), the point count partitions as `onLineOrdinates + offLinePoints`, and `distinctZeros + offLineOnly = atomCount + offLinePoints` exactly | all `ZeroData`, no hypotheses; the bridge to `Zeta23.N0star` is **not** proved and not assumed | `Fiber.onLineOrdinates_eq_onLinePoints`, `onLineOrdinates_add_offLinePoints`, `offLinePoints_le_Noff`, `point_slack_exact` | **A** |
| **Every board row has a threshold rung, and two of them are located** — a rung beats a target `c < κ` exactly when `m > (1−c)/(κ−c)`; rung `7` is the first to beat Route II's `0.60169` (rung `5` does not) and rung `59` the first to beat Route III's `2/3` (rung `57` does not), the thresholds being `39831/7081` and `400/7` | any `κ`, `c < κ`, `m > 1` for the law; the two crossings at `κ = 0.6725`, with the failing previous odd rung shipped alongside | `Gaps.ladder_beats_iff`, `ladder_beats_routeII_first_at_seven`, `ladder_routeII_crossing_exact`, `ladder_beats_routeIII_first_at_fiftynine`, `ladder_routeIII_crossing_exact` | **A** |
| **`N_sc` is a falling-product sum under a multiplicity cap at any bound** — `capWitness D b = (−1)^b · b! · N_sc` whenever every ordinate has mass at most `b + 1`, by Lagrange interpolation of the mass-one indicator on `{1, …, b+1}`; `336`'s two identities are `b = 2` and `b = 3` | all `ZeroData`, all `b`, under the cap; the **expansion into `momentK 0 … momentK b` is not proved** — the product form is what is stated | `Fiber.capWitness_eq`, `cap_pointwise`, `capWitness_from_profile`, `capWitness_needs_the_cap` (a mass-four atom breaks it at `b = 2`) | **A** |
| **Under a multiplicity cap the first `b+1` moments determine `N_sc`** — `(−1)^b · b! · N_sc = Σ_{k≤b} capCoeff b k · momentK k` when every mass is at most `b+1`, the coefficients given by a two-term recursion; and two capped configurations agreeing on those moments have equal `N_sc` | all `ZeroData`, all `b`, under the cap. **Uncapped: nothing** — the coefficients depend on `b` and no uniform combination is claimed. The `esymm` identification of `capCoeff` is not proved | `Fiber.capCoeff_prod`, `capWitness_eq_sum_moments` (hypothesis-free), `Nsc_from_moments`, `Nsc_determined_by_moments_of_cap` | **A** |
| **The whole moment sequence determines `N_sc`, with no cap hypothesis** — every `ZeroData` is capped by its own `N`, and `N` is the moment at `k = 1`, so `345`'s capped determinacy applies at `b = N`; with `335`'s single-moment negative this makes the family strictly stronger than any member | all `ZeroData`. **Not** a function on arbitrary sequences: the formula reads `D.N` off its input before choosing coefficients | `Optimal.Nsc_determined_by_all_moments`, `Nsc_from_moments_at_N`, `Optimal.H_le_N`, `Blindness.momentK_one`, `Blindness.single_momentK_not_determine_Nsc` | **A** |
| **The moment sequence does not determine `NscStd`, and the witness is `X`'s founding pair** — a haunted ordinate and a pure on-line triple have equal `momentK` at every `k`, with `NscStd` equal to `1` and `0`; their `N_sc` values agree, as `346` requires | the pair `configAt 0 1 1 a` against `configAt 0 3 0 a`, any `a ≠ 1/2`. Puts `335`'s `¬∃ F` negative and `346`'s positive into one currency | `Fiber.NscStd_not_determined_by_all_moments`, `Nsc_agrees_on_the_moment_blind_pair`, `haunted_indistinguishable_from_triple`, `momentK_eq_count_sum` | **A** |
| **Equal moment sequences force equal mass counts at every `j`** — Newton's recovery in this vocabulary, proved without naming the interpolation coefficients: any product of monic linear factors is a polynomial (existence, with vanishing carried inside the existential), such a product summed over the atoms is a `ℤ`-combination of moments, and the erased-node product isolates one mass with a nonzero constant | all `ZeroData`, all `j`, no cap needed (the cap is `D.N` via `346`). **Not** equal ordinates: heights are invisible to every count here | `Fiber.exists_poly_of_prod`, `sum_prod_eq_sum_moments`, `node_sum_eq`, `node_const_ne_zero`, `massCount_determined_of_cap`, `Optimal.massCount_determined_by_all_moments`, `Fiber.massCount_one` | **A** |
| **The on-line moments determine `NscStd`, with no hypothesis** — `348`'s machinery run on `onAt` instead of `H`: the moments of the on-line count pin every on-line count, and `NscStd` is the `onAt = 1` one. Not a route — `onAt` is not a `μ_T` functional — but the exact name of what the `H`-moments lack | all `ZeroData`; no cap and no assumption that the two `N`s agree, since the on-line moments do not determine `N` | `Optimal.NscStd_determined_by_on_moments`, `Fiber.onCount_determined_of_cap`, `on_node_sum_eq`, `NscStd_eq_onCount_one`, `sum_prod_eq_sum_weight_moments` | **A** |
| **Each moment family sees one ledger row and misses the other** — the `H`-family determines `N_sc` and not `NscStd` (`347`'s haunted-against-triple pair); the `onAt`-family determines `NscStd` and not `N_sc`, nor `N` (a haunted ordinate against a **simple** one, equal on-moments, `N_sc` `1` and `0`, `N` `1` and `3`) | the two pairs named, any `a ≠ 1/2`; both `NscStd` values agree on the second pair, as `349` requires | `Fiber.Nsc_not_determined_by_on_moments`, `NscStd_not_determined_by_all_moments`, `Optimal.NscStd_determined_by_on_moments`, `Optimal.Nsc_determined_by_all_moments`, `Fiber.onMoment_from_onProfile` | **A** |
| **The two moment families together determine every ledger row, and still not the profile** — `N` and `N⊛` are `H`-moments at `1` and `2`, `N_sc` is `346`, `NscStd` is `349`, and `N_off` closes by `N_off + Σ onAt = N`; but two two-atom configurations with profiles `{(3,2),(5,2)}` and `{(3,0),(5,4)}` share both marginals and differ in the joint | all `ZeroData` for the positive half; the negative half is that named pair, any `γ ≠ 0`, `a ≠ 1/2` | `Optimal.ledger_determined_by_both_moment_families`, `Fiber.profile_not_determined_by_both_families`, `Noff_add_onMoment_one`, `Noff_eq_sum_offAt` | **A** |
| **The profile's own two marginals lose `NscStd`; swapping off-line for on-line does not** — profiles `{(3,0),(5,2)}` and `{(3,2),(5,0)}` share masses `{3,5}` and off-line masses `{0,2}` paired the other way, giving `NscStd` `0` against `1`, while the other four rows agree on that pair. The reason: `NscStd` is a functional of the on-line marginal alone (`349`), and recovering the on-line count from mass and off needs the joint | that named pair for the negative, any `γ ≠ 0`, `a ≠ 1/2`; the four-row agreement is a fact about the witness, not a general claim | `Fiber.NscStd_not_determined_by_profile_marginals`, `marginal_pair_separates_only_NscStd`, contrast `Optimal.ledger_determined_by_both_moment_families` | **A** |
| **All three ways of marginalising the profile's coordinates, surveyed** — with `on = mass − off` there are three pairs to keep: `(mass, on)` determines all five rows (`351`), `(mass, off)` loses `NscStd` (`353`), `(on, off)` keeps `N`, `N_off`, `NscStd` and loses `N⊛` and `N_sc` (`354`). Each pairing loses the rows whose definition needs the discarded pairing | the positive halves hold for all `ZeroData`; each negative half is a named two-atom pair, any `γ ≠ 0`, `a ≠ 1/2` | `Fiber.ledger_partly_determined_by_on_off_marginals`, `Nstar_Nsc_not_determined_by_on_off_marginals`, `NscStd_from_on_marginal`, `Noff_from_on_marginal`, `N_from_on_marginals`, `profile_snd_le_fst` | **A** |
| **`NscStd` is insensitive to added off-line zeros and `N_sc` is not** — superposing a configuration with no on-line zeros leaves `NscStd` unchanged at **any** size, not merely `o(N)`; the same superposition takes `N_sc` from `1` to `0`, since a mass-one ordinate acquiring an off-line pair has `H = 3`. This is the formal shape of `arXiv:2608.13637` §1.4's *"insensitive to `o(N)` off-line zeros"*, and the count version is sharper than the proportion version | all `D`, all `E` with no on-line zeros, for the positive half; the witness is `configAt 0 1 0 a` superposed with `configAt 0 0 1 a`, which is `rfl`-equal to `configAt 0 1 1 a` | `Fiber.NscStd_insensitive_to_offLine`, `onAt_superpose`, `onAt_eq_zero_of_offLine`, `Nsc_sensitive_to_offLine`, `NscStd_insensitive_offLine_witness` | **A** |
| **Reaching the certified row does not constrain where the zeros are** — a constant family on one haunted ordinate among four simple ones satisfies `ProportionStd 0.6725` (`NscStd/N = 5/7`) while `2/7` of its zeros are off the line, a share that does not decay. This is the second clause of `arXiv:2608.13637` §1.4 — *"hold for Davenport–Heilbronn and Epstein zeta functions, for which the analogue of RH is false"* — in this vocabulary | that named chain and its constant family, any `a ≠ 1/2`; `ZeroData` does not model those `L`-functions, so this is the translated content and not the paper's statement | `Riemann.proportionStd_admits_positive_offline_density`, `constFamily_proportionStd`, `mixed_chain_counts` | **A** |
| **The `13/18` row is outside both currencies this project owns** — `arXiv:2608.13637` §7.3's `HL*`-conditional `liminf N₀ˢ/N ≥ 13/18 = 0.7222…` is above Route III's `2/3` and above the certified `0.6725`, below `[OPEN D]`'s `1 − ε`, and no ladder rung or off-line exchange output reaches it at any `m` or any `β` | all `m > 1` and all `β ≥ 0`; three-line consequences of `ladder_lt_kappa` and `currencies_saturate_at_kappa`, so the content is the comparison and not the difficulty. `HL*` is an open conjecture and is **not** adopted | `Riemann.HL_row_on_the_board`, `ladder_cannot_reach_HL_row`, `offLine_currency_cannot_reach_HL_row` | **A** |
| **The on-line moments determine `oddAtoms` as well as `NscStd`** — `349`'s capped `onCount` determinacy, taken uncapped at `B = max D.N D'.N`, plus a fiberwise partition of the ordinates by `onAt` keeping the odd fibres | all `D`, `D'` agreeing on every `onMoment`, no cap. **`onLineOrdinates` is not done** — the same argument with `n ≠ 0` would give it and this cycle did not write it | `Optimal.onCount_determined_by_on_moments`, `oddAtoms_determined_by_on_moments`, `Blindness.oddAtoms_eq_sum_onCount` | **A** |
| **The on-line moments determine the chain's four upper terms and stop below the fifth** — `NscStd` (`349`), `oddAtoms` (`365`), `onLineOrdinates` and `atomCount` (`366`, the last as `onMoment 0`); `N_sc` is separated by `350`'s pair, a simple atom against a haunted one with equal on-moments | all `D`, `D'` agreeing on every `onMoment`, no cap, for the four; the negative is `350`'s named pair | `Optimal.chain_upper_four_determined_by_on_moments`, `onLineOrdinates_determined_by_on_moments`, `Blindness.atomCount_eq_onMoment_zero`, `onLineOrdinates_eq_sum_onCount`, `Blindness.Nsc_not_determined_by_on_moments` | **A** |
| **The `H`-family's reach along the chain alternates** — `even_offAt` makes `H` and `onAt` share parity, so `oddAtoms` counts odd-**mass** ordinates and **both** families reach it. Along `N_sc ≤ NscStd ≤ oddAtoms ≤ onLineOrdinates ≤ atomCount` the `H`-moments have `N_sc`, miss `NscStd`, have `oddAtoms`, miss `onLineOrdinates`, have `atomCount` | the two positives for all `D`, `D'` agreeing on every `momentK`; the two negatives are named configuration pairs, any `a ≠ 1/2`. **Corrects `366`'s framing**, which said the split was a cut at the two reported rows | `Optimal.oddAtoms_determined_by_all_moments`, `Blindness.oddAtoms_eq_odd_H`, `oddAtoms_eq_sum_massCount`, `onLineOrdinates_not_determined_by_all_moments`, `NscStd_not_determined_by_all_moments` | **A** |
| **Each moment family's reach is exactly its own count family** — agreeing on every `momentK` is the same condition as agreeing on every `massCount`, and agreeing on every `onMoment` the same as agreeing on every `onCount`. Both directions, cap-free | two equivalences for all `D`, `D'`; the forward halves are `346` and `365`, the converses the weighted fiberwise sums with the cap discharged at `max D.N D'.N` via `H_le_N` | `Optimal.moment_blind_iff_massCount`, `Optimal.on_moment_blind_iff_onCount`, `Blindness.momentK_eq_sum_massCount`, `Blindness.onMoment_eq_sum_onCount` | **A** |
| **The ledger is a functional of five named scalars** — `momentK 1`, `momentK 2`, `massCount 1`, `onMoment 1`, `onCount 1`. Not two infinite families. **Sufficient, and minimal under inclusion** (`370`) — every one of the five is necessary, so no proper subset determines the ledger. **Not the smallest possible count, and that question is empty unrestricted** (`372`) — one number suffices, so minimality holds *within the five named scalars* and nowhere wider | all `ZeroData`, axiom-free; each row is one existing identity | `Blindness.ledger_determined_by_five_scalars`; necessity by `Blindness.onCount_one_cannot_be_dropped`, `momentK_one_cannot_be_dropped`, `momentK_two_cannot_be_dropped`, `massCount_one_cannot_be_dropped`, `Noff_not_determined_by_ledger` | **A** |
| **A minimality claim about a sufficient statistic is relative to a declared class** — unrestricted, one natural number carries the whole ledger, so "the fewest scalars" is empty until a class is named. Three classes are on the board with three answers: unrestricted collapses to one; the five named moment-and-count scalars are minimal under inclusion (`370`); ordinate-local statistics floor at the profile (`077`) | all `ZeroData`, axiom-free; `Nat.pair` nested four times | `Blindness.ledgerCode`, `Blindness.ledgerCode_eq_iff`; `Fiber.profile_minimal_among_local` | **A** |
| **[READ AT `356`] `arXiv:2608.13637` is the paper of the artifact this repo vendors** — its Lean repository is `github.com/anthropics/zeta-23-lean`; its count `N0simple` is our `NscStd` (`274`); its `2/3` is the indicator window and its `0.6725 = 2 − c_MT⁻¹` is the Montgomery–Taylor window, *"optimal among windows"*, both unconditional; its §1.4 states that the inputs *"are insensitive to `o(N)` off-line zeros and hold for Davenport–Heilbronn and Epstein zeta functions, for which the analogue of RH is false"* | §1, §1.4, the constant definitions and Appendix A were read; **the proof was not**. Nothing here is a claim about correctness | quotes recorded in `LEADS.md` and `PRICES.md`; no repo declaration asserts any of it | **N** (a reading of a source, not a repo claim) |
| ~~**[ABSTRACT ONLY, `355`] `arXiv:2608.13637` states `2/3` unconditional for zeros "simple and on the critical line, counted with multiplicity", and `0.6725`/`0.8362` under the Montgomery–Taylor window** — the same numerals as `Zeta23.ThmD.HD 1` and `GD 1`. Which of this project's counts the paper's quantity is, whether its Lean artifact is `zeta-23`, and whether it subsumes the vendored `ThmD` are all **unread** | an abstract fetched from `arxiv.org`, nothing more; `136`'s rule — this discharges "does the paper claim this" and not "is the claim correct" | none in this repo; the escalation is in `LEADS.md` | **N** (not a repo claim; recorded so no cycle quotes it as one) | — superseded by the row above~~ |
| **Both additive ledger rows are load-bearing** — `N` alone misses `N_off` and `N_off` alone misses `N`, so neither single row forces the injectivity of `profile_minimal_among_local` | single atoms of mass `2` and `4` | `Fiber.mass_only_not_sufficient`, `off_only_not_sufficient` | **A** |
| **The profile *is* minimal among ordinate-local statistics** — any per-atom coarsening `g` whose value-multiset determines `N` and `N_off` is injective on realisable atoms | all realisable atoms `(mass, off-line mass)` | `Fiber.profile_minimal_among_local`, `configAt_profile` | **A** |
| **The profile is *not* a minimal sufficient statistic for the ledger** — two realisable configurations have distinct profiles and identical `N`, `N⊛`, `Nsc`, `NscStd`, `N_off` | two-atom configurations, mass `4 + 2` | `Fiber.profile_not_minimal`, `twoAtom_profile` | **A** |
| **The invisible row's ambiguity sits only on odd atoms of mass `≥ 3`** — every state over an even mass contributes `0` to `NscStd`, and parity is `μ_T`-visible, so even atoms are `μ_T`-determined; odd atoms of mass `≥ 3` carry states that share ordinates and disagree | all `ZeroData`, all masses | `Fiber.config_NscStd`, `even_mass_NscStd_zero`, `odd_mass_NscStd_ambiguous`, `config_parity` | **A** |
| **The shadow's size is `⌊m/2⌋ + 1` per atom** — the class cannot distinguish that many configurations at an atom of mass `m`, faithfully indexed by `j` and separated by `N_off` | all `ZeroData`, all masses | `Fiber.gauge_orbit_size`, `fiber_states_share_ordinates`, `fiber_states_distinguished` | **A** |
| **The `ZeroData` axioms are not rigid** — they admit a configuration with every zero off the line, and one with none. **Tier 1** only; tier 2 (anti-rigidity among genuine analytic objects, i.e. D–H) stays `[RECALL]` | functional equation + counting | `Fiber.zeroData_not_rigid`, `zeroData_admits_both` | **A** |
| **The moment route is walled at *every* order** — both witnesses forcing `prop1`'s optimum have all factorial moments of order `≥ 3` equal to zero, so no moment constraint of any order can exclude them | all orders `k ≥ 3` | `Optimal.moment_route_walled`, `Blindness.factMoment_eq_zero_of_masses_le_two` | **A** |
| **The third moment cannot improve `prop1`** — `Σm³ ≥ 3N⊛ − 2N` for every configuration, so the three-moment LP's improvement term is never positive | all `ZeroData` | `Fiber.three_Nstar_le_thirdMoment_add_two_N` | **A** |
| **The ledger's five components split 3 : 2 by visibility** — `N`, `N⊛`, `Nsc` are `μ_T`-functionals; `NscStd`, `N_off` provably are not | all `ZeroData` | `Fiber.ledger_visibility_split` | **A** |
| **Every moment of the mass distribution is a functional of `μ_T`** — including the third moment `Σ m³` that `prop1` needs | all `ZeroData` | `Fiber.thirdMoment_determined`, `Fiber.moment_determined` | **A** |
| **No reweighting of a shift-average can reduce the worst-case error** — equal-mass weights admit equal worst cases, which is attained | any finite weight family under a uniform error bound | `Capacity.reweighting_worst_case`, `weighted_sum_le_mass_mul`, `equal_mass_equal_worst_case` | **A** |
| The ledger is invariant under any injective **relabelling of ordinates** — their names carry no information | all `ZeroData`, all injective `σ` | `Fiber.ledger_relabel_invariant` | **A** |
| The real Landau weight **cannot** recover `offAt` — it agrees on the swap pair at every `x` | functionals of `Σ_ρ x^β` alone | `Fiber.landau_cannot_determine_offAt` | **A** |
| `prop1` is optimal among linear bounds in `(N, N⊛)` | `LinearBound a b` | `Optimal.prop1_LP_optimal` | **A** |
| Extension past the known range is useless, and fatal if the multiplier dips negative | `{F pinned on A, F ≥ 0 off A}`, `A` measurable | `Capacity.no_gain_past_known_integral`, `unbounded_below_of_neg_outside_integral` | **A** |
| `offline_le`'s `(C−1)` cannot be improved to `(C−1)/2` | the inequality itself | `Gauge.offline_le_tight` (saturating witness) | **A** |
| Route I cannot do better than `c₀ ≈ 0.16` | any effective Fujii constant | `Fujii.c0_lower_bound` | **A** |
| The bandwidth-one ceiling is `≤ 0.6818287` | bandwidth-one certificates, **and `EnclOK`** | `Zeta23.PairCeiling.ceiling_law256` — imported, vendored at `231`, and **reachable** from `import Riemann` (`#check` verified `244`) | **A**, conditional — see the note below |
| "Multiplicity bounds cannot tighten `C`" (W7, precise part) | `BoundedMult M` — `H γ ≤ M`, pure counting, no Euler product | `Optimal.prop1_LP_optimal_cheap` | **A** |
| "No free classical invariant *of any kind* will tighten `C`" (W7, general) | *"classical invariant"* — still informal | — | **C** |
| "Post-1974 extremal technology cannot buy anything through the `v` slot" | the `v` slot of the rank–trace container at `λ = 1` — **well defined** | a quadrature optimisation (`N = 160` midpoint, `0.6725126` vs M–T's `0.6725007`), reproducible via `forensics/window_opt.py` | **N** |
| E20's plane: the cleavage is the one thing no single-natured instrument can certify | *"single-natured instrument"* — informal | — | **C**, and already marked statistically unsupported in `FAILURES.md` |

> **`SESSION 244` — two corrections to the bandwidth-one row above.**
>
> **Reachability.** The row read *"not reachable from `import Riemann`"* with a
> caveat parked for Joop. That was fixed long ago — the heartbeat's own
> `DISCHARGED` block records `PairCeiling` as imported and reachable — and
> `244` re-verified it: `#check @Zeta23.PairCeiling.ceiling_law256` resolves
> under `import Riemann`. `231` additionally vendored it, so the theorem now
> lives on our disk.
>
> **The hypothesis, which the row did not name.** `ceiling_law256` is
> conditional on `EnclOK LawN256.K S 0 LawN256.encl`, which `LawN256.lean` calls
> a *"DISPLAYED HYPOTHESIS downstream … verified outside Lean by interval
> arithmetic"* and which is discharged nowhere in zeta-23 (`232`). Its
> certificate, `cert_N256_blk_b128m.json`, is not in this repository. The row's
> grade **A** is correct — the theorem is machine-checked — but the ceiling it
> certifies is available to us only if that hypothesis is granted, which is the
> open ruling `232` raised.
>
> **`SESSION 245`: every grade-A citation in this file is now guarded.**
> All 96 distinct declarations cited by the 97 grade-A rows resolve; four
> of them — `Nsc_le_NscStd`, `mul_NscStd_le_N_add_pred_mul_Nsc`,
> `routeIII_with_narrowBox`, `ceiling_law256` — were outside
> `audit/Declarations.lean` and are now in it, so `ISSUES` `#17`'s
> guarantee covers this table rather than most of it.

## The sweep's verdict (night cycle 8)

**Kill condition, stated first:** *if the sweep finds no further uncertified
class-impossibility claims beyond the two already fixed, the "pattern" was two
coincidences and must not be generalised into doctrine.*

**It fired, in the informative direction.** Every Lean docstring's impossibility
claim is backed — `c0_lower_bound` and `offline_le_tight` are real theorems, not
prose, and I expected at least one of them not to be. **Grade B is now empty.**

The two remaining uncertified claims are **grade C, not grade B**: their classes
are informal, so they are not theorems-in-waiting but statements of a different
species. Promoting them would require *defining* "cheap invariant" and
"post-1974 technology" first, which is a research question rather than a
formalisation task.

**So the pattern does not generalise into doctrine.** What survives is narrower
and more useful: a standing inventory, and the rule that a claim cited as a
bound must be grade A. The disease was real, finite, and is now cured; what
remains is a category that could not be cured by formalisation **as the classes
then stood**.

> ⚠️ **Corrected one cycle later (S23), and the correction belongs here rather
> than sixty lines below.** "Never curable by formalisation" was wrong: W7's
> grade-C entry was promoted in a single cycle once its class was defined
> (`BoundedMult`, `Optimal.prop1_LP_optimal_cheap`). Grade C means *not yet
> defined*, not *undefinable*.


## Amendment (night cycle 9) — grade C is not a life sentence

`CLAIMS.md` asserted, one cycle ago, that promoting a grade-C claim "would
require *defining* the class first, which is a research question rather than a
formalisation task". **For W7 that took one cycle.**

Every constraint in the cheap family has the same shape — an upper bound on
horizontal multiplicity — and that shape is pure counting with no multiplicative
input. `BoundedMult M D := ∀ γ, D.H γ ≤ M` is the class, and
`Optimal.prop1_LP_optimal_cheap` proves that assuming *any* such bound
(`M ≥ 2`) leaves the two-moment optimum at `2 − C`. The binding configurations
have `H ≤ 2`, so the cheap invariants are satisfied by construction and cannot
bind — which is exactly what the autopsy said, now as a theorem.

**Scope, stated plainly:** this certifies the vacuity of *multiplicity bounds*
for *this* extremal problem. The wider claim — that no classical invariant of
any kind tightens `C` — quantifies over a class still undefined and stays C.

**Revised guidance:** grade C means *the class has not been defined yet*, not
*the class cannot be defined*. When a C entry's claims all share one shape, that
shape is usually the definition. Filed as `SURPRISES` S23.


## Amendment (night cycle 10) — a fourth grade, and an unreproducible table

**Kill condition, stated first:** *if "post-1974 extremal technology" collapses
into the bandwidth-one class already certified by `ceiling_law256`, the entry is
a duplicate of an existing grade-A row rather than a new class.* **It did not
fire.** The registers are explicit that the two are different: the `0.28pp` gap
up to the bandwidth-one ceiling "does not live in window shape; it must live in
the richer certificate class their ceiling theorem quantifies over". The `v`
slot is a strict subclass.

**So the class is definable — and the grading scheme was missing a bin.** The
claim's support is neither a proof (grade A) nor prose (B) nor an undefined
class (C). It is a **numerical optimisation**: `N = 160` midpoint quadrature
over windows at `λ = 1`, giving `0.6725126` against Montgomery–Taylor's
`3/2 − ϑ cot ϑ`. Hence grade **N**.

**Verified tonight:** `3/2 − (1/√2)cot(1/√2) = 0.6725007036794116`, matching the
register's `0.6725007` exactly. The quoted optimiser sits `1.19 × 10⁻⁵` above
it, consistent with the stated quadrature error — so the *identification* is
sound as a numerical statement.

**And the snag that matters more than the grade:** the optimisation's **code is
not in this repo.** `forensics/` holds `lemma1_guard.py`, `provenance_lint.py`,
`quarry.py`, `w16_price.py` and `surprises.py` — no window optimiser. The table
in `LEADS.md` and the `18.18pp` instrument claim in `E.md` rest on a computation
that a reader cannot re-run and that we cannot re-run either.

That is a **reproducibility defect, not a mathematical one**, and it is the
first found in this repo. It was filed as `ISSUES` #29 rather than repaired
that night — **and #29 has since been resolved: the specification was in
`LEADS.md` all along and `forensics/window_opt.py` reproduces every digit
(S27).** The reasoning below stands as stated at the time: reconstructing the variational problem from memory would produce a
script that computes *something*, and passing that off as the original
computation is exactly the failure mode this project exists to avoid.

## Quantitative audit (night cycle 11)

**Kill condition, stated first:** *if `#29` is the only unreproducible number,
the defect is isolated and the sweep says so rather than inflating it.*
**It fired for its stated scope** — `#29` is the sole *missing-computation*
defect. The sweep then found a different species, recorded below.

> ⚠️ **Stale as of `SESSION 120`, corrected here.** `#29` was resolved:
> `forensics/window_opt.py` reproduces the
> whole `λ`-sweep to seven digits. **The count of missing-computation defects is
> now zero**, not one. The audit's conclusion stands; its subject does not.

Every computed figure in the registers, traced:

| figure | provenance | status |
|---|---|---|
| `0.6818287` bandlimited ceiling | `Zeta23.PairCeiling.ceiling_law256` | Lean ✓ — **reachable from `import Riemann`**, re-verified `SESSION 121`. (Graded "unreachable from our root — parked" until then; W34a's discharge made it reachable and this cell was never updated.) |
| `0.6725007` Montgomery–Taylor | closed form `3/2 − (1/√2)cot(1/√2)` | verified exactly, night 10 ✓ |
| `5.035` row-opening threshold — ⚠️ **the row is no longer closed (SESSION 084); beating `0.50875` needs `C < 1.49125` (Prop 1) or `C < 1.9825` (the `/6` bridge)** | `1 + 6 × 0.6725`, and `Proportion.nsc_row_opens` carries `C < 5.035` | Lean ✓, arithmetic transparent |
| `2.345` (the `/2` route's threshold) | `1 + 2 × 0.6725` | exact ✓ |
| `19/27 = 0.703704` (CGG98) | exact rational | ✓ |
| `1.3275` (record-beating `Cbound`) | `Fujii.Cbound_lt_record` | Lean ✓ |
| `0.85838` (`ξ'` proportion) | axiom `zeta23_xiPrime`, declared | trusted base ✓ |
| `0.80869`, `0.809` | **retracted** (`ISSUES` #27), marked | ✓ |
| `7.995`, `9.532`, `3.667`, `1.4283`, `0.8126`, `10.824` | **retracted** (`ISSUES` #24/#25) | ✓ *but see the ordering defect* |
| `0.6725126` and the whole `λ`-sweep (all five rows) | `forensics/window_opt.py`, the register's own linear solve | **reproduced to seven digits, every row ✓** (was graded "code not in repo" until `SESSION 120`; `#29` was resolved ~90 cycles earlier and this grade was never updated) |
| `1.3208` (CMR), `0.679`/`0.6792` (CGdL) | literature | `[RECALL]`, and CMR is a lint node |

**The new defect: retraction ordering.** `PRICES.md` carried its retracted
`c`-table at lines 165–176 with the retraction banner at line 183 — *below* the
numbers. A reader scanning the tables would meet `c ≤ 7.995` before meeting the
sentence that voids it. No false statement was *found* in it — which is a
search result, not a property of the text, and `SESSION 149` downgraded the
original "nothing false was written" to what the triage actually witnessed. It
was **badly ordered**, which for a register meant to be quoted from carries a
comparable hazard by a different route — comparable, not identical: no false
quotation from it has been recorded, whereas a false sentence would be one. **Fixed this cycle:** a warning now sits immediately above the tables.

**Standing rule added:** a retraction must appear *above* the material it
retracts, not merely somewhere in the same file.


## Ordering sweep (night cycle 12)

**Kill condition, stated first:** *if `PRICES.md` was the only misordering, the
defect is isolated and the sweep says so rather than manufacturing more.*
**It did not fire — a second instance exists**, of the same species but a
different shape: not a retracted table, a **stale figure still stated as
current**.

`LEADS.md` said, at lines 72 and 125, that L9's payoff window is `+0.93pp`. The
correction — that `0.93pp` is the *total* gap to the ceiling, of which CGdL 2020
already took `0.65pp`, leaving **`0.28pp`** — lived at line 284 and in `E.md`,
i.e. **two hundred lines below the framing it corrects**. Both quoted figures
are arithmetically true; the *framing* was stale, and a reader looking for "what
is left to win" met the wrong number first. Fixed: the correction is now carried
up to both points of use.

**And the sweep found the pattern done right, which is worth naming as the
template.** `LEADS.md`'s W4 entry heads with *"RESURRECTED. The autopsy below
reached the wrong verdict; read the correction first"*, puts the correction
immediately under it, and keeps the superseded autopsy below, labelled
*"verdict superseded"*. That is the shape every correction in these registers
should take: **verdict in the heading, correction next, superseded material last
and marked.** `E.md`'s E20m does the same for the withdrawn statistics.

**Tally: two instances of the defect, both now fixed; one model example.** The
ordering rule stands, with W4 as its worked example.

## Triage of the gate's own flags (2026-08-15, first live measurement)

**Kill condition, stated first:** *if the true-positive rate is zero, the gate is
noise on live registers and its wordlist needs narrowing before the instrument
can be cited at all.* **It did not fire — the rate was 3/6.**

`claims_gate.py` flagged six sentences in this file. Triaged one by one:

| # | sentence | verdict |
|---|---|---|
| 1 | grade C "cannot be promoted without first defining the class" | **true** — the residue of the claim `S23` falsified; W7's C entry was promoted in one cycle |
| 2 | "Never cite as one." | false — a directive, not a claim |
| 3 | "**Never as a bound.**" | false — same |
| 4 | "a category that was **never curable by formalisation**" | **true** — falsified by `S23` outright |
| 5 | "grade C means not yet defined, **not** *that the class cannot be defined*" | false — the trigger sits inside a phrase being denied |
| 6 | "filed as `ISSUES` #29 rather than repaired tonight" | **true** — stale; #29 has since been resolved (`S27`) |

**All three true positives were stale text whose correction already existed
elsewhere in the file.** The gate rediscovered ordering violations from a
completely different direction than the ordering sweep did — a wordlist scan and
a retraction audit converging on the same defect is the closest thing to
independent confirmation this project has produced about its own prose.

All three are now fixed **at their locations**, and `CLAIMS.md` reports **zero**
unwitnessed flags.

**And the three false positives were two mechanical shapes**, both now excluded
without touching the wordlist: *directives* ("Never cite as one") and *denied
quotations* ("not *that the class cannot be defined*"). The calibration cases
`S26` and `S27` are still caught after the narrowing.

**Remaining, and explicitly untriaged:** `LEADS.md` 25, `E.md` 10. Those counts
are a queue, not a defect rate — the same caution that applied before the
triage still applies to them.


## The identity detector (2026-08-15) — fourth error class, fourth instrument

**Purchased by exactly one failure**, per the house rule: `SURPRISES` S30, where
*"the `/6` census result and the third-moment obstruction are two readings of
one polynomial"* was false and quoted onward before it was checked.

`claims_gate` gains an `IDENTITY` wordlist — *"are the same"*, *"two readings of
one"*, *"turns out to be the"*, *"is exactly the"*, *"not a coincidence"* — on
the principle that **an identity claim is an exactness claim wearing the costume
of an insight**, and neither the lint (typed inputs), the gate's original
wordlist (exactness wording), nor the kernel (unstated claims) was checking for
it.

**Kill condition, stated first:** *if the patterns fire so broadly that the
true-positive rate is near zero, the class is not lintable and the finding is
that it needs a human check instead.* **It did not fire.**

* Calibration: both of S30's false sentences are caught; the corrected form
  passes.
* Live triage: `CLAIMS.md` `0 → 1` (that one a **false** positive —
  *"the same hazard by a different route"* is metaphorical, not an identity
  between objects); `S.md` 6, of which roughly **3 are true** (unwitnessed
  universal claims) and 3 false.
* **Rate ≈ 3/7**, comparable to the original gate's 3/6 at its first measurement.

> ⚠️ **Superseded by the SESSION 076 triage below, and the correction belongs
> here.** "Exempting definitional sentences is the next refinement" was the
> wrong next refinement. A full hand-triage of all seven `CLAIMS.md` flags found
> two *different* mechanical shapes, neither of them definitional sentences, and
> one of them a **false-negative** generator the flag count could not show.

**The false positives cluster on one shape: definitions and file premises.**
*"Absence is never certified as absence"* is `S.md`'s founding thesis, not a
claim owing a converse; the compression criterion is a definition and contains
`iff` by construction. **Exempting definitional sentences is the next
refinement — named, not built**, and deliberately left unbuilt this cycle so the
rate above is measured against the instrument as it actually stands.


---

## SESSION 076 — full hand-triage of the gate on `CLAIMS.md`

Seven sentences trigger, not six (the earlier note counted only the unwitnessed
ones). Every one graded by hand:

| # | trigger | verdict |
|---|---|---|
| 1 | `never` — "the risk was never that we believed false things" | **false** positive: scoped to the two cases named in the same sentence |
| 2 | `never` — quoting *"Never curable by formalisation"* to retract it | **false** positive: quoted retracted text |
| 3 | `exactly the` — the `#29` resolution note | **false** positive: the claim is true and `forensics/window_opt.py` reproduces it |
| 4 | `never`, `iff` — quoting `S.md`'s founding thesis | **false** positive: quoted material |
| 5 | `is the same` — *"the same hazard by a different route"* | **false** positive (as already graded above): a metaphor between hazards, not an identity between objects |
| 6 | `two readings of one` — quoting `S30` to retract it | **false** positive: quoted retracted text |
| 7 | the `IDENTITY` wordlist itself, quoted | **false** positive: vocabulary listing |

**True-positive rate on `CLAIMS.md`: 0/7.** Stated plainly, and it is *not*
evidence the gate is useless: `CLAIMS.md` is the register that has already been
triaged and cleaned twice, so a near-zero rate here is the expected reading of a
clean register. The gate's rate must be measured on the untriaged registers, and
that measurement has not been made.

**Two mechanical defects found, both fixed this cycle.**

1. **Filename false-witness — a false *negative* generator, and the more serious
   of the two.** `FAILURES.md`, `LEADS.md`, `S.md` and `Gauge.lean` all satisfied
   the `Namespace.lemma` witness pattern. **Three of the four passing sentences
   passed on a filename alone.** Any sentence mentioning a file was silently
   exempt. Fixed by excluding known extensions, and by admitting
   `forensics/*.py` explicitly — a script that reproduces the digits *is* a
   converse witness in this project.
2. **Quoted material.** Three of the seven flags triggered on text the sentence
   was quoting in order to retract it, or listing as vocabulary. Fixed by
   stripping italic-quoted, double-quoted and backtick-quoted spans before
   matching; a trigger surviving outside them is the author speaking.

**Measured effect, decomposed — and the decomposition is the point:**

| register | baseline | +quoted only | +filename only | both |
|---|---|---|---|---|
| `CLAIMS.md` | 3 | 1 | 5 | 2 |
| `LEADS.md` | 47 | 45 | 50 | 48 |
| `E.md` | 16 | 14 | 16 | 14 |
| `FAILURES.md` | 16 | 16 | 17 | 17 |
| **total** | **82** | **76** | **88** | **81** |

The two corrections are `−6` and `+6`, and the headline count moves by **one**.
Had this cycle reported only the aggregate, it would have read as "the gate is
unchanged" while both of its error modes had been repaired. No claim is made
that the cancellation means anything; it is two independent effects that
happened to be the same size.

**Still not done:** the untriaged flags on `LEADS.md` (48), `E.md` (14) and
`FAILURES.md` (17) remain untriaged and must not be quoted as a defect rate.


---

## SESSION 086 — the gate run on Lean docstrings, triaged

`claims_gate` had only ever patrolled the markdown registers. `S34`'s defect —
an unscoped enumeration in a load-bearing **docstring** — lived on a surface the
instrument had never seen. First run over `Riemann/*.lean`: 69 flags, of which
14 in the load-bearing files. All 14 hand-graded:

| file | flag | verdict |
|---|---|---|
| `Proportion` | "never its hoped-for constant" | false — design statement about the metric tool |
| `Proportion` | "they were simply not the only routes" | false — this is `084`'s own correction, in its corrected form |
| `Proportion` | "removes one axiom" | false — factual and checkable |
| `Program` | "the literature bridges that cannot be …" | false — descriptive |
| **`Program`** | **"This is the only arrow that survives"** | **TRUE — unscoped absolute, and the next two theorems in the same file are two more arrows** |
| `Program` | "the same pattern as ISSUES #3" | false — analogical, per the standing metaphor ruling |
| `Gaps` | "still a hypothesis, never an axiom" | false — accurate and structural |
| `Assumptions` | "an open problem must never be assumed" | false — directive |
| `Basic` | "the only analytic input is the reflection symmetry" | false — true, and witnessed by `ZeroData` having exactly two fields |
| `Basic` | "must never be compared as though they were the same" | false — directive |
| `Basic` | ×2 theorem statements | false — statements, not claims about the record |
| `Basic` | "the only form the accounting needs" | false — harmless |
| `Basic` | "every ordinate carries exactly one zero" | false — a definition |

**1 true positive in 14 — but it is the one being hunted.** The rate is low and
the yield is not: the gate's first exposure to docstrings found an unscoped
enumeration of exactly the class that produced `S34`, in a route-table file.

The kill condition — *if the gate on `.lean` files produces only false
positives, the instrument does not transfer and I say so* — **did not fire**.

**Standing change:** the load-bearing Lean files are now in the gate's beat.
`Fiber.lean` (36 flags) is almost entirely my own prose and is **untriaged**;
it must not be quoted as a defect rate.

> **`342`: that figure is a dated record and the number has tripled.** Measured
> this cycle: `Fiber.lean` **108**, `Gaps.lean` `32`, `Proportion.lean` `18`,
> `Optimal.lean` `13`, `Capacity.lean` and `Basic.lean` `9` each,
> `Blindness.lean` `5`, `Zeta.lean` `4`, `Program.lean` `3`, `Gauge.lean` `2`,
> `Fujii.lean` and `Assumptions.lean` `1` each, `Transfer.lean` `0` — `205` in
> all. The `Fiber.lean` growth is the decomposition arc `292`–`341`, which is
> my prose. Still untriaged in bulk, still not a defect rate; run the script for
> the live figure rather than trusting either number here (`328`).
>
> **Why that surface accumulates: it is the one nothing gates.** `session_gate`
> runs the overclaim gate on the newest `SESSION.md` entry, and its roster entry
> for `claims_gate` is CALIBRATION-only because a bare invocation lints stdin
> (`S123`). So every cycle's prose *entry* is gated and every cycle's Lean
> *docstrings* are not.
>
> **`343`: now they are, by a floor rather than a triage.**
> `forensics/overclaim_floor.py` records the count **per file** and fails if any
> rises — `warning_floor`/`duplication_floor`'s pattern, and for the same reason:
> the backlog is mostly false positives of documented shapes, so rewording it to
> please the gate would be fitting prose to the instrument (`S39`), while a flag
> added tomorrow is one nobody has read. In the roster since `343`, controlled the
> same cycle. Floor `203`; the live figure is what the script prints.

### `SESSION 371` — the twenty-seven `PRICES.md` flags, triaged

**The queue asked the wrong register.** `QUEUE (1)` has asked for *"claims_gate's
six `CLAIMS.md` flags"* every cycle since the instrument shipped. `CLAIMS.md` was
fully triaged at `076` and again at `342`, it carries **four** flags today rather
than six, and all four are in this file's commentary about its own past triages
(`342`). The register that had **never** been triaged is `PRICES.md`, at `27` — see the `forensics/claims_gate.py` per-register counts in the entry.

**Two true positives in twenty-five judgeable — `8.0%`**, by the table below.  Two flags are claims
about the literature (`:33` BHB13 as the field's only certified over-ceiling
result; `:81` the value side as the only tradition past the wall) which cannot be
judged from the registers at all — neither `forensics/board.py` nor any
`Blindness.ledger_determined` -style declaration bears on either; per `R17` they are excluded from **both** columns rather than guessed into
either.

| flag | verdict |
|---|---|
| `:370` *"four declarations … conclude in `OffLineImport`"* | **TRUE** — five. `Gaps.proportionAny_wall_attained` carries `OffLineImport … (2/3)` in its conclusion. The *claim* survives (`2/3 = 1 − 1/3`, and `1/3` is that family's own `ProportionStd`, in the adjacent conjunct); the *count* was stale. Corrected above the text |
| `:410` *"`distinctZeros_le_atomCount_add_Noff` is the only conversion on disk"* | **TRUE** — `Fiber.atomCount_of_distinctZeros_and_Noff` is a second, taking a distinct-zeros bound plus an off-line bound to an `atomCount` bound. Corrected at the sentence |
| `:33`, `:81` | **not judgeable from the registers** — claims about the state of a field. Neither carries a `[RECALL, UNVERIFIED]` label, which `QUEUE (4)` asks for; filed as a lead, not scored |
| `:85`, `:916` | **false** — `exact` as a term of art (Motohashi's spectral expansion; "exact-height pattern") |
| `:203`, `:194` | **false** — both sit inside a **Caveats** list and a **RETRACTED as a bound** block; the sentences limit scope, which is what the gate is asking for |
| `:256`, `:258` | **false** — `μ_T` having no `β` coordinate is a fact about our own definition, checkable from it; the witness is a definition, not a declaration name |
| `:50`, `:198`, `:223`, `:239`, `:696` | **false** — each concludes from a screen, duality argument or table stated in the immediately preceding lines; witnesses are `W`-numbers, cycle numbers and tables, none of which `WITNESS` can read |
| `:397`, `:800`, `:1159`, `:520`, `:666`, `:882` | **false** — absence and history claims about our own tree; `:1159` names both searches and both results in the sentence, which is exactly `R28` |
| `:426`, `:427` | **false** — the arithmetic (`N_d/N > 1` against `distinctZeros ≤ N`) is in the same sentence |
| `:434`-area, `:465`-area | **false** — *"cannot be improved"* cites `171`; *"never been shown tight"* is itself a disclaimer |
| `:994` | **false** — inside a **quotation from the paper**, leaked by the mechanism below |
| remaining | **false** — self-scoping remarks (*"Nothing else here depends on it"*) |

**Both true positives are one shape** — `Gaps.proportionAny_wall_attained` and
`Fiber.atomCount_of_distinctZeros_and_Noff` each falsify a count, not an argument: a
mechanically-verifiable enumeration over our own tree that was right when written and went
stale as the tree grew. Neither is a
wrong claim about mathematics. That is `S115`'s decay pattern showing up in a
*priced* register, and it says which register content needs re-checking: not the
arguments, the enumerations.

**The quote-fragment mechanism, measured and left unfixed.** `:994` is inside a
multi-sentence quotation from `arXiv:2608.13637`. `QUOTED` handles `*"…"*` and
`"…"`, but `scan` splits into sentences **before** `unquoted` runs, so a quotation
spanning more than one sentence leaks every sentence after its first. Across all
eighteen registers the class is **3 flags in 242 (1.2%)** — `ISSUES.md`,
`PRICES.md`, `RULING.md`, one each. Reordering the split would change the flag
count on every register, including the one just measured, so it is declined on
`S39`'s ground, the same ground `342` declined its three classes on: a filter
fitted to its own measurement proves nothing. The mechanism is recorded here so
the next reader does not re-derive it.

### `SESSION 342` — the four `CLAIMS.md` flags, triaged

The prompt has asked for this rate every cycle. **Zero true positives in four**,
and the four are not in the ninety-six claim rows — they are in this file's
commentary about its own past triages.

| flag | verdict |
|---|---|
| `:5` *"Two were found living as prose in three cycles"* | **false** — the two witnesses are named in the same sentence, as *files*; `WITNESS`'s `_EXT` guard drops file names by design |
| `:469` *"lived on a surface the instrument had never seen"* | **false** — a claim about the gate's own scan set, checkable from the script |
| `:490` *"1 true positive in 14 — but it is the one being hunted"* | **false** — witnessed by the fourteen-row table directly above, which `EXEMPT` removes from scanning and therefore from witnessing |
| `:550` *"The route table had never been triaged"* | **false**, and **already graded at `323`** in a blockquote directly above it |

**One reason in three shapes:** each sentence carries its witness in a form the
gate's vocabulary cannot read — a file name, a preceding table, a grading note.
Recorded in `forensics/claims_gate.py` and **not fixed**, on `S39`'s ground that
a filter fitted to its own measurement proves nothing; each widening would mute
real flags.

**The bounded slice that did yield one.** Rather than claim a rate for
`Fiber.lean`'s `108`, I graded only the flags in declarations added at `334`–`341`,
which I wrote and can judge. Six flags, **one true positive**:
`momentK_zero`'s docstring said the first three moments *"are exactly the three
ledger counts the ordinates already determine"* — wrong twice, since `atomCount`
is not a ledger row and `ZeroData.Nsc_eq_ordinate_functional` makes `N_sc` a
fourth ordinate-determined quantity. Corrected at that docstring and at the
`SESSION 335` entry that repeated it. The other five are the documented shapes: a
docstring heading an `iff` theorem, an accurate `never`, a cast described as "the
same fact", a composition naming its own witnesses without dots, and a question.


---

## SESSION 089 — triaging my own prose (`Fiber.lean`, 36 flags)

The largest untriaged flag set was one I created: twelve cycles of new prose in
`Fiber.lean`. Triaged in full.

**1 true positive**, and it is a stale superlative I wrote and then refuted
myself, twelve cycles ago:

| # | text | verdict |
|---|---|---|
| 13 | *"**The residue is exactly the fiber coordinate.** … Nothing beyond `(μ_T, offAt)` is needed — which is what 'the whole residue' means"* (`onOrd_determined`) | **TRUE** — the converse is false and `offAt_not_minimal` refutes it. `S26` recorded the retraction, but it lives 150 lines further down, so the superlative stood here unqualified |
| 12 | *"the fiber coordinate really is the whole residue"* (`NscStd_eq_onAt_functional`) | **TRUE — same claim, second location** |

Both corrected at their locations, each naming `offAt_not_minimal` and `S26`.

The other 34 are false positives of four mechanical shapes, all previously
identified: theorem statements quoted into the flagged sentence (11 of them);
claims whose Lean witness sits on an adjacent line and so falls outside the
sentence the splitter built (9); genuine algebraic identities printed in full and
backed by a named theorem — e.g. *"the reason is an identity: `3N⊛ − 2N − Σm³ =
−Σ m(m−1)(m−2)`"*, which is `three_Nstar_le_thirdMoment_add_two_N` (6); and
directives or `[RECALL]`-marked comparisons (8).

**Rate: 2/36.** Low, and the two it found are the *same* defect the register's
most expensive prose entries are about — a sufficiency result written up as an
identity, with the retraction filed somewhere else.

**The kill condition** — *if the triage finds no true positives in my own prose,
the gate has nothing to say about my writing* — **did not fire.** The instrument
reads my prose no worse than anyone's.

**Standing note:** the dominant false-positive shape here is sentence-splitting
across a docstring/theorem boundary, which is a fixable parser issue and not a
wordlist issue. Named, not built.


---

## SESSION 127 — `LEADS.md` triaged, all 56 flags

> **Re-check, `SESSION 323` (2026-08-17).** `absence_queue` flags the sentence
> below as a claim of absence. It is a **past-tense record of the state before
> the triage this same section then reports** — `146` listed exactly this shape
> among the mechanical false positives it declined to filter, on `S39`'s ground
> that a filter fitted to its own measurement proves nothing. Graded, not fixed.

The route table had never been triaged, and it is the register that decides what
future cycles do.

**2 true positives in 56.** Both are stale claims, not overclaims — the `121`/`122`
species again:

| flag | verdict |
|---|---|
| *"Whether the profile is minimal is not proved and is not claimed"* | **TRUE** — settled both ways in `075`/`077`, fifty cycles earlier, with the answers filed in a **later section of the same file** |
| *"`L5` is the only item that could move a number without closing a box"* | **TRUE** — `084` moved the `Nsc` row by `50.88` points without closing a box and without `L5`; a session-003 board assessment never revisited |

The other 54 are false positives of the four mechanical shapes documented in
`089`: theorem statements quoted into the flagged sentence, claims whose Lean
witness sits on an adjacent line, genuine identities printed in full, and
directives or `[RECALL]`-marked comparisons. A large block (flags 45–49) are the
*corrected* profile-minimality statements — which is how the stale one at the top
of the file was found: the register carries both.

**Rate 2/56 ≈ 3.6%**, and both catches are staleness rather than overclaim, which
is the defect class no instrument in the project patrols (`121`).


---

## SESSION 128 — `E.md` and `FAILURES.md` triaged

**1 true positive in 31**, and it is a *duplicated* stale claim:

> *"The only capacity certificate we can run came in with zeta-23"* —
> `LEADS.md` line 962 **and** `FAILURES.md` line 275, in different wordings.

`Riemann/Capacity.lean` carries eleven capacity theorems of our own, axiom-free
and audited. `LEADS.md` even names the repair as "next rung-0 item, and it is
cheap" — and it was done: `no_gain_past_known` is exactly that statement.
Annotated at both locations.

The other 30 are false positives of the four shapes documented in `089`.

**New sub-species: the duplicated stale claim.** A sentence copied between
registers goes stale in both, and correcting one leaves the other. Neither
`121`'s sweep nor `127`'s would have caught this — `121` looked at `CLAIMS.md`,
`127` at `LEADS.md`, and each would have found one copy and moved on.
