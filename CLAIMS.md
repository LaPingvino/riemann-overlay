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
| **At most 32.75% of the zeros of `ζ` are off the critical line** — unconditional at the baseline's own axiom tier, no star bound; the standard-simple zeros are on the line and disjoint from the off-line ones | `zetaFamily`; axioms `baseline_zeta23` + `zetaNonempty`, count unchanged | `certified_offline`, `offLineImport_of_proportionStd`, `Fiber.Noff_add_NscStd_le_N` | **A** |
| **The `Nsc` row has two independent derivations agreeing exactly** — via `3·NscStd ≤ N + 2·Nsc`, and via the off-line row plus the exchange rate; both give `0.50875` | `zetaFamily` | `certified_nsc_unconditional`, `certified_nsc_via_offline` | **A** |
| **`baseline_przz` is redundant** — `ProportionStd` is monotone in its constant, so `0.4162` follows from `0.6725`; `#print axioms` confirms the derivation consumes only `baseline_zeta23` | the two `ProportionStd` baselines | `Family.ProportionStd.mono`, `przz_of_zeta23` | **A** |
| **Every point of off-line control is worth half a point of the `Nsc` row** — `ProportionStd κ` plus `N_off ≤ (β+o(1))·N` gives `Proportion (κ − β/2)`; and the derivative family's `Proportion κ'` supplies `β = 1 − κ'` *given two named transfer hypotheses* | all families; the transfer hypotheses are **not** discharged | `proportion_of_offLineImport`, `offLineImport_of_derivative`, `Fiber.Nsc_add_Noff_le_N` | **A** (the conditional; the ζ instantiation is **not** claimed) |
| **The four-quantity bridge exists and collapses** — `2·A + #{odd atoms} ≤ N + 2·Nsc` is strictly finer, but `A, #{odd atoms} ≥ NscStd` recovers `(3,2)` exactly, so it moves the row only given a lower bound on the atom count | all `ZeroData` | `Fiber.two_mul_atomCount_add_oddAtoms_le`, `three_mul_NscStd_le_of_four` | **A** |
| **`(3, 2)` is the optimal constant pair** — any bridge `c·NscStd ≤ N + d·Nsc` valid on all `ZeroData` has `c ≤ 3`, and `c = 3` forces `d ≥ 2`; so `(3κ−1)/2` cannot be improved *by an inequality of this shape*. A bridge using further `μ_T`-visible data is not excluded | bridges in the triple `(NscStd, N, Nsc)` only | `Fiber.bridge_optimal`, `haunted_atom_counts`, `simple_atom_counts` | **A** |
| **`3·NscStd ≤ N + 2·Nsc`, unconditional and axiom-free** — a haunted atom has even nonzero off-line part, hence mass `≥ 3`, so it costs three zeros and yields one `NscStd`; transported, `ProportionStd κ ⟹ Proportion (3κ−1)/2` with no star bound | all `ZeroData`, all families | `Fiber.three_mul_NscStd_le_N_add_two_mul_Nsc`, `proportion_of_proportionStd`, `certified_nsc_unconditional` | **A** |
| **The two invisible rows are coupled, sharply** — `2·(NscStd − Nsc) ≤ N_off`, with equality on `n` atoms of mass `3`; every haunted zero costs at least two off-line zeros | all `ZeroData`; sharpness on the mass-`3` family | `Fiber.two_mul_NscStd_le_Noff_add_two_mul_Nsc`, `coupling_tight` | **A** |
| **The other invisible row is bracketed too** — `N_off` is even and `N_off + #{odd atoms} ≤ N`, both endpoints `μ_T` functionals, and every parity-admissible value is attained | all `ZeroData`; attainment on `n` atoms of mass `3` | `Fiber.Noff_even`, `Noff_add_oddAtoms_le_N`, `Noff_tight_chain` | **A** |
| **The bracket is attained at every value, at every width** — for all `t ≤ n`, `n` atoms of mass `3` realise `NscStd = t` with `Nsc = 0`, `#{odd atoms} = n`, and a `t`-independent `μ_T` | all `n`, all `t ≤ n` | `Fiber.bracket_tight_chain`, `chain_profile`, `profile_superpose_disjoint` | **A** |
| **The bracket is attained at every value** — on the two-atom mass-3 family both endpoints and the interior point are realised by configurations sharing one `μ_T` | two atoms of mass `3`; **not** proved for arbitrary `μ_T` | `Fiber.bracket_tight_two_atoms`, `oddAtoms_from_profile` | **A** |
| **The class computes an interval for `NscStd`, not a point** — `Nsc ≤ NscStd ≤ #{odd atoms}`, and both endpoints are functionals of `μ_T` alone | all `ZeroData` | `Fiber.NscStd_bracketed`, `NscStd_le_oddAtoms`, `bracket_muInvariant`, `Basic.Nsc_le_NscStd` | **A** |
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
| The bandwidth-one ceiling is `≤ 0.6818287` | bandwidth-one certificates | `Zeta23.PairCeiling.ceiling_law256` — **imported**, and *not reachable from `import Riemann`* | **A**, with a caveat parked for Joop |
| "Multiplicity bounds cannot tighten `C`" (W7, precise part) | `BoundedMult M` — `H γ ≤ M`, pure counting, no Euler product | `Optimal.prop1_LP_optimal_cheap` | **A** |
| "No free classical invariant *of any kind* will tighten `C`" (W7, general) | *"classical invariant"* — still informal | — | **C** |
| "Post-1974 extremal technology cannot buy anything through the `v` slot" | the `v` slot of the rank–trace container at `λ = 1` — **well defined** | a quadrature optimisation (`N = 160` midpoint, `0.6725126` vs M–T's `0.6725007`), reproducible via `forensics/window_opt.py` | **N** |
| E20's plane: the cleavage is the one thing no single-natured instrument can certify | *"single-natured instrument"* — informal | — | **C**, and already marked statistically unsupported in `FAILURES.md` |

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
sentence that voids it. Nothing false was written; it was **badly ordered**,
which for a register meant to be quoted from is the same hazard by a different
route. **Fixed this cycle:** a warning now sits immediately above the tables.

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
