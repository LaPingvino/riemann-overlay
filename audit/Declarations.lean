/-
MANDATORY AUDIT POINT (ISSUES #17): every name this project makes claims about
must EXIST.  A green `lake build` proves nothing about a declaration that was
never written — that is how session 013 filed a register entry for three
theorems that did not exist.

This file fails to compile the moment a claimed name disappears or is renamed.
`tools/proportion.go` runs it before writing any log line.
-/
import Riemann

-- the combinatorial core
#check @Riemann.ZeroData.prop1
#check @Riemann.ZeroData.N_add_Noff_le_Nstar
#check @Riemann.ZeroData.two_NscStd_le
#check @Riemann.ZeroData.six_mul_NscStd_le
#check @Riemann.ZeroData.six_mul_card_le_Nstar_sub_N
#check @Riemann.ZeroData.NscStd_eq_Nsc_add_haunted
#check @Riemann.ZeroData.three_le_H_of_haunted
#check @Riemann.ZeroData.odd_mass_inhabited
#check @Riemann.ZeroData.card_odd_atoms_le_critical
-- X: the μ_T layer
#check @Riemann.ZeroData.ordinates
#check @Riemann.ZeroData.H_eq_count
#check @Riemann.ZeroData.Nsc_eq_ordinate_functional
#check @Riemann.ZeroData.N_Nstar_ordinate_functional
#check @Riemann.ZeroData.ordinates_simple_iff
#check @Riemann.ZeroData.Nsc_eq_N_iff
-- A2: resolution independence
#check @Riemann.ZeroData.Hr
#check @Riemann.ZeroData.Hr_zero
#check @Riemann.ZeroData.on_line_of_Hr_eq_one
#check @Riemann.ZeroData.odd_Hr_inhabited
-- the gauge boundary and the R16 audit
#check @Riemann.Gauge.ordinates_eq
#check @Riemann.Gauge.Nsc_gauge_invariant
#check @Riemann.Gauge.NscStd_not_gauge_invariant
#check @Riemann.Gauge.offline_le_tight
-- the zeta family, constructed
#check @Riemann.zetaZeroData
#check @Riemann.ZeroData.ofMult
#check @Riemann.ZeroData.ofMult_N
-- transfer and ledger
#check @Riemann.Counts.proportion_of_starBound
#check @Riemann.Counts.one_le_of_starBound
#check @Riemann.Family.offline_le
#check @Riemann.Family.nscStd_le_nsc_add
#check @Riemann.nsc_of_nscStd
#check @Riemann.nsc_row_opens
#check @Riemann.certified_std
#check @Riemann.certified_nsc
#check @Riemann.certified_axiomFree
-- Route I numerics
#check @Riemann.Cbound
#check @Riemann.Cbound_lt_two
#check @Riemann.Cbound_lt_record
#check @Riemann.c0_lower_bound
#check @Riemann.Gauge.prop1_tight
#check @Riemann.Gauge.pairOnly_Nsc
-- rung 1: the blindness cluster relativised (W28 / tri-read {4,7,8})
#check @Riemann.Blindness.MuInvariant
#check @Riemann.Blindness.MuInvariant.forall
#check @Riemann.Blindness.no_muInvariant_bundle_computes_NscStd
#check @Riemann.Blindness.no_muInvariant_theory_computes_NscStd
#check @Riemann.Blindness.no_muInvariant_bundle_computes_Noff
#check @Riemann.Blindness.separating_bundle_excludes
#check @Riemann.Blindness.NscStd_not_ordinate_functional
#check @Riemann.Blindness.onLine_not_muInvariant
#check @Riemann.Blindness.NscStd_eq_Nsc_of_onLine
#check @Riemann.Blindness.two_le_Hr_of_off_line
-- the fiber: blindness supported exactly on the crowded atoms
#check @Riemann.Blindness.config
#check @Riemann.Blindness.config_ordinates_eq
#check @Riemann.Blindness.config_parity
#check @Riemann.Blindness.Noff_eq_zero_of_simple
#check @Riemann.Blindness.blind_at_every_crowded_mass
-- the acceptance test and its calibration inputs
#check @Riemann.Blindness.Discriminates
#check @Riemann.Blindness.not_discriminates_of_factors
#check @Riemann.Blindness.not_factors_of_discriminates
#check @Riemann.Blindness.landau
#check @Riemann.Blindness.landau_discriminates
#check @Riemann.Blindness.Discriminates₂
#check @Riemann.Blindness.spectator_gauge_pair
#check @Riemann.Blindness.landau_discriminates₂
#check @Riemann.Blindness.not_discriminates₂_of_factors
#check @Riemann.Blindness.swap_not_a_gauge_pair
-- rung 0: the capacity skeleton (no arithmetic input; not about zeta)
#check @Riemann.Capacity.Admissible
#check @Riemann.Capacity.pinned_value_is_floor
#check @Riemann.Capacity.pinned_value_attained
#check @Riemann.Capacity.unbounded_below_of_neg_outside
#check @Riemann.Capacity.value_eq_pinned
#check @Riemann.Capacity.no_gain_past_known
#check @Riemann.Capacity.AdmissibleOn
#check @Riemann.Capacity.value_eq_pinned_integral
#check @Riemann.Capacity.no_gain_past_known_integral
-- SESSION 198: why the bandwidth-one half of rung 0 is not bookkeeping.
#check @Riemann.Capacity.subclass_floor_strictly_above_pinned
-- SESSION 199: and #10's no-gain conclusion does not transfer to a subclass.
#check @Riemann.Capacity.no_gain_past_known_fails_on_subclass
#check @Riemann.Capacity.unbounded_below_of_neg_outside_integral
-- prop1's optimality in the two moments, certified (was a docstring claim)
#check @Riemann.Optimal.LinearBound
#check @Riemann.Optimal.linearBound_prop1
#check @Riemann.Optimal.linearBound_le_one
#check @Riemann.Optimal.linearBound_mass2
#check @Riemann.Optimal.prop1_LP_optimal
#check @Riemann.Optimal.BoundedMult
#check @Riemann.Optimal.LinearBoundCheap
#check @Riemann.Optimal.prop1_LP_optimal_cheap
-- SESSION 200: the optimality is a fact about the class, not the inequality.
#check @Riemann.Optimal.prop1_LP_optimal_needs_the_witnesses
-- SESSION 201: and it fails outright on the multiplicity-one class.
#check @Riemann.Optimal.Nsc_eq_N_of_boundedMult_one
#check @Riemann.Optimal.prop1_LP_optimal_fails_on_simple_class
-- SESSION 202: and the threshold between them is exactly M = 2.
#check @Riemann.Optimal.prop1_LP_threshold_at_two
-- SESSION 203: and that threshold class is exactly {Nsc = N}.
#check @Riemann.Optimal.boundedMult_one_iff_Nsc_eq_N
-- SESSION 204: #20's "for every m >= 1" quantifier, machine-checked.
#check @Riemann.Blindness.config_Nstar_pure
#check @Riemann.Blindness.config_Nsc_pure
#check @Riemann.Optimal.linearBound_mass
-- SESSION 205: and the converse, so #20's characterisation is checked both ways.
#check @Riemann.Blindness.Nsc_eq_sum_mass_one
#check @Riemann.Optimal.linearBound_of_mass_test
-- SESSION 206: and the feasible set is three inequalities; only masses 1 and 2 bind.
#check @Riemann.Optimal.linearBound_iff
-- SESSION 207: the LP's value, attained at prop1.
#check @Riemann.Optimal.linearBound_prop1_via_iff
#check @Riemann.Optimal.prop1_LP_value
-- SESSION 208: the three-moment program, and why 206's reduction stops at two.
#check @Riemann.Blindness.config_thirdMoment_pure
#check @Riemann.Optimal.LinearBound3
#check @Riemann.Optimal.linearBound3_mass
#check @Riemann.Optimal.linearBound3_not_reducible_to_mass_two
-- SESSION 209: and the three-moment LP has the same value, 2 - C.
#check @Riemann.Optimal.prop1_as_linearBound3
#check @Riemann.Optimal.linearBound3_no_gain
#check @Riemann.Optimal.linearBound3_LP_value
-- SESSION 210: order four repeats it — the pattern is the tight-at-1-and-2 minorant.
#check @Riemann.Blindness.fourthMoment
#check @Riemann.Blindness.seven_Nstar_le_fourthMoment_add_six_N
#check @Riemann.Blindness.config_fourthMoment_pure
#check @Riemann.Optimal.LinearBound4
#check @Riemann.Optimal.linearBound4_mass
#check @Riemann.Optimal.prop1_as_linearBound4
#check @Riemann.Optimal.linearBound4_no_gain
#check @Riemann.Optimal.linearBound4_LP_value
-- SESSION 211: and every order at once — the moment route is walled for all k >= 2.
#check @Riemann.Blindness.moment_minorant
#check @Riemann.Blindness.momentK
#check @Riemann.Blindness.moment_obstruction
#check @Riemann.Blindness.config_momentK_pure
#check @Riemann.Optimal.LinearBoundK
#check @Riemann.Optimal.linearBoundK_mass
#check @Riemann.Optimal.prop1_as_linearBoundK
#check @Riemann.Optimal.linearBoundK_no_gain
#check @Riemann.Optimal.linearBoundK_LP_value
-- SESSION 212: a feasible c is non-positive, so any realizable C_k is no better.
#check @Riemann.Optimal.linearBoundK_c_nonpos
#check @Riemann.Optimal.linearBoundK_no_gain_at_any_moment
-- SESSION 214: the NscAny genre wall at family level, which 197 declined.
#check @Riemann.Family.NscAny
#check @Riemann.Family.ProportionAny
#check @Riemann.Family.proportionAny_le_one
#check @Riemann.Family.proportionStd_of_proportionAny
-- SESSION 218: and that family-level wall is attained.
#check @Riemann.proportionAny_wall_attained
-- SESSION 219: and the distinct-zeros conversion rate is attained too.
#check @Riemann.hauntedDensity_distinctZeros_attained
-- SESSION 220: the three genres wall at one configuration but not at one layer.
#check @Riemann.Blindness.atomCount_ordinate_functional
-- SESSION 229: and oddAtoms likewise, which is what makes NscStd's bracket useful.
#check @Riemann.Blindness.oddAtoms_ordinate_functional
#check @Riemann.Blindness.NscAny_not_ordinate_functional
-- SESSION 221: and not a functional of (mu_T, offAt) either.
#check @Riemann.Blindness.NscAny_not_fiber_functional
-- SESSION 222: hence not a profile functional, which is why 196's entries are inequalities.
#check @Riemann.Blindness.profile_eq_of_ordinates_offAt
#check @Riemann.Blindness.NscAny_not_profile_functional
#check @Riemann.Blindness.no_profile_function_computes_NscAny
-- SESSION 223: and the same pair hides N_d from the fiber coordinate too.
#check @Riemann.Blindness.distinctZeros_not_fiber_functional
-- SESSION 225: the haunted count is exactly the mu_T-invisible part of NscStd.
#check @Riemann.Blindness.hauntedSet_card_not_ordinate_functional
#check @Riemann.Blindness.hauntedSet_card_determined
-- SESSION 226: the two haunted counts are the same number; 225 carried across.
-- SESSION 230: NoHaunted is a separating bundle — it makes NscStd mu_T-computable.
-- SESSION 234: the multiplicity ladder's first rung is free.
#check @Riemann.noSmallHaunted_three
-- SESSION 235: the ladder has only odd rungs; even m is the same hypothesis as m+1.
#check @Riemann.noSmallHaunted_even_step
#check @Riemann.noSmallHaunted_even_iff
-- SESSION 236: what a rung buys, and the constant that governs the ladder.
#check @Riemann.ladder_gap
#check @Riemann.ladder_step
#check @Riemann.ladder_gap_at_three
-- SESSION 237: the same off-line formula at both baselines.
#check @Riemann.offLine_bound_at_both_baselines
-- SESSION 238: the unconditional row and the xi' route are one formula.
#check @Riemann.exchange_at_both_imports
-- SESSION 239: the off-line currency's range, its inverse, and the board in beta.
#check @Riemann.offLineImport_range
#check @Riemann.offLineImport_inverse
#check @Riemann.offLineImport_board_prices
-- SESSION 240: both currencies saturate at kappa.
#check @Riemann.ladder_lt_kappa
#check @Riemann.currencies_saturate_at_kappa
-- SESSION 241: the third currency's ceiling is 1, which is why two rows sit above kappa.
#check @Riemann.Counts.starBound_ceiling
#check @Riemann.Counts.starBound_ceiling_iff
-- SESSION 243: E11's pincer, sharpened for the multiplicity family.
#check @Riemann.Optimal.mult_cap_excluding_pairOnly
-- SESSION 247: E11's jaw exists and is mu_T-visible, but every instance is priced in kappa.
#check @Riemann.Optimal.pairOnly_oddAtoms
#check @Riemann.Optimal.oddAtoms_bound_excludes_pairOnly
-- SESSION 249: what the odd-atom class does to prop1's LP.
#check @Riemann.prop1_saturates_mass_two_family
#check @Riemann.oddAtom_class_ratio
-- SESSION 250: multiplicity <= 2 IS the equality class of the star bound.
#check @Riemann.Blindness.two_mul_N_le_Nstar_add_Nsc
#check @Riemann.Blindness.boundedMult_two_iff_star_exact
-- SESSION 251: odd atoms are the simple ones at multiplicity two.
#check @Riemann.Blindness.oddAtoms_eq_Nsc_of_mult_le_two
#check @Riemann.Blindness.Nstar_add_oddAtoms_eq_two_mul_N
-- SESSION 252: the odd-atom equality characterises the class too.
#check @Riemann.Blindness.boundedMult_two_iff_oddAtom_exact
-- SESSION 254: the ladder's supremum is kappa, over the rungs that exist.
#check @Riemann.ladder_approaches_kappa
-- SESSION 255: the domination of the two kappa rows, lifted to Family.
#check @Riemann.Family.noHaunted_of_boundedMult_two
-- SESSION 257: NoHaunted buys no star bound; 181's docstring, witnessed.
#check @Riemann.Blindness.noHaunted_no_starBound
-- SESSION 260: the threshold is exactly two; H <= 3 already admits a haunted atom.
#check @Riemann.Blindness.noHaunted_fails_at_mult_three
#check @Riemann.Family.noHaunted_sharp_at_two
-- SESSION 261: a cap collapses the ladder to its limit one rung above it.
#check @Riemann.noHaunted_of_boundedMult_of_noSmallHaunted
#check @Riemann.noHaunted_of_mult_three_rung_five
-- SESSION 262: the off-line currency sharpens with the rung.
#check @Riemann.Blindness.pred_mul_haunted_le_Noff
#check @Riemann.hauntedDensity_of_offLineImport_at_rung
-- SESSION 270: our N is zeta-23's Ncount — half of discharging zetaNonempty.
#check @Riemann.zetaZeroData_N
-- SESSION 271: the residue of zetaNonempty, stated exactly.
#check @Riemann.Ncount_mono_left
#check @Riemann.zetaNonempty_of_dyadic
-- SESSION 272: the discharge reduced to one imported fact.
#check @Riemann.eventually_one_le_ell1
#check @Riemann.eventually_const_mul_log_lt
#check @Riemann.zetaNonempty_of_rvm_main
-- SESSION 273: a single fibre's multiplicity, for the NscStd-side bridge.
#check @Riemann.ZeroData.ofMult_count
-- SESSION 274: the NscStd count bridge to zeta-23's N0simple.
#check @Riemann.ZeroData.ofMult_NscStd
#check @Riemann.zetaZeroData_NscStd
-- SESSION 276: cos to order ten, for the cot(1/sqrt2) bound.
#check @Riemann.cos_bound10
#check @Riemann.sin_bound10
-- SESSION 279: the decimal 0.6725 is a proved floor for 3/2 - cot(1/sqrt2)/sqrt2.
#check @Riemann.baseline_decimal_le_exact
-- SESSION 280: baseline_zeta23 reduced to zeta-23's cumulative ThmD row.
#check @Riemann.baseline_of_cumulative
-- SESSION 283: ISSUES #7's split — what zeta23_xiPrime absorbs, named.
#check @Riemann.xiPrime_proportion_of_std_and_noHaunted
-- SESSION 286: oddAtoms counts odd ON-LINE multiplicity.
#check @Riemann.Blindness.oddAtoms_eq_odd_onAt
#check @Riemann.Blindness.onAt_pos_of_odd_H
-- SESSION 287: NscStd counts onAt = 1; the visibility map has a second level.
#check @Riemann.Blindness.NscStd_eq_onAt_one
-- SESSION 288: a haunted ordinate is onAt = 1 with off-line mass beside it.
#check @Riemann.Blindness.hauntedCount_eq_onAt_one_offAt_pos
-- SESSION 289: the free rung, pointwise and without the zero-level lemma.
#check @Riemann.Blindness.three_le_H_of_haunted_at
-- SESSION 292: Nsc in (onAt, offAt) coordinates; the three make a partition.
#check @Riemann.Blindness.Nsc_eq_onAt_one_offAt_zero
-- SESSION 293: the bracket's upper gap — odd on-line count above one.
#check @Riemann.Blindness.oddAtoms_eq_NscStd_add_oddAbove
-- SESSION 294: the profile in 293's (onAt, offAt) coordinates.
#check @Riemann.Blindness.onProfile
#check @Riemann.Blindness.onProfile_eq_profile_map
#check @Riemann.Blindness.profile_eq_onProfile_map
#check @Riemann.Blindness.NscStd_from_onProfile
#check @Riemann.Blindness.hauntedCount_from_onProfile
#check @Riemann.Blindness.Nsc_from_onProfile
-- SESSION 295: where hauntedCount and oddAtoms sit relative to the ledger.
#check @Riemann.Blindness.oddAtoms_mod_four
#check @Riemann.Blindness.hauntedCount_eq_NscStd_sub_Nsc
#check @Riemann.Blindness.oddAtoms_not_determined_by_ledger
-- SESSION 297: rung 3 is the last family-generic rung of the ladder.
#check @Riemann.NoSmallHaunted.mono_le
#check @Riemann.free_ladder_stops_at_three
-- SESSION 299: the m = 7 rung's precision, prose until now.
#check @Riemann.ladder_seven_exact_value
#check @Riemann.ladder_seven_shortfall
-- SESSION 302: the ledger's upper bound on oddAtoms, and its attainment.
#check @Riemann.Blindness.three_mul_oddAtoms_le
#check @Riemann.Blindness.three_mul_oddAtoms_attained
-- SESSION 303: equality needs mass 1 or 3, not pure triples; and the rate-3/2 route.
#check @Riemann.Blindness.three_mul_oddAtoms_eq_cap_witness
#check @Riemann.proportion_of_oddAtoms
-- SESSION 304: the crossover LEADS.md carried as prose since 098.
#check @Riemann.starBound_delta_beats_baseline
-- SESSION 305: the equality set of 302's bound, and that it is a new one.
#check @Riemann.Blindness.three_mul_oddAtoms_eq_iff
#check @Riemann.Blindness.three_mul_oddAtoms_eq_iff_separates
-- SESSION 306: the 3/2 rate is attained across the whole equality set.
#check @Riemann.proportion_of_oddAtoms_attained
-- SESSION 307: the threshold a supplier must clear.
#check @Riemann.oddAtoms_input_beats_certified_row_iff
-- SESSION 308: the dependency's N0star, in our vocabulary, and its bracket.
#check @Riemann.Blindness.onLineOrdinates
#check @Riemann.Blindness.oddAtoms_le_onLineOrdinates
#check @Riemann.Blindness.onLineOrdinates_le_atomCount
-- SESSION 309: the gap between the two vocabularies, bounded.
#check @Riemann.Blindness.evenOnAt
#check @Riemann.Blindness.onLineOrdinates_eq_oddAtoms_add_evenOnAt
#check @Riemann.Blindness.evenOnAt_add_atomCount_le_N
#check @Riemann.Blindness.onLineOrdinates_le_N
#check @Riemann.onLineOrdinates_route_threshold
-- SESSION 310: the chain's last gap — ordinates with no on-line zero.
#check @Riemann.Blindness.offLineOnly
#check @Riemann.Blindness.onLineOrdinates_add_offLineOnly
#check @Riemann.Blindness.offLineOnly_le_Noff
-- SESSION 311: simple zeros off the line — the gap 222 computed and discarded.
#check @Riemann.ZeroData.simpleOffLine
#check @Riemann.ZeroData.NscStd_add_simpleOffLine
#check @Riemann.ZeroData.simpleOffLine_le_Noff
#check @Riemann.ZeroData.NscAny_eq_NscStd_of_Noff_zero
-- SESSION 312: which gaps Noff = 0 closes, and one that survives it.
#check @Riemann.Blindness.offLineOnly_eq_zero_of_Noff_zero
#check @Riemann.Blindness.hauntedCount_eq_zero_of_Noff_zero
#check @Riemann.Blindness.evenOnAt_survives_Noff_zero
-- SESSION 313: the upper gap promoted to a def, and the chain closing on itself.
#check @Riemann.Blindness.oddAbove
#check @Riemann.Blindness.Nsc_add_gaps_eq_atomCount_of_Noff_zero
-- SESSION 314: the decomposition without the hypothesis, and all five inhabited.
#check @Riemann.Blindness.atomCount_decomposition
#check @Riemann.Blindness.offLineOnly_from_profile
-- SESSION 321: the profile dictionary completed, and 312's second witness.
#check @Riemann.Blindness.oddAbove_from_profile
#check @Riemann.Blindness.evenOnAt_from_profile
#check @Riemann.Blindness.oddAbove_survives_Noff_zero
#check @Riemann.Blindness.atomCount_decomposition_all_inhabited
-- SESSION 315: each class charged its minimum mass.
-- SESSION 325: Blindness extended to the decomposition's four gaps.
-- SESSION 329: the decomposition priced in the N* currency.
#check @Riemann.Blindness.star_charges_every_class
-- SESSION 330: the same classes at the third moment, and the weights do not scale.
-- SESSION 331: the general moment; 329 and 330 are now corollaries.
#check @Riemann.Blindness.momentK_charges_every_class
#check @Riemann.Blindness.momentK_two
#check @Riemann.Blindness.momentK_three
#check @Riemann.Blindness.thirdMoment_charges_every_class
#check @Riemann.Blindness.third_moment_weights_not_parallel
-- SESSION 332: every member of the family is sharp, at one configuration.
-- SESSION 333: mass at most three saturates the whole family.
#check @Riemann.Blindness.momentK_charges_eq_of_mult_le_three
-- SESSION 334: the converse, so mass at most three is exactly the condition.
#check @Riemann.Blindness.momentK_charges_lt_of_big
#check @Riemann.Blindness.momentK_charges_eq_iff
#check @Riemann.Blindness.momentK_from_profile
#check @Riemann.Blindness.momentK_five_class
#check @Riemann.Blindness.momentK_charges_tight
#check @Riemann.Blindness.gauge_pair_separates_haunted_and_oddAbove
#check @Riemann.Blindness.gauge_pair_two_separates_even_and_offLine
-- SESSION 326: the argument abstracted, and three new necessity theorems.
#check @Riemann.Blindness.not_muInvariant_computable_of_separating
#check @Riemann.Blindness.oddAbove_not_ordinate_functional
#check @Riemann.Blindness.evenOnAt_not_ordinate_functional
#check @Riemann.Blindness.offLineOnly_not_ordinate_functional
#check @Riemann.Blindness.mass_charges_every_class
#check @Riemann.Blindness.Nsc_add_gaps_le_N
-- SESSION 316: the weights are tight; the bound is a re-coordinatisation.
#check @Riemann.Blindness.Nsc_add_gaps_le_N_tight
#check @Riemann.Blindness.noHaunted_bundle_computes_NscStd
#check @Riemann.Blindness.noHaunted_bundle_excludes
#check @Riemann.Blindness.hauntedCount_eq_hauntedSet_card
#check @Riemann.Blindness.hauntedCount_not_ordinate_functional
#check @Riemann.Blindness.hauntedCount_determined
-- SESSION 227: the two literature quantities, related to each other.
-- SESSION 228: the 1/2-vs-2^-1 normalisation helpers (R24).
#check @Riemann.Blindness.offLine_ne_half
#check @Riemann.Blindness.offLine_ne_refl
#check @Riemann.Blindness.offLine_mirror_ne_half
#check @Riemann.Blindness.NscAny_le_distinctZeros
#check @Riemann.Blindness.NscAny_le_distinctZeros_attained_and_strict
-- SESSION 216: two ledger entries are not recoverable from the other four.
#check @Riemann.Blindness.Noff_not_determined_by_ledger
#check @Riemann.Blindness.NscStd_not_determined_by_ledger
-- SESSION 217: the remaining three, so no ledger entry is redundant.
#check @Riemann.Blindness.threeAtom
#check @Riemann.Blindness.threeAtom_profile
#check @Riemann.Blindness.N_not_determined_by_ledger
#check @Riemann.Blindness.Nstar_not_determined_by_ledger
#check @Riemann.Blindness.Nsc_not_determined_by_ledger
-- X from the other side: the fiber decomposition and what each row reads
#check @Riemann.Blindness.onAt
#check @Riemann.Blindness.offAt
#check @Riemann.Blindness.H_eq_onAt_add_offAt
#check @Riemann.Blindness.count_eq_onAt
#check @Riemann.Blindness.NscStd_eq_onAt_functional
#check @Riemann.Blindness.Nsc_reads_total
#check @Riemann.Blindness.onOrd
#check @Riemann.Blindness.count_onOrd
#check @Riemann.Blindness.NscStd_eq_onOrd_functional
#check @Riemann.Blindness.onAt_determined
#check @Riemann.Blindness.NscStd_determined
#check @Riemann.Blindness.onOrd_determined
#check @Riemann.Blindness.card_onOrd_add_Noff
#check @Riemann.Blindness.Noff_determined
#check @Riemann.Blindness.ledger_determined
#check @Riemann.Blindness.offAt_superpose
#check @Riemann.Blindness.landau_cannot_determine_offAt
#check @Riemann.Blindness.offAt_not_minimal
#check @Riemann.Blindness.relabel
#check @Riemann.Blindness.relabel_H
#check @Riemann.Blindness.relabel_count
#check @Riemann.Blindness.ledger_relabel_invariant
-- the profile: the ledger with the heights discarded
#check @Riemann.Blindness.offOrd
#check @Riemann.Blindness.count_offOrd
#check @Riemann.Blindness.profile
#check @Riemann.Blindness.N_from_profile
#check @Riemann.Blindness.Nstar_from_profile
#check @Riemann.Blindness.Nsc_from_profile
#check @Riemann.Blindness.NscStd_from_profile
#check @Riemann.Blindness.Noff_from_profile
#check @Riemann.Blindness.thirdMoment
#check @Riemann.Blindness.thirdMoment_determined
#check @Riemann.Blindness.moment_determined
#check @Riemann.Blindness.ledger_visibility_split
#check @Riemann.Blindness.N_eq_sum_H
#check @Riemann.Blindness.Nstar_eq_sum_H_sq
#check @Riemann.Blindness.three_Nstar_le_thirdMoment_add_two_N
#check @Riemann.Capacity.reweighting_worst_case
#check @Riemann.Capacity.weighted_sum_le_mass_mul
#check @Riemann.Capacity.equal_mass_equal_worst_case
#check @Riemann.Blindness.factMoment
#check @Riemann.Blindness.factMoment_eq_zero_of_masses_le_two
#check @Riemann.Optimal.moment_route_walled
#check @Riemann.Blindness.zeroData_not_rigid
#check @Riemann.Blindness.zeroData_admits_both
#check @Riemann.Blindness.fiber_states_share_ordinates
#check @Riemann.Blindness.fiber_states_distinguished
#check @Riemann.Blindness.gauge_orbit_size
#check @Riemann.Blindness.config_onAt
#check @Riemann.Blindness.config_NscStd
-- SESSION 196: the `NscAny` dictionary bounds, attained and strict.
-- SESSION 197: the genre wall those bounds carry.
#check @Riemann.ZeroData.nscAny_import_transfer
#check @Riemann.ZeroData.nscAny_import_kappa_le_one
#check @Riemann.ZeroData.nscAny_import_ceiling
#check @Riemann.ZeroData.nscAny_ceiling_is_the_certified_row
#check @Riemann.Blindness.nscAny_import_transfer_attained
#check @Riemann.Blindness.config_NscAny
#check @Riemann.Blindness.nscAny_bounds_attained
#check @Riemann.Blindness.nscStd_le_nscAny_attained
#check @Riemann.Blindness.nscAny_bounds_strict
#check @Riemann.Blindness.odd_mass_NscStd_ambiguous
#check @Riemann.Blindness.even_mass_NscStd_zero
#check @Riemann.Blindness.twoAtom
#check @Riemann.Blindness.twoAtom_ordinates
#check @Riemann.Blindness.twoAtom_profile
#check @Riemann.Blindness.profile_not_minimal
#check @Riemann.Blindness.configAt_N
#check @Riemann.Blindness.configAt_profile
#check @Riemann.Blindness.profile_minimal_among_local
#check @Riemann.Blindness.mass_only_not_sufficient
#check @Riemann.Blindness.off_only_not_sufficient
#check @Riemann.Blindness.even_offAt
#check @Riemann.Blindness.oddAtoms
#check @Riemann.Blindness.NscStd_le_oddAtoms
#check @Riemann.Blindness.bracket_muInvariant
#check @Riemann.Blindness.NscStd_bracketed
#check @Riemann.Blindness.oddAtoms_from_profile
#check @Riemann.Blindness.bracket_tight_two_atoms
#check @Riemann.Blindness.H_superpose
#check @Riemann.Blindness.profile_superpose_disjoint
#check @Riemann.Blindness.chain
#check @Riemann.Blindness.chain_profile
#check @Riemann.Blindness.chain_ordinates_congr
#check @Riemann.Blindness.bracket_tight_chain
#check @Riemann.Blindness.Noff_even
#check @Riemann.Blindness.Noff_add_oddAtoms_le_N
#check @Riemann.Blindness.Noff_tight_chain
#check @Riemann.Blindness.two_mul_NscStd_le_Noff_add_two_mul_Nsc
#check @Riemann.Blindness.coupling_tight
#check @Riemann.Blindness.Noff_le_N
#check @Riemann.Blindness.Nsc_ge_of_Noff_le
#check @Riemann.Blindness.two_mul_NscStd_le_two_mul_Nsc_add_N
#check @Riemann.Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc
#check @Riemann.proportion_of_proportionStd
#check @Riemann.certified_nsc_unconditional
#check @Riemann.Blindness.haunted_atom_counts
#check @Riemann.Blindness.simple_atom_counts
#check @Riemann.Blindness.bridge_optimal
#check @Riemann.Blindness.atomCount
#check @Riemann.Blindness.two_mul_atomCount_add_oddAtoms_le
#check @Riemann.Blindness.three_mul_NscStd_le_of_four
#check @Riemann.Blindness.Nsc_add_Noff_le_N
#check @Riemann.OffLineImport
#check @Riemann.proportion_of_offLineImport
#check @Riemann.OffTransfer
#check @Riemann.NzComparable
#check @Riemann.offLineImport_of_derivative
#check @Riemann.Family.Nz_nonneg
#check @Riemann.Family.ProportionStd.mono
#check @Riemann.przz_of_zeta23
#check @Riemann.Blindness.Noff_add_NscStd_le_N
#check @Riemann.offLineImport_of_proportionStd
#check @Riemann.certified_offline
#check @Riemann.certified_nsc_via_offline
#check @Riemann.Blindness.no_starBound_from_proportionStd
#check @Riemann.Blindness.NscStd_le_atomCount
#check @Riemann.Family.atomCount
#check @Riemann.atomCount_ge_of_proportionStd
#check @Riemann.Blindness.Nstar_le_of_multiplicity_le
#check @Riemann.starBound_of_multiplicity_le
#check @Riemann.Blindness.lowMult
#check @Riemann.Blindness.no_starBound_from_lowMult
#check @Riemann.Blindness.goodCount
#check @Riemann.Blindness.no_starBound_from_goodness
#check @Riemann.Blindness.lowMult_eq_goodCount
#check @Riemann.Blindness.no_starBound_from_goodness_at_any_level
#check @Riemann.Blindness.Nstar_add_mul_Nsc_le
#check @Riemann.starBound_of_multiplicity_and_proportion
#check @Riemann.starBound_of_multiplicity_two
#check @Riemann.Blindness.Nsc_eq_NscStd_of_mult_le_two
#check @Riemann.Blindness.Nstar_add_Nsc_eq_two_mul_N
#check @Riemann.starBound_of_mult_le_two
#check @Riemann.starBound_of_mult_le_two_zeta
#check @Riemann.proportion_of_mult_le_two
#check @Riemann.Blindness.Nstar_add_pred_mul_Nsc_le
#check @Riemann.starBound_of_mult_le
#check @Riemann.starBound_of_mult_le_three
#check @Riemann.Blindness.Nstar_add_pred_mul_Nsc_le_except
#check @Riemann.Blindness.Nstar_add_pred_mul_Nsc_le_of_except
#check @Riemann.Blindness.starBound_allows_any_multiplicity
#check @Riemann.Blindness.no_NscStd_coefficient_at_three
#check @Riemann.Blindness.haunted_atom_saturates
#check @Riemann.Blindness.three_mul_NscStd_eq_iff
#check @Riemann.Blindness.haunted_odd
#check @Riemann.Blindness.noSmallHaunted_succ_of_even
#check @Riemann.Blindness.ladder_sharp_at_odd
#check @Riemann.Blindness.Nsc_eq_NscStd_of_noHaunted
#check @Riemann.Blindness.noHaunted_of_mult_le_two
#check @Riemann.Blindness.noHaunted_not_mult_le_two
#check @Riemann.NoHaunted
#check @Riemann.proportion_of_noHaunted
#check @Riemann.proportion_of_noHaunted_zeta
#check @Riemann.Blindness.Nsc_eq_NscStd_iff_noHaunted
#check @Riemann.Blindness.hauntedCount
#check @Riemann.Blindness.NscStd_eq_Nsc_add_haunted
#check @Riemann.Blindness.Nsc_add_three_mul_haunted_le_N
#check @Riemann.Blindness.three_mul_NscStd_le_of_identity
#check @Riemann.Blindness.two_mul_haunted_add_NscStd_le_N
#check @Riemann.Blindness.two_mul_haunted_add_NscStd_eq_iff
#check @Riemann.Blindness.row_essentially_optimal
#check @Riemann.constFamily
#check @Riemann.baseline_cap
#check @Riemann.baseline_cap_witness
#check @Riemann.Blindness.cap_witness_respects_derived
#check @Riemann.Blindness.haunted_indistinguishable_from_triple
#check @Riemann.Blindness.noHaunted_of_allDistinct
#check @Riemann.Blindness.Noff_eq_zero_of_allDistinct
#check @Riemann.Blindness.noHaunted_not_imp_Noff_zero
#check @Riemann.Blindness.noHaunted_of_Noff_zero
#check @Riemann.Blindness.noHaunted_strictly_weaker_than_RH
#check @Riemann.HauntedDensity
#check @Riemann.proportion_of_hauntedDensity
#check @Riemann.hauntedDensity_of_offLineImport
#check @Riemann.certified_nsc_via_haunted
#check @Riemann.Blindness.pred_mul_haunted_add_NscStd_le_N
#check @Riemann.hauntedDensity_of_noSmallHaunted
#check @Riemann.Blindness.six_mul_haunted_add_N_le_Nstar
#check @Riemann.hauntedDensity_of_starBound
#check @Riemann.Blindness.six_mul_haunted_le_factMoment_three
#check @Riemann.Blindness.haunted_le_NscStd
#check @Riemann.Blindness.three_mul_haunted_le_N
#check @Riemann.Blindness.best_delta_is_from_110
#check @Riemann.certified_haunted
#check @Riemann.Family.oddAtoms
#check @Riemann.oddAtoms_ge_of_proportionStd
#check @Riemann.certified_atomCount
#check @Riemann.certified_oddAtoms
#check @Riemann.Blindness.oddAtoms_le_atomCount
#check @Riemann.Blindness.two_mul_haunted_add_atomCount_le_N
#check @Riemann.hauntedDensity_of_distinctZeros
#check @Riemann.certified_haunted_via_distinctZeros
#check @Riemann.Blindness.landau_ge_N_mul_sqrt
#check @Riemann.offline_via_xiPrime
#check @Riemann.certified_nsc_via_xiPrime
#check @Riemann.certified_nsc_via_noSmallHaunted
#check @Riemann.certified_nsc_ladder
#check @Riemann.certified_nsc_via_noSmallHaunted_seven
#check @Riemann.proportion_of_mult_le_zeta
#check @Riemann.mult_ladder_value
#check @Riemann.mult_ladder_no_gain
#check @Riemann.NoSmallHaunted.mono
#check @Riemann.noHaunted_iff_forall_noSmallHaunted
#check @Riemann.noSmallHaunted_strict
#check @Riemann.configAt_noSmallHaunted
#check @Riemann.noSmallHaunted_admits_offline
#check @Riemann.ZeroData.NscAny
#check @Riemann.ZeroData.NscStd_le_NscAny
#check @Riemann.ZeroData.NscAny_le_NscStd_add_Noff
#check @Riemann.ZeroData.NscAny_le_N
#check @Riemann.offline_roundtrip_loses
#check @Riemann.starBound_exchange_crossover
#check @Riemann.proportionStd_exchange_identity
#check @Riemann.offline_roundtrip_eq_iff
#check @Riemann.Blindness.distinctZeros
#check @Riemann.Blindness.atomCount_le_distinctZeros
#check @Riemann.Blindness.distinctZeros_le_atomCount_add_Noff
#check @Riemann.Blindness.offLine_bound_attained
#check @Riemann.Blindness.offLine_count_not_bounded_by_proximity
#check @Riemann.Blindness.Nstar_bound_attained
#check @Riemann.Blindness.mass_three_atom_attains_all
#check @Riemann.Blindness.haunted_chain_attains
#check @Riemann.Blindness.haunted_chain_attains_star_and_atoms
#check @Riemann.Blindness.atomCount_eq_card_profile
#check @Riemann.Blindness.hauntedCount_from_profile
#check @Riemann.Blindness.distinctZeros_not_profile_functional
#check @Riemann.Blindness.dictionary_bounds_attained
#check @Riemann.Blindness.minimal_haunted_configuration
#check @Riemann.Blindness.minimal_haunted_attained
#check @Riemann.Blindness.configAt_H
#check @Riemann.Blindness.offAt_configAt_self

-- SESSION 245: the four grade-A citations in CLAIMS.md that this file did not
-- guard.  All 96 cited names resolve today; these four were outside the audit
-- point, so a rename would have broken a claim without breaking a build.
-- `ceiling_law256` additionally pins the vendored zeta-23's reachability, which
-- `244` had to verify by hand.
#check @Riemann.ZeroData.Nsc_le_NscStd
#check @Riemann.Blindness.mul_NscStd_le_N_add_pred_mul_Nsc
#check @Riemann.routeIII_with_narrowBox
#check @Zeta23.PairCeiling.ceiling_law256

-- SESSION 335: what the whole moment family can and cannot compute.  `momentK`
-- is a functional of the ordinates with the functional exhibited, so nothing the
-- ordinates hide survives the family; and no single moment determines `N_sc`.
#check @Riemann.Blindness.momentK_eq_count_sum
#check @Riemann.Blindness.momentK_ordinate_functional
#check @Riemann.Blindness.not_momentK_computable_of_not_ordinate_functional
#check @Riemann.Blindness.hauntedCount_not_momentK_computable
#check @Riemann.Blindness.oddAbove_not_momentK_computable
#check @Riemann.Blindness.evenOnAt_not_momentK_computable
#check @Riemann.Blindness.offLineOnly_not_momentK_computable
#check @Riemann.Blindness.NscStd_not_momentK_computable
#check @Riemann.Blindness.momentK_zero
#check @Riemann.Blindness.momentK_one
#check @Riemann.Blindness.simple_chain_profile
#check @Riemann.Blindness.simple_chain_momentK
#check @Riemann.Blindness.simple_chain_Nsc
#check @Riemann.Blindness.pure_chain_momentK
#check @Riemann.Blindness.pure_chain_Nsc
#check @Riemann.Blindness.single_momentK_not_determine_Nsc

-- SESSION 336: a multiplicity cap does not bound `N_sc`, it computes it.  Two
-- hypothesis-free inequalities whose equality cases are the caps at 3 and 4, and
-- the composition with 334 -- the moment family's equality set is exactly where
-- three moments compute `N_sc`.
#check @Riemann.Blindness.Nsc_eq_sum_mass_one_nat
#check @Riemann.Blindness.one_le_H_of_mem
#check @Riemann.Blindness.cap_three_pointwise
#check @Riemann.Blindness.cap_three_pointwise_lt
#check @Riemann.Blindness.two_mul_Nsc_add_five_mul_N_le
#check @Riemann.Blindness.two_mul_Nsc_eq_iff
#check @Riemann.Blindness.momentK_charges_eq_iff_Nsc_computed
#check @Riemann.Blindness.cap_four_pointwise
#check @Riemann.Blindness.cap_four_pointwise_lt
#check @Riemann.Blindness.nine_mul_Nstar_add_atomCount_le
#check @Riemann.Blindness.nine_mul_Nstar_add_atomCount_eq_iff

-- SESSION 337: the two axioms are theorems.  `baseline_of_cumulative` moved from
-- Riemann/Proportion.lean to Riemann/Assumptions.lean so it sits above every
-- consumer of `baseline_zeta23`.  `go run tools/proportion.go` reports axioms: 0.
#check @Riemann.zetaNonempty
#check @Riemann.baseline_zeta23
#check @Riemann.baseline_of_cumulative

-- SESSION 338: the distinct-zeros route, priced and closed.  337's reachability
-- change surfaced zeta-23's unconditional point-count proportions; the dictionary
-- on disk converts them to at most c - 0.3275, which ties 0.6725 at c = 1.
#check @Riemann.Blindness.atomCount_of_distinctZeros_and_Noff
#check @Riemann.Blindness.distinct_route_margin
#check @Riemann.zeta23_GD_eq_of_HD
#check @Riemann.distinctZeros_route_dominated
#check @Riemann.distinctZeros_route_ties_at_one

-- SESSION 339: the on-line dictionary is an equality where 338's general one is
-- one-way.  A zero on the line is (1/2, γ), so its ordinate determines it, and
-- the point count partitions as on-line ordinates plus off-line points.
#check @Riemann.Blindness.onLineOrdinates_eq_onLinePoints
#check @Riemann.Blindness.offLinePoints
#check @Riemann.Blindness.onLineOrdinates_add_offLinePoints
#check @Riemann.Blindness.offLinePoints_le_Noff
#check @Riemann.Blindness.point_slack_exact

-- SESSION 341: where the ladder crosses the board.  The ceiling and the limit
-- were already on disk (ladder_lt_kappa 240, ladder_approaches_kappa 254); what is
-- new is the crossing law and the two thresholds it locates.
#check @Riemann.ladder_beats_iff
#check @Riemann.ladder_routeII_crossing_exact
#check @Riemann.ladder_beats_routeII_first_at_seven
#check @Riemann.ladder_routeIII_crossing_exact
#check @Riemann.ladder_beats_routeIII_first_at_fiftynine

-- SESSION 344: the cap identity at every bound.  336 shipped mass <= 3 and <= 4
-- and said "for no general m"; this is the general one, by Lagrange interpolation
-- on {1..b+1}.  The expansion into moments is NOT proved.
#check @Riemann.Blindness.capWitness
#check @Riemann.Blindness.cap_pointwise
#check @Riemann.Blindness.capWitness_eq
#check @Riemann.Blindness.capWitness_from_profile
#check @Riemann.Blindness.capWitness_needs_the_cap

-- SESSION 345: the expansion 344 left open, by a coefficient recursion rather
-- than elementary symmetric polynomials.  Under a cap at b+1, N_sc is a Z-linear
-- combination of momentK 0 .. momentK b, and those moments determine it.
#check @Riemann.Blindness.capCoeff
#check @Riemann.Blindness.capCoeff_eq_zero_of_gt
#check @Riemann.Blindness.capCoeff_prod
#check @Riemann.Blindness.momentK_cast
#check @Riemann.Blindness.capWitness_eq_sum_moments
#check @Riemann.Blindness.Nsc_from_moments
#check @Riemann.Blindness.Nsc_determined_by_moments_of_cap

-- SESSION 346: the uncapped question, answered.  Every ZeroData is capped by its
-- own N (H_le_N) and N is the moment at k = 1, so 345's capped theorems apply at
-- b = D.N.  The whole moment sequence determines N_sc.
#check @Riemann.Optimal.Nsc_determined_by_all_moments
#check @Riemann.Optimal.Nsc_from_moments_at_N

-- SESSION 347: both sides of the moment comparison in one currency.  The sequence
-- determines N_sc (346) and does not determine NscStd — witnessed by X's founding
-- pair, a haunted ordinate against a pure triple.
#check @Riemann.Blindness.NscStd_not_determined_by_all_moments
#check @Riemann.Blindness.Nsc_agrees_on_the_moment_blind_pair

-- SESSION 348: the recovery 347 left unproved.  Equal moment sequences force equal
-- mass counts at every j — Newton's recovery in this vocabulary, with the
-- coefficients never named.  Not equal ordinates: heights stay invisible.
#check @Riemann.Blindness.exists_poly_of_prod
#check @Riemann.Blindness.massCount
#check @Riemann.Blindness.massCount_one
#check @Riemann.Blindness.sum_prod_eq_sum_moments
#check @Riemann.Blindness.node_prod_pointwise
#check @Riemann.Blindness.node_const_ne_zero
#check @Riemann.Blindness.node_sum_eq
#check @Riemann.Blindness.massCount_determined_of_cap
#check @Riemann.Optimal.massCount_determined_by_all_moments

-- SESSION 349: what would suffice.  348's machinery run on onAt instead of H: the
-- on-line moments determine NscStd, with no hypothesis.  Not a route (onAt is not a
-- mu_T functional) but the exact name of the missing datum.
#check @Riemann.Blindness.sum_prod_eq_sum_weight_moments
#check @Riemann.Blindness.onCount
#check @Riemann.Blindness.onMoment
#check @Riemann.Blindness.node_prod_pointwise_range
#check @Riemann.Blindness.node_const_range_ne_zero
#check @Riemann.Blindness.on_node_sum_eq
#check @Riemann.Blindness.onCount_determined_of_cap
#check @Riemann.Blindness.NscStd_eq_onCount_one
#check @Riemann.Optimal.NscStd_determined_by_on_moments

-- SESSION 350: each moment family sees one ledger row and misses the other.  The
-- H-family determines N_sc and not NscStd (347/348); the onAt-family determines
-- NscStd and not N_sc, nor N — which pays 349's unwitnessed docstring claim.
#check @Riemann.Blindness.onMoment_from_onProfile
#check @Riemann.Blindness.Nsc_not_determined_by_on_moments

-- SESSION 351: the two families jointly.  Together they determine every ledger row
-- (N_off closes via Noff + sum onAt = N) and still not the profile — two two-atom
-- configurations share both marginals and differ in the joint.
#check @Riemann.Blindness.Noff_eq_sum_offAt
#check @Riemann.Blindness.Noff_add_onMoment_one
#check @Riemann.Blindness.profile_not_determined_by_both_families
#check @Riemann.Optimal.ledger_determined_by_both_moment_families

-- SESSION 353: two marginalisations of one object.  The profile's own marginals
-- (mass, off-line mass) lose NscStd; 351's (mass, on-line) pair does not, because
-- NscStd is a functional of the on-line marginal alone (349).
#check @Riemann.Blindness.NscStd_not_determined_by_profile_marginals
#check @Riemann.Blindness.marginal_pair_separates_only_NscStd

-- SESSION 354: the third pairing, and the survey of all three closes.  (on, off)
-- keeps N, N_off, NscStd and loses N-star and N_sc — both need mass = on + off per
-- ordinate, which is the pairing the coarsening discards.
#check @Riemann.Blindness.profile_snd_le_fst
#check @Riemann.Blindness.NscStd_from_on_marginal
#check @Riemann.Blindness.Noff_from_on_marginal
#check @Riemann.Blindness.N_from_on_marginals
#check @Riemann.Blindness.ledger_partly_determined_by_on_off_marginals
#check @Riemann.Blindness.Nstar_Nsc_not_determined_by_on_off_marginals

-- SESSION 358: the formalisable half of arXiv:2608.13637's section 1.4.  Superposing a
-- configuration with no on-line zeros leaves NscStd unchanged at ANY size, not merely
-- o(N); N_sc is not insensitive, and the same superposition drops it 1 -> 0.
#check @Riemann.Blindness.onAt_superpose
#check @Riemann.Blindness.onAt_eq_zero_of_not_mem
#check @Riemann.Blindness.NscStd_insensitive_to_offLine
#check @Riemann.Blindness.onAt_eq_zero_of_offLine
#check @Riemann.Blindness.offLine_pair_no_online
#check @Riemann.Blindness.Nsc_sensitive_to_offLine
#check @Riemann.Blindness.NscStd_insensitive_offLine_witness

-- SESSION 360: the second clause of arXiv:2608.13637 section 1.4.  The certified row
-- is satisfiable with off-line zeros at positive, non-decaying density — one haunted
-- ordinate among four simple ones, NscStd/N = 5/7 and Noff/N = 2/7.
#check @Riemann.constFamily_proportionStd
#check @Riemann.mixed_chain_counts
#check @Riemann.proportionStd_admits_positive_offline_density

-- SESSION 362: the 13/18 row of arXiv:2608.13637 section 7.3 against this project's
-- proved ceilings.  Above Route III and above the certified row; out of reach of both
-- currencies the project owns, at every m and every beta.
#check @Riemann.HL_row_on_the_board
#check @Riemann.ladder_cannot_reach_HL_row
#check @Riemann.offLine_currency_cannot_reach_HL_row

-- SESSION 363: 361's analogy, refuted in its naive reading.  The three global numbers
-- N, Nstar, Noff (and the on-line total they determine) do not fix NscStd, so the
-- paper's certificate class is strictly richer than that shadow of it.
#check @Riemann.Blindness.NscStd_not_determined_by_two_moments_and_split

-- SESSION 365: the on-line side of the chain.  349's capped onCount determinacy, taken
-- uncapped, plus a fiberwise partition of the ordinates by onAt, gives oddAtoms.
-- onLineOrdinates is NOT done.
#check @Riemann.Blindness.oddAtoms_eq_sum_onCount
#check @Riemann.Optimal.onCount_determined_by_on_moments
#check @Riemann.Optimal.oddAtoms_determined_by_on_moments

-- SESSION 366: the chain's fourth term, and the on-line family's reach.  onLineOrdinates
-- by 365's argument with the non-zero fibres; atomCount = onMoment 0 from the definition.
-- The family reaches the chain from NscStd upward and stops below it (350).
#check @Riemann.Blindness.atomCount_eq_onMoment_zero
#check @Riemann.Blindness.onLineOrdinates_eq_sum_onCount
#check @Riemann.Optimal.onLineOrdinates_determined_by_on_moments
#check @Riemann.Optimal.chain_upper_four_determined_by_on_moments

-- SESSION 367: 366's picture corrected.  even_offAt makes H and onAt share parity, so
-- oddAtoms counts odd-MASS ordinates and both families reach it.  With 347 below and the
-- new negative above, the H-family's reach along the chain alternates.
#check @Riemann.Blindness.oddAtoms_eq_odd_H
#check @Riemann.Blindness.oddAtoms_eq_sum_massCount
#check @Riemann.Blindness.onLineOrdinates_not_determined_by_all_moments
#check @Riemann.Optimal.oddAtoms_determined_by_all_moments

-- 368: the H-family's reach IS the mass multiset, and the on-line family's IS the on-counts.
-- Two equivalences; each converse is the weighted fiberwise sum.  Explains 367.
#check @Riemann.Blindness.momentK_eq_sum_massCount
#check @Riemann.Blindness.onMoment_eq_sum_onCount
#check @Riemann.Optimal.moment_blind_iff_massCount
#check @Riemann.Optimal.on_moment_blind_iff_onCount

-- 369: the ledger needs five named scalars, not two infinite families.  One of the five
-- is shown necessary; the other four are open.
#check @Riemann.Blindness.ledger_determined_by_five_scalars
#check @Riemann.Blindness.onCount_one_cannot_be_dropped

-- 370: 369's open necessity question.  Three of the four were already on disk; only the
-- N case needed a new pair, because N moving is what breaks the Noff -> onMoment 1 bridge.
#check @Riemann.Blindness.momentK_one_cannot_be_dropped
#check @Riemann.Blindness.momentK_two_cannot_be_dropped
#check @Riemann.Blindness.massCount_one_cannot_be_dropped

-- 372: minimality is class-relative.  Unrestricted, one number does it.
#check @Riemann.Blindness.ledgerCode
#check @Riemann.Blindness.ledgerCode_eq_iff

-- 374: the Nsc row's "no star bound" annotation, priced.  An unconditional
-- N* <= c*N with c < 793/400 beats the certified route; tight at the mass-3 haunted atom.
#check @Riemann.ZeroData.six_mul_NscStd_le
#check @Riemann.Blindness.star_route_pointwise
#check @Riemann.Blindness.star_route_beats_iff
#check @Riemann.Blindness.star_route_threshold_zeta
#check @Riemann.Blindness.star_route_attained

-- 377: 374's star route reconciled with 241's.  Same currency, different trades; they cross
-- at C = 1393/1000, both paying 607/1000.
#check @Riemann.Blindness.star_currency_crossover
#check @Riemann.Blindness.star_currency_crossover_zeta

-- 382: the star bound at a ladder rung.  Coefficient m(m-1), not the fixed 6.
#check @Riemann.Blindness.mass_card_le_Nstar_sub_N
#check @Riemann.Blindness.haunted_rung_star
#check @Riemann.Blindness.star_rung_threshold
#check @Riemann.Blindness.star_rung_threshold_zeta

-- 383: the rung combination lifted to Family level; it joins the HauntedDensity hub.
#check @Riemann.hauntedDensity_of_starBound_at_rung

-- 384: the third rung combination.  All three non-ladder suppliers compose with the ladder.
#check @Riemann.Blindness.haunted_rung_deficit
#check @Riemann.hauntedDensity_of_distinctZeros_at_rung

-- 385: both rung coefficients are attained at every odd rung by the mass-m haunted atom.
#check @Riemann.Blindness.rung_coefficients_attained

-- 386: the rung at every moment order, and one atom saturates the whole family.
#check @Riemann.Blindness.pow_sub_self_mono
#check @Riemann.Blindness.mass_card_le_momentK_sub_N
#check @Riemann.Blindness.haunted_rung_momentK
#check @Riemann.Blindness.rung_momentK_attained

-- 387: the on-line family cannot see haunting; 386's first direction is closed.
#check @Riemann.Blindness.hauntedCount_not_determined_by_on_moments

-- 390: the last two internal channels closed — odd atoms circular, factorial moments covered.
#check @Riemann.Blindness.hauntedCount_le_oddAtoms
#check @Riemann.Blindness.oddAtoms_bound_cannot_beat_baseline
#check @Riemann.Blindness.factMoment_atom

-- 392: the bridge levinson_montgomery -> OffTransfer, modulo LogSmall.
#check @Riemann.LogSmall
#check @Riemann.offTransfer_of_levinsonMontgomery

-- 395: LogSmall discharged from vendored RvM; OffTransfer for zeta/xi' is now a theorem.
#check @Riemann.logSmall_of_rvm_main
#check @Riemann.logSmall_zeta
#check @Riemann.offTransfer_zeta_xiPrime

-- 401: the star rung's termwise charge is exact only at mass m.
#check @Riemann.Blindness.mass_cost_eq_iff

-- 402: the strict monotonicity 401 named, and the general-k uniqueness it unlocks.
#check @Riemann.Blindness.pow_sub_self_strict
#check @Riemann.Blindness.pow_cost_eq_iff

-- 404: the rung bound's global equality characterisation.
#check @Riemann.Blindness.self_eq_pow_iff
#check @Riemann.Blindness.mass_card_eq_momentK_iff

-- 405: the other two rung currencies' equality cases, and their agreement.
#check @Riemann.Blindness.mass_card_le_N_sub_atomCount
#check @Riemann.Blindness.mass_card_eq_N_sub_atomCount_iff
#check @Riemann.Blindness.mass_card_eq_Nstar_sub_N_iff
#check @Riemann.Blindness.rung_currencies_agree

-- 406: the k-th moment bound as a HauntedDensity supplier.
#check @Riemann.Blindness.momentK_mono_order
#check @Riemann.Family.MomentBound
#check @Riemann.momentBound_two_iff_starBound
#check @Riemann.starBound_of_momentBound
#check @Riemann.hauntedDensity_of_momentBound_at_rung
#check @Riemann.moment_rung_beats_star_rung_iff

-- 407: the multiplicity cap as a MomentBound input, and what it buys.
#check @Riemann.Blindness.momentK_le_of_multiplicity_le
#check @Riemann.momentBound_of_multiplicity_le
#check @Riemann.moment_cap_rate_eq_star_rate

-- 408: the cap family's moment rates against its star rate, both directions.
#check @Riemann.moment_cap_rate_ge_star_rate
#check @Riemann.moment_cap_rate_gt_star_rate

-- 412: simple zeros charged 1 at every order; the sharpened star bound.
#check @Riemann.Blindness.momentK_add_mul_Nsc_le
#check @Riemann.momentBound_of_multiplicity_and_proportion
#check @Riemann.moment_proportion_rate_independent_of_order

-- 414: the cap bound's equality case.
#check @Riemann.Blindness.momentK_add_mul_Nsc_eq_iff

-- 415: twoAtom's masses, and 414's equality case attained with both present.
#check @Riemann.Blindness.twoAtom_H
#check @Riemann.Blindness.twoAtom_ordinates_toFinset
#check @Riemann.Blindness.momentK_cap_bound_attained_mixed

-- 416: the arbitrary-arity configuration builder and its profile.
#check @Riemann.Blindness.nAtom
#check @Riemann.Blindness.nAtom_H
#check @Riemann.Blindness.nAtom_profile

-- 417: which multisets are profiles, and the first consequence.
#check @Riemann.Blindness.profile_realisable
#check @Riemann.Blindness.exists_atomCount_N

-- 418: the counting chain is sharp in both directions.
#check @Riemann.Blindness.chain_all_strict
#check @Riemann.Blindness.chain_all_collapse

-- 419: mass_charges_every_class is attained and its weights are maximal.
#check @Riemann.Blindness.mass_charges_sharp
#check @Riemann.Blindness.mass_charges_coefficients_maximal

-- 422: found by the three-term search — haunted and off-line-only both cost two.
#check @Riemann.Blindness.two_mul_haunted_add_two_mul_offLineOnly_le_Noff

-- 424: found by the Farkas step — strengthens Noff_add_oddAtoms_le_N.
#check @Riemann.Blindness.Noff_add_onLineOrdinates_le_N

-- 425: the off-line analogue of mass_charges_every_class, found by the LP.
#check @Riemann.Blindness.Noff_add_onLine_charges_le_N

-- 426: the moment ladder pays the off-line mass at every step.
#check @Riemann.Blindness.momentK_add_Noff_le_momentK_succ
