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
