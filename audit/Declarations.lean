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
