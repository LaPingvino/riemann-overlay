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
