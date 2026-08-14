/- Session 003: proof that the zeta-23 import is live — the headline theorems
   and the ξ′ pair-correlation layer are reachable from this project. -/
import Zeta23.FinalMult
import Zeta23.ThmD.Mult
import Zeta23.XiPrime.Final

-- the ζ baseline (Theorem D, multiplicity-aware, cumulative)
#check @Zeta23.ThmD.thmD₀_simple_mult_cumulative
#print axioms Zeta23.ThmD.thmD₀_simple_mult_cumulative

-- the ξ′ result ([OPEN B])
#check @Zeta23.XiPrime.headlineW_unconditional
#print axioms Zeta23.XiPrime.headlineW_unconditional

-- the second-moment layer Route II wants (ISSUES #11)
#check @Zeta23.XiPrime.jWin
#check @Zeta23.XiPrime.D1
#check @Zeta23.XiPrime.cWin
#check @Zeta23.XiPrime.kappaXi
