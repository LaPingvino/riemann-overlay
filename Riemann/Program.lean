/-
# The dependency graph of §6, assembled

Each theorem is one arrow of the §6 graph, with the open problems **and the
literature bridges that cannot be safely axiomatised** (ISSUES.md #8) carried
as hypotheses.  All are proved; what is checked is that the arrows compose.

Nothing here assumes an open problem.  Where an arrow does not compose, that
is recorded in `ISSUES.md` rather than patched.
-/
import Riemann.Assumptions

open Filter

namespace Riemann

/-! ### Route I -/

/-- **[OPEN 0] with `c₀ ≤ 0.8` ⟹ a positive proportion.** -/
theorem routeI (F : Family) (c₀ : ℝ) (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 0.8)
    (h : EffectiveFujii F.toCounts c₀) : ∃ κ > 0, F.toCounts.Proportion κ :=
  positive_proportion_of_le hc0 hc h

/-- **[OPEN 0] with `c₀ ≤ 0.33` ⟹ the record falls.** -/
theorem routeI_record (F : Family) (c₀ : ℝ) (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 0.33)
    (h : EffectiveFujii F.toCounts c₀) :
    ∃ κ, 0.6725 < κ ∧ F.toCounts.Proportion κ :=
  beats_record_of_le hc0 hc h

/-- **[OPEN 0] + [OPEN 0′].**  The close-pair subtraction relaxes the demand
on the Fujii constant by exactly `c₁` — *at the same `λ`*, which is the whole
content of ISSUES.md #3. -/
theorem routeI_closePairs (closePairs : ℝ → ℝ → ℝ) (F : Family) (c₀ c₁ : ℝ)
    (hbk : ClosePairBookkeeping closePairs F)
    (h₀ : EffectiveFujii F.toCounts c₀)
    (h₁ : ClosePairLowerBound closePairs F (9/10) c₁)
    (hgood : Cbound c₀ (9/10) - c₁ < 2) : ∃ κ > 0, F.toCounts.Proportion κ := by
  refine ⟨2 - (Cbound c₀ (9/10) - c₁), by linarith, ?_⟩
  exact Counts.proportion_of_starBound (hbk c₀ (9/10) c₁ h₀ (by norm_num) h₁)

/-- Route I for the zeta family, with the bookkeeping axiom discharged. -/
theorem routeI_closePairs_zeta (c₀ c₁ : ℝ)
    (h₀ : EffectiveFujii zetaFamily.toCounts c₀)
    (h₁ : ClosePairLowerBound closePairsZeta zetaFamily (9/10) c₁)
    (hgood : Cbound c₀ (9/10) - c₁ < 2) :
    ∃ κ > 0, zetaFamily.toCounts.Proportion κ :=
  routeI_closePairs closePairsZeta zetaFamily c₀ c₁ fujii_closePair_bookkeeping h₀ h₁ hgood

/-! ### Route II -/

/-- **[OPEN B] is closed** — what zeta-23 actually gives for `ξ'`. -/
theorem routeII_xiPrime : xiPrimeFamily.toCounts.Proportion 0.85838 :=
  zeta23_xiPrime

/-- **The Route II gap, isolated.**  Farmer–Ki turns `ξ'`-mass near the line
into `ζ`-close-pairs, but at a `λ` *it* chooses, whereas
`routeI_closePairs` needs `λ = 9/10`.  The two do not meet: this theorem
produces an existential `λ`, and there is no arrow from here into Route I
without a `λ`-uniform version (ISSUES.md #3). -/
theorem routeII_gap (closePairs : ℝ → ℝ → ℝ) (F F' : Family) (M : ℝ → ℝ)
    (hfk : FarmerKiTransfer closePairs F F') (hd : DensityNearLine F' M) :
    ∃ lam > 0, ∃ c₁ > 0, ClosePairLowerBound closePairs F lam c₁ :=
  hfk M hd

/-- **[OPEN B″] composes** (Errata 1, E3).  With the `λ`-uniform form of
Farmer–Ki, the Route II output lands at the `λ` Route I consumes, and the
chain closes.  This is the point of the new gap shape: compare
`routeII_gap`, which produces a `λ` nobody ordered. -/
theorem routeII_via_B'' (closePairs : ℝ → ℝ → ℝ) (F F' : Family) (M : ℝ → ℝ)
    (c₀ : ℝ) (hbk : ClosePairBookkeeping closePairs F)
    (h₀ : EffectiveFujii F.toCounts c₀)
    (hB : LambdaUniformFarmerKi closePairs F F' (6/10) (9/10))
    (hd : DensityNearLine F' M)
    (hgood : ∀ c₁ > 0, Cbound c₀ (9/10) - c₁ < 2) :
    ∃ κ > 0, F.toCounts.Proportion κ := by
  obtain ⟨c₁, hc₁, huni⟩ := hB M hd
  have h₁ : ClosePairLowerBound closePairs F (9/10) c₁ :=
    huni (9/10) (by constructor <;> norm_num)
  exact routeI_closePairs closePairs F c₀ c₁ hbk h₀ h₁ (hgood c₁ hc₁)

/-! ### Route III -/

/-- **Route III, as far as it composes.**  [OPEN A′] gives a narrow box *with
an exceptional set*; BGST assumes one *without*.

⚠️ **Scope corrected (SESSION 086).**  This docstring read "this is the only
arrow that survives", which is false as written — `routeIII_with_narrowBox` and
`routeIII_via_A''` below are two further arrows.  The true statement is that
this is the only arrow that survives **with no hypothesis beyond
`DensityNearLine`**; the other two each buy their arrow with an extra
assumption (`BGSTNarrowBox`, and `NarrowBoxTolerant` plus a fitting condition).
An unscoped absolute in a load-bearing docstring is the defect class that cost
the project the `Nsc` row for many cycles (`SURPRISES` S34), which is why the
scope is now written out rather than left to the reader.

The arrow: `DensityNearLine F M` ⟹ `NarrowBoxExc F δ (M δ)`. -/
theorem routeIII_partial (F : Family) (M : ℝ → ℝ) (hA : DensityNearLine F M)
    (δ : ℝ) (hδ : 0 < δ) : NarrowBoxExc F δ (M δ) := by
  filter_upwards [hA δ hδ] with T hT
  refine le_trans ?_ hT
  have hle : (F.D T).Z.filter (fun p => δ / Real.log T < |p.1 - 1/2|)
      ≤ (F.D T).Z.filter (fun p => δ / Real.log T ≤ |p.1 - 1/2|) :=
    Multiset.monotone_filter_right _ (fun p hp => le_of_lt hp)
  exact_mod_cast Multiset.card_le_card hle

/-- **What Route III would need**: the exceptional-set-free narrow box, i.e.
the shape BGST actually proves. -/
theorem routeIII_with_narrowBox (F : Family) (hbg : BGSTNarrowBox F)
    (h : ∀ b > 0, NarrowBox F b) :
    ∀ ε > 0, F.toCounts.StarBound (4/3 + ε) := by
  intro ε hε
  obtain ⟨b, hb, himp⟩ := hbg ε hε
  exact himp (h b hb)

/-- **[OPEN A″] composes** (Errata 1, E4) — but only with an explicit
fitting condition.  `NarrowBoxTolerant` hands us a box width `b` and an
exceptional allowance `η`; [OPEN A′] must then be *small at that particular
scale*: `M δ ≤ η` for some `δ ≤ b`.  That coupling is the honest content of
"C determined by the quality of E(t,T) and M(t,T)" — and note it is the same
"constant produced at a scale the consumer did not order" pattern as
ISSUES.md #3. -/
theorem routeIII_via_A'' (F : Family) (M : ℝ → ℝ) (hA : DensityNearLine F M)
    (htol : NarrowBoxTolerant F)
    (hfit : ∀ b > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ ≤ b ∧ M δ ≤ η) :
    ∀ ε > 0, F.toCounts.StarBound (4/3 + ε) := by
  intro ε hε
  obtain ⟨b, hb, η, hη, himp⟩ := htol ε hε
  obtain ⟨δ, hδ, hδb, hMδ⟩ := hfit b hb η hη
  exact himp ((routeIII_partial F M hA δ hδ).mono hδb hMδ)

/-! ### Past the second-moment floor -/

/-- **[OPEN D] ⟹ the Tentative Theorem**: `100%` of the zeros simple and on
the critical line. -/
theorem tentativeTheorem (F : Family) (h : ExtendedSupport F) :
    ∀ ε > 0, F.toCounts.Proportion (1 - ε) := by
  intro ε hε
  have := Counts.proportion_of_starBound (h ε hε)
  intro ε' hε'
  filter_upwards [this ε' hε'] with T hT
  linarith [hT]

end Riemann
