/-
# The gaps of the program document, stated

A family of zero data indexed by height `T`, and one Lean `Prop` for each
bracketed gap of the program document.  No axioms here — they live in
`Assumptions.lean`, and the assembly in `Program.lean`.  The one theorem in
this file, `Family.offline_le`, is proved and axiom-free; it sits here
because it is about `Family`.

The point of writing the statements down is that every arrow of the §6
dependency graph is forced to name its quantifiers.  Two of them only
typecheck with side conditions the prose leaves implicit; those are marked
`NOTE` and filed in `ISSUES.md`.

[OPEN A] (uniform Ki–Kim–Lee for the de Bruijn–Newman flow) is *not* stated
formally: it is a statement about `H_t`, and formalising the heat-flow
deformation of `ξ` is a project in itself.  Only its deliverable, the
zero-density consequence [OPEN A′], appears here.
-/
import Riemann.Fujii
import Riemann.Fiber

open Filter

namespace Riemann

/-! ### From a family of zero data to counting functions -/

/-- A family of zero data: `D T` is the zero multiset up to height `T`. -/
structure Family where
  D : ℝ → ZeroData
  /-- The window is eventually nonempty. -/
  nonempty : ∀ᶠ T in atTop, 0 < (D T).N

namespace Family

variable (F : Family)

noncomputable def Nz (T : ℝ) : ℝ := ((F.D T).N : ℝ)
noncomputable def Ns (T : ℝ) : ℝ := ((F.D T).Nstar : ℝ)
noncomputable def Nsc (T : ℝ) : ℝ := ((F.D T).Nsc : ℝ)
noncomputable def Noff (T : ℝ) : ℝ := ((F.D T).Noff : ℝ)
/-- The *standard* count (multiplicity one, on the line) — the literature's
notion, and zeta-23's `N0simple`.  See `Nsc` for the project's stronger one. -/
noncomputable def NscStd (T : ℝ) : ℝ := (((F.D T).NscStd : ℕ) : ℝ)

/-- The counting functions of a family satisfy the hypotheses of
`Riemann.Counts`: Proposition 1 and the floor `N⊛ ≥ N` are the theorems of
`Basic.lean`, transported along `ℕ ↪ ℝ`. -/
noncomputable def toCounts : Counts where
  Nz := F.Nz
  Ns := F.Ns
  Nsc := F.Nsc
  pos := by
    filter_upwards [F.nonempty] with T hT
    unfold Family.Nz
    exact_mod_cast hT
  prop1 := by
    intro T
    have := ZeroData.prop1 (F.D T)
    unfold Family.Nz Family.Ns Family.Nsc
    exact_mod_cast this
  floor := by
    intro T
    have := ZeroData.N_le_Nstar (F.D T)
    unfold Family.Nz Family.Ns
    exact_mod_cast this

/-- **(★) caps the off-line zeros too.**  This is `N_add_Noff_le_Nstar`
transported: a bound `N⊛ ≤ C·N` forces `N_off ≤ (C-1)·N`.  With `C < 2` this
is already a nontrivial unconditional zero-density statement — the "narrow
box" input that Route III wants comes for free once Route I or II delivers.

Proved, no axioms. -/
theorem offline_le {C : ℝ} (h : F.toCounts.StarBound C) :
    ∀ ε > 0, ∀ᶠ T in atTop, F.Noff T ≤ (C - 1 + ε) * F.Nz T := by
  intro ε hε
  filter_upwards [h ε hε] with T hT
  have hbase : F.Nz T + F.Noff T ≤ F.Ns T := by
    have := ZeroData.N_add_Noff_le_Nstar (F.D T)
    unfold Family.Nz Family.Ns Family.Noff
    exact_mod_cast this
  have : F.Ns T ≤ (C + ε) * F.Nz T := hT
  linarith

/-- **The two notions are linked by `(★)` itself** (ISSUES.md #13, resolved).
`NscStd - Nsc ≤ N⊛ - N`, so a bound `N⊛ ≤ C·N` pins the discrepancy at
`(C-1)·N`.

Consequence for the interface: an external result stated for `NscStd`
(zeta-23's `N0simple`, GLSS's `N_sc`) transfers to the project's stronger
`Nsc` **at a cost of `C - 1`** — and therefore transfers usefully only once
`(★)` is known with `C < 2 - 0.6725 + ... `, concretely `C < 1.6725` for the
zeta-23 baseline to say anything at all about `Nsc`.  Today `C = 2` (nothing
proved), so the baseline and the routes' output are **not comparable**, and
they become comparable exactly when the program delivers its first nontrivial
constant.  That is a statement about the map, not a convention. -/
theorem nscStd_le_nsc_add {C : ℝ} (h : F.toCounts.StarBound C) :
    ∀ ε > 0, ∀ᶠ T in atTop, F.NscStd T ≤ F.Nsc T + ((C - 1 + ε) / 6) * F.Nz T := by
  intro ε hε
  filter_upwards [h ε hε] with T hT
  have hbase : 6 * F.NscStd T + F.Nz T ≤ 6 * F.Nsc T + F.Ns T := by
    have := ZeroData.six_mul_NscStd_le (F.D T)
    unfold Family.NscStd Family.Nsc Family.Ns Family.Nz
    exact_mod_cast this
  have : F.Ns T ≤ (C + ε) * F.Nz T := hT
  linarith

end Family

/-- The literature's row of the ledger: a proportion bound on the **standard**
count `NscStd` (multiplicity one, on the line).  `Counts.Proportion` is the
project's row, on the stronger `Nsc`.  `nsc_of_nscStd` is the bridge, and it
costs `(C-1)/2`. -/
def Family.ProportionStd (F : Family) (κ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, (κ - ε) * F.Nz T ≤ F.NscStd T

/-- `N(T) ≥ 0` — it is a cardinality. -/
lemma Family.Nz_nonneg (F : Family) (T : ℝ) : 0 ≤ F.Nz T := by
  unfold Family.Nz; positivity

/-- **`ProportionStd` is monotone in the constant.**  A larger certified
proportion implies every smaller one — so two `ProportionStd` axioms about the
same family are never independent: the weaker is a theorem. -/
theorem Family.ProportionStd.mono {F : Family} {κ₁ κ₂ : ℝ} (hle : κ₁ ≤ κ₂)
    (hp : F.ProportionStd κ₂) : F.ProportionStd κ₁ := by
  intro ε hε
  filter_upwards [hp ε hε] with T hT
  have := F.Nz_nonneg T
  nlinarith [hT, this]

/-- **An off-line import**: a bound `N_off ≤ (β + o(1))·N`.  This is the currency
a zero-density statement pays in, and — by `proportion_of_offLineImport` — the
currency the `Nsc` row buys in. -/
def OffLineImport (F : Family) (β : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, F.Noff T ≤ (β + ε) * F.Nz T

/-- **The `Nsc` row, priced against an off-line import.**

`Blindness.two_mul_NscStd_le_Noff_add_two_mul_Nsc` is `2·(NscStd − Nsc) ≤ N_off`,
axiom-free.  So a `ProportionStd κ` together with `N_off ≤ (β + o(1))·N` gives
`Proportion (κ − β/2)` — **every point of off-line control is worth half a point
of the project's own row.**

At `β = 1` this is the unconditional `certified_nsc_unconditional`
(`κ − 1/2`); any genuine off-line bound improves on it linearly. -/
theorem proportion_of_offLineImport {F : Family} {κ β : ℝ}
    (hstd : F.ProportionStd κ) (hoff : OffLineImport F β) :
    F.toCounts.Proportion (κ - β / 2) := by
  intro ε hε
  filter_upwards [hstd (ε / 2) (by linarith), hoff (ε / 2) (by linarith),
    F.toCounts.pos] with T hT hO hpos
  have hpos' : 0 < F.Nz T := hpos
  have hbase : 2 * F.NscStd T ≤ F.Noff T + 2 * F.Nsc T := by
    have := Blindness.two_mul_NscStd_le_Noff_add_two_mul_Nsc (F.D T)
    unfold Family.NscStd Family.Noff Family.Nsc
    exact_mod_cast this
  show κ - β / 2 - ε ≤ F.Nsc T / F.Nz T
  rw [le_div_iff₀ hpos']
  nlinarith [hT, hO, hbase, hpos']

/-- **Levinson–Montgomery, with the `O(log T)` absorbed into `o(N)`.**  The
axiom `levinson_montgomery` gives `|N_off' − N_off| ≤ c·log T`; turning that
into this `Prop` needs `log T = o(N(T))`, which is Riemann–von Mangoldt and is
*not* in the registers.  Carried as a hypothesis, never an axiom. -/
def OffTransfer (F F' : Family) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, F.Noff T ≤ F'.Noff T + ε * F.Nz T

/-- **The two families' zero counts agree to first order.**  Classical for `ζ`
and `ξ'`, and **the missing ingredient**: `xiPrimeFamily` is an opaque axiom with
no stated relation to `zetaFamily`, so nothing in the development connects their
`Nz`.  Carried as a hypothesis, never an axiom. -/
def NzComparable (F F' : Family) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, F'.Nz T ≤ (1 + ε) * F.Nz T

/-- **Route II, priced in ledger currency.**  A `Proportion κ'` for the
derivative family converts to an off-line import for the base family: the
derivative's simple on-line zeros crowd out its off-line ones
(`Blindness.Nsc_add_Noff_le_N`), and the two transfer hypotheses carry that
across.

With zeta-23's `ξ'` value `κ' = 0.85838` this is `β = 0.14162`, and
`proportion_of_offLineImport` then prices the `Nsc` row at
`0.6725 − 0.07081 = 0.60169` — **provided both hypotheses are supplied.** -/
theorem offLineImport_of_derivative {F F' : Family} {κ' : ℝ}
    (hκ0 : 0 ≤ κ') (hκ1 : κ' ≤ 1) (hp : F'.toCounts.Proportion κ')
    (htr : OffTransfer F F') (hcmp : NzComparable F F') :
    OffLineImport F (1 - κ') := by
  intro ε hε
  have hδpos : 0 < min (ε / 8) 1 := lt_min (by linarith) one_pos
  filter_upwards [hp _ hδpos, htr _ hδpos, hcmp _ hδpos,
    F.toCounts.pos, F'.toCounts.pos] with T hP hT hC hpos hpos'
  set δ := min (ε / 8) 1 with hδ
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδe : δ ≤ ε / 8 := min_le_left _ _
  have hposF : 0 < F.Nz T := hpos
  have hposF' : 0 < F'.Nz T := hpos'
  have hNsc' : (κ' - δ) * F'.Nz T ≤ F'.Nsc T := by
    have hP' : κ' - δ ≤ F'.Nsc T / F'.Nz T := hP
    rw [le_div_iff₀ hposF'] at hP'
    exact hP'
  have hdisj : F'.Nsc T + F'.Noff T ≤ F'.Nz T := by
    have := Blindness.Nsc_add_Noff_le_N (F'.D T)
    unfold Family.Nsc Family.Noff Family.Nz
    exact_mod_cast this
  have s1 : F'.Noff T ≤ (1 - κ' + δ) * F'.Nz T := by nlinarith [hdisj, hNsc']
  have hnn : 0 ≤ 1 - κ' + δ := by linarith
  have s2 : (1 - κ' + δ) * F'.Nz T ≤ (1 - κ' + δ) * ((1 + δ) * F.Nz T) :=
    mul_le_mul_of_nonneg_left hC hnn
  have s3 : F.Noff T ≤ (1 - κ' + δ) * ((1 + δ) * F.Nz T) + δ * F.Nz T := by linarith
  have s4 : (1 - κ' + δ) * (1 + δ) + δ ≤ 1 - κ' + ε := by nlinarith
  nlinarith [s3, s4, hposF]

/-- **The literature's row transfers to the project's row with NO star bound.**

`nscStd_le_nsc_add` above costs `(C-1)/6` and is therefore vacuous until `(★)`
is known with some `C < 2`; today nothing is proved and that bridge says
nothing.  This one costs nothing at all:
`Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc` is `3·NscStd ≤ N + 2·Nsc`,
axiom-free and unconditional, because a *haunted* atom has even nonzero
off-line part and hence mass at least `3` — it consumes three zeros of `N`
while contributing one to `NscStd`.

Consequence: `ProportionStd κ` gives `Proportion ((3κ − 1)/2)` outright.  The
bound is **tight**: `s` simple atoms and `h` haunted atoms of mass `3` give
`NscStd/N = (s+h)/(s+3h)` and `Nsc/N = s/(s+3h)`, and the constraint binds. -/
theorem proportion_of_proportionStd {F : Family} {κ : ℝ} (h : F.ProportionStd κ) :
    F.toCounts.Proportion ((3 * κ - 1) / 2) := by
  intro ε hε
  filter_upwards [h (2 * ε / 3) (by linarith), F.toCounts.pos] with T hT hpos
  have hbase : 3 * F.NscStd T ≤ F.Nz T + 2 * F.Nsc T := by
    have := Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc (F.D T)
    unfold Family.NscStd Family.Nsc Family.Nz
    exact_mod_cast this
  have hpos' : 0 < F.Nz T := hpos
  show (3 * κ - 1) / 2 - ε ≤ F.Nsc T / F.Nz T
  rw [le_div_iff₀ hpos']
  linarith

/-! ### The gaps -/

/-- **[OPEN 0′] — a positive proportion of close pairs.**  A lower bound
`(2/λ)∫₀^λ 𝒩(α)dα ≥ c₁·N(T)` at a fixed normalised spacing `λ`;
`closePairs lam T` abstracts the left-hand side.

NOTE (ISSUES.md #3).  In the identity of Proposition 2 this quantity is
*subtracted*, so it improves `(★)` to `Cbound c₀ λ - c₁`.  The prose says it
"subtracts `c₁` directly from `C`" — true only at the *same* `λ` at which
`Cbound` is optimised.  That is a real constraint: `c₁` must be delivered at
`λ ≈ 0.6–0.9`, not at an arbitrarily small `λ`. -/
def ClosePairLowerBound (closePairs : ℝ → ℝ → ℝ) (F : Family) (lam c₁ : ℝ) : Prop :=
  0 < c₁ ∧ ∀ ε > 0, ∀ᶠ T in atTop, c₁ * F.Nz T - ε ≤ closePairs lam T

/-- **[OPEN A′] — the dynamically produced zero-density theorem.**  An
off-line zero at horizontal distance `δ/log T` is destroyed by the heat flow
by time `≈ cδ²`; the count of survivors is `M δ · N(T)`. -/
def DensityNearLine (F : Family) (M : ℝ → ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ T in atTop,
    ((Multiset.card ((F.D T).Z.filter fun p => δ / Real.log T ≤ |p.1 - 1/2|) : ℕ) : ℝ)
      ≤ M δ * F.Nz T

/-- **The narrow-box hypothesis** (BGST, arXiv:2501.14545, 2603.28104): *all*
zeros lie within `b/log T` of the critical line.

NOTE (ISSUES.md #1, Doubt 3).  Compare with `DensityNearLine`: this is a
universally quantified statement with **no exceptional set**, while [OPEN A′]
delivers a bound on an exceptional set.  The two shapes do not match; the
Route III assembly needs the BGST proof to tolerate an exceptional set, or a
strengthened [OPEN A″].  This is the predicted bin-3 hole and it is real. -/
def NarrowBox (F : Family) (b : ℝ) : Prop :=
  ∀ᶠ T in atTop, ∀ p ∈ (F.D T).Z, |p.1 - 1/2| ≤ b / Real.log T

/-- The narrow box with an exceptional set of relative size `η`: the shape
[OPEN A′] can actually deliver.  `NarrowBox F b = NarrowBoxExc F b 0` in
spirit; the BGST theorems are stated for the former. -/
def NarrowBoxExc (F : Family) (b η : ℝ) : Prop :=
  ∀ᶠ T in atTop,
    ((Multiset.card ((F.D T).Z.filter fun p => b / Real.log T < |p.1 - 1/2|) : ℕ) : ℝ)
      ≤ η * F.Nz T

/-- **[OPEN B / B′] — the derivative route.**  `F'` is the zero family of
`ξ'`.  Levinson–Montgomery: the two off-line counts agree up to `O(log T)`. -/
def LevinsonMontgomery (F F' : Family) : Prop :=
  ∃ c > 0, ∀ᶠ T in atTop, |F'.Noff T - F.Noff T| ≤ c * Real.log T

/-- Unconditional Farmer–Gonek–Lee for `ξ'` (**[OPEN B]**): `(★)` for the
derivative family.

Status, carefully: the derivative-side **proportion** is closed —
`Assumptions.zeta23_xiPrime` records zeta-23's unconditional `0.85838` for
`ξ'`.  That does *not* supply this `Prop`: Proposition 1 bounds `N⊛` from
below, so the `(★)` form needs the pair-correlation input of the zeta-23 `ξ'`
argument directly (ISSUES.md #7).  Hence still a hypothesis, never an
axiom. -/
def UnconditionalFGL (F' : Family) (C' : ℝ) : Prop := F'.toCounts.StarBound C'

/-! ### Bridge statements

These were axioms in the first draft of `Assumptions.lean`.  They are
**refutable** when quantified over an arbitrary `Family` or an arbitrary
`closePairs` function — see ISSUES.md #8 — so they are `Prop`s, carried as
hypotheses, exactly like the open problems. -/

/-- Proposition 2 with the `𝒩`-term kept: a close-pair lower bound at the
*same* `λ` improves the constant by `c₁`.  (GLSS §5–6 bookkeeping.) -/
def ClosePairBookkeeping (closePairs : ℝ → ℝ → ℝ) (F : Family) : Prop :=
  ∀ c₀ lam c₁ : ℝ, EffectiveFujii F.toCounts c₀ → 0 < lam →
    ClosePairLowerBound closePairs F lam c₁ →
      F.toCounts.StarBound (Cbound c₀ lam - c₁)

/-- Farmer–Ki (arXiv:1002.1616), quantitative form: `ζ'`-zeros near the
`½`-line give closely spaced `ζ`-zeros.  Note the `λ` is **produced**, not
chosen — ISSUES.md #3. -/
def FarmerKiTransfer (closePairs : ℝ → ℝ → ℝ) (F F' : Family) : Prop :=
  ∀ M : ℝ → ℝ, DensityNearLine F' M →
    ∃ lam > 0, ∃ c₁ > 0, ClosePairLowerBound closePairs F lam c₁

/-- BGST's narrow-box theorem (arXiv:2501.14545, 2603.28104): inside a box of
width `b/log T` with `b → 0`, `(★)` holds with `C = 4/3`.  Stated with **no
exceptional set** — ISSUES.md #1. -/
def BGSTNarrowBox (F : Family) : Prop :=
  ∀ ε > 0, ∃ b > 0, NarrowBox F b → F.toCounts.StarBound (4/3 + ε)

/-- **[OPEN B″] — λ-uniform quantitative Farmer–Ki** (Errata 1, E3).

The Route II gap after [OPEN B] retired: near-line mass of `ξ'`-zeros gives
`ζ`-close-pair mass **with a constant uniform over a λ-range covering the
`Cbound` optimum** (`≈ 0.6–0.9`).  Contrast `FarmerKiTransfer`, in which the
`λ` is existentially produced — "a constant produced at a scale the consumer
did not order". -/
def LambdaUniformFarmerKi (closePairs : ℝ → ℝ → ℝ) (F F' : Family)
    (lamLo lamHi : ℝ) : Prop :=
  ∀ M : ℝ → ℝ, DensityNearLine F' M →
    ∃ c₁ > 0, ∀ lam ∈ Set.Icc lamLo lamHi, ClosePairLowerBound closePairs F lam c₁

/-- **[OPEN A″] — an exceptional-set-tolerant narrow-box theorem**
(Errata 1, E4).  The BGST argument rerun so that it accepts `NarrowBoxExc`
(all but `η·N(T)` zeros in the box) rather than `NarrowBox` (all of them).
Route III is blocked behind this regardless of progress on [OPEN A]/[OPEN A′]. -/
def NarrowBoxTolerant (F : Family) : Prop :=
  ∀ ε > 0, ∃ b > 0, ∃ η > 0, NarrowBoxExc F b η → F.toCounts.StarBound (4/3 + ε)

/-- `NarrowBoxExc` is monotone: a wider box and a larger exceptional
allowance are weaker hypotheses. -/
theorem NarrowBoxExc.mono {F : Family} {b b' η η' : ℝ} (h : NarrowBoxExc F b η)
    (hb : b ≤ b') (hη : η ≤ η') : NarrowBoxExc F b' η' := by
  filter_upwards [h, Filter.eventually_gt_atTop (1:ℝ)] with T hT hT1
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hle : (F.D T).Z.filter (fun p => b' / Real.log T < |p.1 - 1/2|)
      ≤ (F.D T).Z.filter (fun p => b / Real.log T < |p.1 - 1/2|) :=
    Multiset.monotone_filter_right _ (fun p hp =>
      lt_of_le_of_lt (div_le_div_of_nonneg_right hb hlog.le) hp)
  have hcard : ((Multiset.card ((F.D T).Z.filter
        fun p => b' / Real.log T < |p.1 - 1/2|) : ℕ) : ℝ)
      ≤ ((Multiset.card ((F.D T).Z.filter
        fun p => b / Real.log T < |p.1 - 1/2|) : ℕ) : ℝ) := by
    exact_mod_cast Multiset.card_le_card hle
  have hnn : (0:ℝ) ≤ F.Nz T := by
    unfold Family.Nz; positivity
  nlinarith [hT, hcard, hnn]

/-- **[OPEN D] — third-moment input**, stated at the level of its
consequence: `(★)` with `C` arbitrarily close to `1`, which is what the Pair
Correlation Conjecture gives and what the Tentative Theorem needs. -/
def ExtendedSupport (F : Family) : Prop := ∀ ε > 0, F.toCounts.StarBound (1 + ε)

end Riemann
