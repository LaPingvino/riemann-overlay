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

/-- **The literature's row is already a zero-density statement, with no `(★)`.**

`offline_le` above extracts `N_off ≤ (C−1)·N` from a star bound.  None is
needed: the standard-simple zeros are *on* the line, so
`Blindness.Noff_add_NscStd_le_N` gives `N_off ≤ N − NscStd` outright, and a
`ProportionStd κ` turns that into an off-line import at `β = 1 − κ`.

At the zeta-23 baseline this is `N_off ≤ 0.3275·N` — **at most 32.75% of the
zeros are off the critical line, unconditionally at the baseline's own axiom
tier.**  Feeding it back through `proportion_of_offLineImport` returns
`0.6725 − 0.16375 = 0.50875`, i.e. exactly `certified_nsc_unconditional`: the
two derivations of the `Nsc` row agree, by different routes. -/
theorem offLineImport_of_proportionStd {F : Family} {κ : ℝ}
    (hstd : F.ProportionStd κ) : OffLineImport F (1 - κ) := by
  intro ε hε
  filter_upwards [hstd ε hε] with T hT
  have hdisj : F.Noff T + F.NscStd T ≤ F.Nz T := by
    have := Blindness.Noff_add_NscStd_le_N (F.D T)
    unfold Family.Noff Family.NscStd Family.Nz
    exact_mod_cast this
  linarith

/-- The number of distinct ordinates at height `T`. -/
noncomputable def Family.atomCount (F : Family) (T : ℝ) : ℝ :=
  ((Blindness.atomCount (F.D T) : ℕ) : ℝ)

/-- **The literature's row is also a bound on mean vertical multiplicity.**
`ProportionStd κ` forces at least `κ·N` *distinct* ordinates
(`Blindness.NscStd_le_atomCount`), so the average number of zeros per ordinate is
at most `1/κ`.  At the zeta-23 baseline: at least `67.25%` as many distinct
ordinates as zeros, i.e. **mean multiplicity at most `1/0.6725 ≈ 1.487`**. -/
theorem atomCount_ge_of_proportionStd {F : Family} {κ : ℝ}
    (hstd : F.ProportionStd κ) :
    ∀ ε > 0, ∀ᶠ T in atTop, (κ - ε) * F.Nz T ≤ F.atomCount T := by
  intro ε hε
  filter_upwards [hstd ε hε] with T hT
  have h : F.NscStd T ≤ F.atomCount T := by
    have := Blindness.NscStd_le_atomCount (F.D T)
    unfold Family.NscStd Family.atomCount
    exact_mod_cast this
  linarith

/-- **A supremum bound on multiplicity is a star bound, at the same constant.**
Together with `Blindness.no_starBound_from_proportionStd` this brackets where
`(★)`'s constant lives: **not** obtainable from a proportion of simple zeros at
any constant, and obtainable from a multiplicity supremum only at constant `M` —
which `prop1` can use only when `M ≤ 1`, i.e. when every zero is already simple.

`(★)`'s constant is neither: `Blindness.Nstar_eq_sum_H_sq` gives
`N⊛/N = Σ H² / Σ H`, the **size-biased mean multiplicity**. -/
theorem starBound_of_multiplicity_le {F : Family} {M : ℕ}
    (h : ∀ T γ, (F.D T).H γ ≤ M) : F.toCounts.StarBound M := by
  intro ε hε
  filter_upwards with T
  have hb : F.Ns T ≤ (M : ℝ) * F.Nz T := by
    have := Blindness.Nstar_le_of_multiplicity_le (F.D T) M (h T)
    unfold Family.Ns Family.Nz
    exact_mod_cast this
  have hnn := F.Nz_nonneg T
  show F.Ns T ≤ ((M : ℝ) + ε) * F.Nz T
  nlinarith [hb, hnn]

/-- **A multiplicity supremum, *plus* a certified `Nsc` row, gives a useful star
bound.**  `starBound_of_multiplicity_le` charges every zero `M`; this charges the
simple ones `1`, which is what the ledger's row pays for:

> `C ≤ 1 + M·(1 − κ)`.

At `M = 2` and the certified `κ = 0.50875` this is `C ≤ 1.9825 < 2` — so
**"no zero of `ζ` has multiplicity three or more" already implies `(★)`**, a
hypothesis strictly weaker than simplicity and the first sufficient condition for
`(★)` in the registers that does not assume the conclusion. -/
theorem starBound_of_multiplicity_and_proportion {F : Family} {M : ℕ} {κ : ℝ}
    (hM : ∀ T γ, (F.D T).H γ ≤ M) (hp : F.toCounts.Proportion κ) :
    F.toCounts.StarBound (1 + M * (1 - κ)) := by
  intro ε hε
  have hδ : 0 < ε / (M + 1) := by positivity
  filter_upwards [hp _ hδ, F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have hNsc : (κ - ε / (M + 1)) * F.Nz T ≤ F.Nsc T := by
    have h' : κ - ε / (M + 1) ≤ F.Nsc T / F.Nz T := hT
    rw [le_div_iff₀ hpos'] at h'
    exact h'
  have hbase : F.Ns T + M * F.Nsc T ≤ (1 + M) * F.Nz T := by
    have := Blindness.Nstar_add_mul_Nsc_le (F.D T) M (hM T)
    unfold Family.Ns Family.Nsc Family.Nz
    exact_mod_cast this
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hkey : (M : ℝ) * (ε / (M + 1)) ≤ ε := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hM1]
    nlinarith [hε.le]
  show F.Ns T ≤ (1 + M * (1 - κ) + ε) * F.Nz T
  nlinarith [hNsc, hbase, hpos', hkey]

/-- **Multiplicity `≤ 2` turns the literature's row into `(★)` at `C = 2 − κ`.**

Two exact facts do it (`Blindness.Nstar_add_Nsc_eq_two_mul_N` and
`Blindness.Nsc_eq_NscStd_of_mult_le_two`): under `H ≤ 2` the star constant is
`2 − Nsc/N` with no estimation at all, and `Nsc = NscStd`, so the *standard*
proportion the literature certifies applies directly.

At the zeta-23 baseline `κ = 0.6725` this is `C ≤ 1.3275`. -/
theorem starBound_of_mult_le_two {F : Family} {κ : ℝ}
    (hM : ∀ T γ, (F.D T).H γ ≤ 2) (hstd : F.ProportionStd κ) :
    F.toCounts.StarBound (2 - κ) := by
  intro ε hε
  filter_upwards [hstd ε hε] with T hT
  have hexact : F.Ns T + F.Nsc T = 2 * F.Nz T := by
    have := Blindness.Nstar_add_Nsc_eq_two_mul_N (F.D T) (hM T)
    unfold Family.Ns Family.Nsc Family.Nz
    exact_mod_cast this
  have heq : F.Nsc T = F.NscStd T := by
    have := Blindness.Nsc_eq_NscStd_of_mult_le_two (F.D T) (hM T)
    unfold Family.Nsc Family.NscStd
    exact_mod_cast this
  show F.Ns T ≤ (2 - κ + ε) * F.Nz T
  rw [heq] at hexact
  nlinarith [hT, hexact]

/-- **The sharp multiplicity criterion at every `M`:** `C ≤ M − (M−1)·κ`.

Strictly better than `starBound_of_multiplicity_and_proportion`'s
`1 + M·(1 − κ)` — by exactly `1 − κ` — and tight, since
`Blindness.Nstar_add_pred_mul_Nsc_le` attains equality at `H = 1` and `H = M`.

`C < 2` iff `κ > 1 − 1/(M − 1)`. -/
theorem starBound_of_mult_le {F : Family} {M : ℕ} {κ : ℝ} (hM1 : 1 ≤ M)
    (hM : ∀ T γ, (F.D T).H γ ≤ M) (hp : F.toCounts.Proportion κ) :
    F.toCounts.StarBound ((M : ℝ) - ((M : ℝ) - 1) * κ) := by
  intro ε hε
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hδ : 0 < ε / M := by positivity
  filter_upwards [hp _ hδ, F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have hNsc : (κ - ε / M) * F.Nz T ≤ F.Nsc T := by
    have h' : κ - ε / M ≤ F.Nsc T / F.Nz T := hT
    rw [le_div_iff₀ hpos'] at h'
    exact h'
  have hbase : F.Ns T + ((M : ℝ) - 1) * F.Nsc T ≤ (M : ℝ) * F.Nz T := by
    have hnat := Blindness.Nstar_add_pred_mul_Nsc_le (F.D T) M hM1 (hM T)
    have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have : (1 : ℕ) ≤ M := hM1
      push_cast [Nat.cast_sub this]
      ring
    unfold Family.Ns Family.Nsc Family.Nz
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast [hcast] at this
    linarith [this]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hkey : ((M : ℝ) - 1) * (ε / M) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hMpos]
    nlinarith [hε.le, hMpos, hM0]
  show F.Ns T ≤ ((M : ℝ) - ((M : ℝ) - 1) * κ + ε) * F.Nz T
  nlinarith [hNsc, hbase, hpos', hkey, hMpos, hM0]

/-- **No haunted ordinate carries fewer than `m` zeros.**  The hypothesis of the
ladder: a standard-simple ordinate is either simple outright, or crowded to mass
at least `m`.  Carried as a `Prop`, never an axiom. -/
def NoSmallHaunted (F : Family) (m : ℕ) : Prop :=
  ∀ T γ, (F.D T).H γ - Blindness.offAt (F.D T) γ = 1 →
    (F.D T).H γ = 1 ∨ m ≤ (F.D T).H γ

/-- **The ladder, transported: `ProportionStd κ` gives `Proportion ((m·κ−1)/(m−1))`.**

At `m = 3` this is `084`'s `(3κ−1)/2`; each odd rung upward is worth real points,
and the limit is `κ` itself — excluding *every* small haunted ordinate would
transfer the literature's row whole. -/
theorem proportion_of_noSmallHaunted {F : Family} {m : ℕ} {κ : ℝ} (hm : 2 ≤ m)
    (hh : NoSmallHaunted F m) (hstd : F.ProportionStd κ) :
    F.toCounts.Proportion (((m : ℝ) * κ - 1) / ((m : ℝ) - 1)) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  intro ε hε
  filter_upwards [hstd (ε / m) (by positivity), F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have hbase : (m : ℝ) * F.NscStd T ≤ F.Nz T + ((m : ℝ) - 1) * F.Nsc T := by
    have hnat := Blindness.mul_NscStd_le_N_add_pred_mul_Nsc (F.D T) m (by omega)
      (fun γ => hh T γ)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := by omega
      push_cast [Nat.cast_sub this]; ring
    unfold Family.NscStd Family.Nz Family.Nsc
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast [hcast] at this
    linarith [this]
  show ((m : ℝ) * κ - 1) / ((m : ℝ) - 1) - ε ≤ F.Nsc T / F.Nz T
  rw [le_div_iff₀ hpos']
  have hm0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hTm : ((m : ℝ) * κ - ε) * F.Nz T ≤ (m : ℝ) * F.NscStd T := by
    have he : (m : ℝ) * (κ - ε / m) = (m : ℝ) * κ - ε := by field_simp
    calc ((m : ℝ) * κ - ε) * F.Nz T
        = (m : ℝ) * ((κ - ε / m) * F.Nz T) := by rw [← he]; ring
      _ ≤ (m : ℝ) * F.NscStd T := by nlinarith [hT, hmpos]
  have hstep : ((m : ℝ) * κ - 1 - ε) * F.Nz T ≤ ((m : ℝ) - 1) * F.Nsc T := by
    nlinarith [hTm, hbase, hpos']
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfrac : ((m : ℝ) * κ - 1) / ((m : ℝ) - 1) - ε
      ≤ ((m : ℝ) * κ - 1 - ε) / ((m : ℝ) - 1) := by
    have hsplit : ((m : ℝ) * κ - 1 - ε) / ((m : ℝ) - 1)
        = ((m : ℝ) * κ - 1) / ((m : ℝ) - 1) - ε / ((m : ℝ) - 1) := by
      field_simp
    rw [hsplit]
    have hle : ε / ((m : ℝ) - 1) ≤ ε := by
      rw [div_le_iff₀ hm0]
      nlinarith [hε.le, hm2]
    linarith
  calc (((m : ℝ) * κ - 1) / ((m : ℝ) - 1) - ε) * F.Nz T
      ≤ (((m : ℝ) * κ - 1 - ε) / ((m : ℝ) - 1)) * F.Nz T :=
        mul_le_mul_of_nonneg_right hfrac hpos'.le
    _ ≤ F.Nsc T := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
        linarith [hstep]

/-- **No haunted ordinate anywhere** — the `m → ∞` end of the ladder. -/
def NoHaunted (F : Family) : Prop :=
  ∀ T γ, (F.D T).H γ - Blindness.offAt (F.D T) γ = 1 → (F.D T).H γ = 1

/-- **The ladder's limit, attained: `NoHaunted` transfers the literature's row
whole.**  Weaker than `097`'s `H ≤ 2` — which forbids unhaunted crowding too —
and it yields the same proportion, though not the same star bound. -/
theorem proportion_of_noHaunted {F : Family} {κ : ℝ}
    (hh : NoHaunted F) (hstd : F.ProportionStd κ) : F.toCounts.Proportion κ := by
  intro ε hε
  filter_upwards [hstd ε hε, F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have heq : F.Nsc T = F.NscStd T := by
    have := Blindness.Nsc_eq_NscStd_of_noHaunted (F.D T) (fun γ => hh T γ)
    unfold Family.Nsc Family.NscStd
    exact_mod_cast this
  show κ - ε ≤ F.Nsc T / F.Nz T
  rw [le_div_iff₀ hpos', heq]
  linarith [hT]

/-- The constant family on one configuration.  `Proportion` and `ProportionStd`
are asymptotic predicates on families, so a `ZeroData` witness only refutes a
`Family`-level claim once it is placed in a family — which is what this is for. -/
noncomputable def constFamily (D : ZeroData) (h : 0 < D.N) : Family where
  D := fun _ => D
  nonempty := Filter.Eventually.of_forall fun _ => h

/-- **`111`'s witness, upgraded from `ZeroData` to `Family`.**

The configuration of `Fiber.row_essentially_optimal` — `1000` simple atoms beside
`321` haunted mass-`3` atoms — placed in a constant family satisfies
`ProportionStd 0.6725` and **fails** `Proportion 0.50943`.

So the cap is genuine at the level where `Proportion` is defined: no theorem of
the form "`ProportionStd 0.6725` implies `Proportion κ`" can hold with
`κ > 1000/1963 ≈ 0.509424`.  The ledger certifies `0.50875`. -/
theorem baseline_cap {D : ZeroData} (hpos : 0 < D.N)
    (hstd : 6725 * D.N ≤ 10000 * D.NscStd)
    (hsc : 100000 * D.Nsc ≤ 50943 * D.N) :
    (constFamily D hpos).ProportionStd 0.6725
      ∧ ¬ (constFamily D hpos).toCounts.Proportion 0.50944 := by
  have hNz : ∀ T : ℝ, (constFamily D hpos).Nz T = (D.N : ℝ) := fun _ => rfl
  have hNsc : ∀ T : ℝ, (constFamily D hpos).Nsc T = (D.Nsc : ℝ) := fun _ => rfl
  have hNscStd : ∀ T : ℝ, (constFamily D hpos).NscStd T = (D.NscStd : ℝ) :=
    fun _ => rfl
  have hposR : (0 : ℝ) < (D.N : ℝ) := by exact_mod_cast hpos
  have hstdR : 6725 * (D.N : ℝ) ≤ 10000 * (D.NscStd : ℝ) := by exact_mod_cast hstd
  have hscR : 100000 * (D.Nsc : ℝ) ≤ 50943 * (D.N : ℝ) := by exact_mod_cast hsc
  constructor
  · intro ε hε
    filter_upwards with T
    rw [hNz, hNscStd]
    nlinarith [hstdR, hposR, hε.le]
  · intro hcon
    have := hcon (1 / 1000000) (by norm_num)
    rw [Filter.eventually_atTop] at this
    obtain ⟨T₀, hT₀⟩ := this
    have h := hT₀ T₀ le_rfl
    have h' : (0.50944 : ℝ) - 1 / 1000000 ≤ (D.Nsc : ℝ) / (D.N : ℝ) := h
    rw [le_div_iff₀ hposR] at h'
    nlinarith [h', hscR, hposR]

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
