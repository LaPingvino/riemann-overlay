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

/-! ### The `NscAny` genre at family level — `SESSION 214`

`197` proved the arXiv:2306.04799 genre wall at a single `ZeroData` and declined
the family version, because `Transfer.Counts` has fields `Nz`, `Ns`, `Nsc` and a
family-level `NscAny` looked like widening the structure every route theorem is
stated over.

That was the wrong place to look. `Family`'s counts are **derived definitions,
not fields** — `Family.Nz`, `Family.Nsc`, `Family.Noff` are all `def`s over
`F.D T`. Adding one more changes no existing declaration. -/

/-- Simple zeros anywhere in the strip, at family level.  `SESSION 214`. -/
noncomputable def Family.NscAny (F : Family) (T : ℝ) : ℝ := (((F.D T).NscAny : ℕ) : ℝ)

/-- **The literature's simple-zero row**, with no location demand — the quantity
arXiv:2306.04799 bounds.  `SESSION 214`. -/
def Family.ProportionAny (F : Family) (κ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, (κ - ε) * F.Nz T ≤ F.NscAny T

/-- **The genre's constant can never exceed `1`.**  `SESSION 214`.
`NscAny ≤ N`, so a `ProportionAny κ` with the window eventually nonempty forces
`κ ≤ 1`: more simple zeros than zeros is not on offer. -/
theorem Family.proportionAny_le_one {F : Family} {κ : ℝ}
    (h : F.ProportionAny κ) : κ ≤ 1 := by
  by_contra hκ
  push_neg at hκ
  have hε : (0 : ℝ) < (κ - 1) / 2 := by linarith
  have hev := h _ hε
  obtain ⟨T, hT, hpos⟩ := (hev.and F.nonempty).exists
  have hle : F.NscAny T ≤ F.Nz T := by
    unfold Family.NscAny Family.Nz
    exact_mod_cast ZeroData.NscAny_le_N (F.D T)
  have hNz : (0 : ℝ) < F.Nz T := by
    unfold Family.Nz; exact_mod_cast hpos
  nlinarith [hT, hle, hNz]

/-- **The genre wall, at family level.**  `SESSION 214`.

A `ProportionAny κ` together with an off-line import at `β` delivers
`ProportionStd (κ − β)`, and `κ ≤ 1`, so what reaches the ledger's own row is at
most `1 − β`.

At the baseline's own off-line bound `β = 0.3275` that ceiling is `0.6725` —
the row the genre would have to beat.  `197` proved this pointwise; this is the
statement about a family, which is the level the ledger's rows live at. -/
theorem Family.proportionStd_of_proportionAny {F : Family} {κ β : ℝ}
    (h : F.ProportionAny κ) (hoff : OffLineImport F β) :
    F.ProportionStd (κ - β) ∧ κ - β ≤ 1 - β := by
  refine ⟨?_, by have := F.proportionAny_le_one h; linarith⟩
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  filter_upwards [h _ hε2, hoff _ hε2] with T hT hO
  have hsplit : F.NscAny T ≤ F.NscStd T + F.Noff T := by
    unfold Family.NscAny Family.NscStd Family.Noff
    exact_mod_cast ZeroData.NscAny_le_NscStd_add_Noff (F.D T)
  linarith

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

/-- **The ladder's first rung is free.**  `SESSION 234`.

`NoSmallHaunted F 3` is a *theorem*, not a hypothesis: a haunted ordinate — one
whose on-line part is `1` and whose mass is not `1` — carries at least three
zeros, because the functional equation pairs its off-line ghosts
(`ZeroData.three_le_H_of_haunted`, and `R10`'s factor of two).

This is why `certified_nsc_ladder` at `m = 3` returns `407/800 = 0.50875`, which
is `certified_nsc_unconditional` exactly.  The multiplicity ladder does not
start at the certified row by coincidence — the certified row **is** its first
rung, and it is free because rung `3` demands nothing. -/
theorem noSmallHaunted_three (F : Family) : NoSmallHaunted F 3 := by
  classical
  intro T γ hγ
  by_cases h1 : (F.D T).H γ = 1
  · exact Or.inl h1
  · refine Or.inr ?_
    -- `onAt γ = 1` puts the on-line point at `γ` in `Z` with multiplicity one
    have hon : Blindness.onAt (F.D T) γ = 1 := by
      have := Blindness.H_eq_onAt_add_offAt (F.D T) γ
      omega
    have hcount : (F.D T).Z.count ((1/2 : ℝ), γ) = 1 := by
      rw [Blindness.count_eq_onAt (F.D T) (by rfl)]; exact hon
    have hmem : ((1/2 : ℝ), γ) ∈ (F.D T).Z :=
      Multiset.count_pos.1 (by rw [hcount]; norm_num)
    have h2 : 2 ≤ (F.D T).H γ := by
      have hsum := Blindness.H_eq_onAt_add_offAt (F.D T) γ
      omega
    exact ZeroData.three_le_H_of_haunted hmem (by rfl) hcount h2

/-- **The board's two `κ` rows are one row.**  `SESSION 255`.

`proportion_of_mult_le_two` and `proportion_of_noHaunted_zeta` both return
`0.6725`, from hypotheses that look unrelated.  They are not: multiplicity `≤ 2`
*implies* `NoHaunted`, so the first row is a corollary of the second.

The mechanism is `Blindness.noHaunted_of_mult_le_two`, which has been in
`Fiber.lean` since `181`: `offAt` is even and at most `H`, so `H − offAt = 1`
under `H ≤ 2` forces `H = 1`, leaving no haunted ordinate to exclude.  Strictness
is `Blindness.noHaunted_not_mult_le_two`.  Both hypotheses reach `κ` by making
`N_sc = NscStd`, and `κ` is the certified `NscStd` row.

**What is new here is only the lift.**  Those two theorems are about a single
`ZeroData`; `RULING.md` has stated the domination as prose since `234` and cited
them, but nothing carried it to the `Family` level where `NoHaunted` is defined
and where the board's rows live.  This is that one line, so the board's claim is
now a term and not a sentence.

*(`260`: and the cap cannot be relaxed — `Family.noHaunted_sharp_at_two`
exhibits a family at `H ≤ 3` that is haunted, so `2` is the threshold and not
merely a convenient value.)* -/
theorem Family.noHaunted_of_boundedMult_two (F : Family)
    (h : ∀ T γ, (F.D T).H γ ≤ 2) : NoHaunted F :=
  fun T γ hγ => Blindness.noHaunted_of_mult_le_two (F.D T) (h T) γ hγ

/-- **The rungs are nested: a higher rung is at least as large a demand.**

`PRICES.md`'s menu presents `m = 5, 7, → ∞` as a *dial* — a scale on which you
choose how much to assume.  That framing needs the hypotheses to be comparable,
and nothing had said they were.  They are: `m ≤ H` follows from `m + 1 ≤ H`, so
`NoSmallHaunted F (m+1) → NoSmallHaunted F m`.

Together with `noHaunted_iff_forall_noSmallHaunted` this makes the menu's top row
the top of a *chain* rather than a separate item that happens to pay more.

*Scope, as first stated:* this is `≤`, not `<`.

✅ **Strictness proved in `SESSION 157`** — `noSmallHaunted_strict` supplies the
witness at every rung, so the chain is strictly increasing and no two rungs of
the menu are the same hypothesis. -/
theorem NoSmallHaunted.mono {F : Family} {m : ℕ}
    (hh : NoSmallHaunted F (m + 1)) : NoSmallHaunted F m := by
  intro T γ hg
  rcases hh T γ hg with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by omega)


/-- **The ladder has only odd rungs.**  `SESSION 235`.

A haunted ordinate carries an odd number of zeros (`Blindness.haunted_odd`: its
off-line part is even and its on-line part is one).  So demanding *"every
haunted mass is at least `m`"* for an **even** `m` is the same demand as for
`m + 1` — no haunted ordinate can sit at an even mass to be excluded.

With `NoSmallHaunted.mono` the two are equivalent, so the rungs at even `m` are
not separate hypotheses.

**And that matters for pricing, not just for tidiness.**
`certified_nsc_ladder` evaluates to `(m·κ − 1)/(m − 1)`, which is strictly
increasing in `m`; at `m = 4` it returns `169/300 = 0.5633…` while the very same
hypothesis, read at `m = 5`, returns `189/320 = 0.590625`.  Reading an even rung
off the ladder **understates what the hypothesis buys**.  `RULING.md`'s table
lists odd `m` for this reason. -/
theorem noSmallHaunted_even_step {F : Family} {m : ℕ} (hm : 2 ≤ m) (he : Even m)
    (h : NoSmallHaunted F m) : NoSmallHaunted F (m + 1) := by
  intro T γ hg
  rcases h T γ hg with h1 | h2
  · exact Or.inl h1
  · refine Or.inr ?_
    have hpos : 0 < (F.D T).H γ := by omega
    have hodd := Blindness.haunted_odd (F.D T) hg hpos
    rcases Nat.even_or_odd ((F.D T).H γ) with hev | _
    · exact absurd hev hodd
    · -- `m` even, `H` odd, `m ≤ H`, so `m ≠ H`
      have hne : m ≠ (F.D T).H γ := by
        intro hEq
        exact hodd (hEq ▸ he)
      omega

/-- The two rungs are the same hypothesis.  `SESSION 235`. -/
theorem noSmallHaunted_even_iff {F : Family} {m : ℕ} (hm : 2 ≤ m) (he : Even m) :
    NoSmallHaunted F m ↔ NoSmallHaunted F (m + 1) :=
  ⟨noSmallHaunted_even_step hm he, NoSmallHaunted.mono⟩

/-- **`NoHaunted` really is the ladder's limit** — `SESSION 156`.

The docstring below has called it that since `105`, and `PRICES.md`'s menu lists
`m → ∞` as the top rung, but nothing connected the two definitions: `NoHaunted`
and `NoSmallHaunted` were introduced separately and only the *proportions* they
deliver were compared.  They are related exactly as the word "limit" claims.

Forward is immediate.  Backward is the one line worth having: instantiate the
family at `m = H γ + 1`, and the rung's own disjunction `H = 1 ∨ m ≤ H` collapses,
because `H + 1 ≤ H` is false.  So no ordinate can hide above every rung — which is
what makes the ladder exhaustive rather than merely increasing. -/
theorem noHaunted_iff_forall_noSmallHaunted (F : Family) :
    NoHaunted F ↔ ∀ m, NoSmallHaunted F m := by
  constructor
  · intro h m T γ hg
    exact Or.inl (h T γ hg)
  · intro h T γ hg
    rcases h ((F.D T).H γ + 1) T γ hg with h1 | h2
    · exact h1
    · omega

/-- **A multiplicity cap collapses the ladder to its limit one rung above it.**
`SESSION 261`.

`noHaunted_iff_forall_noSmallHaunted` reaches `NoHaunted` by taking *every* rung.
Under a cap it takes one.  A haunted ordinate satisfies the rung's disjunction as
`m ≤ H`, and the cap says `H ≤ M`; if `M < m` the two cannot both hold, so the
disjunction's other branch fires and `H = 1`.

**What this is worth, and it is not small.**  At `M = 3` the cap alone is nearly
empty — `259` re-verified `LEADS`'s table: `M ≤ 3` carries a star constant of
`1.9825` and a `prop1` image of `7/400 = 0.0175`.  The `m = 5` rung alone is
`certified_nsc_via_noSmallHaunted`'s `0.590625`.  Together they are `NoHaunted`,
which is `κ = 0.6725` — more than either, and `254` showed no rung of the ladder
ever reaches `κ` on its own.

So the two axes `260` separated are not independent purchases: bounded
multiplicity is a threshold hypothesis worth almost nothing by itself on the
`Nsc` row, and its value is entirely in what it does to the crowding axis. -/
theorem noHaunted_of_boundedMult_of_noSmallHaunted {F : Family} {M m : ℕ}
    (hcap : ∀ T γ, (F.D T).H γ ≤ M) (hlt : M < m) (h : NoSmallHaunted F m) :
    NoHaunted F := by
  intro T γ hγ
  rcases h T γ hγ with h1 | h2
  · exact h1
  · have := le_trans h2 (hcap T γ)
    omega

/-- **The cheapest instance: cap at three, rung at five.**  `SESSION 261`.

`260` showed `BoundedMult 2` is the last cap that gives `NoHaunted` unaided.
This is the next one along, bought with the ladder's second rung — and `235`'s
collapse of the even rungs means `m = 5` is the adjacent one, not `m = 4`. -/
theorem noHaunted_of_mult_three_rung_five {F : Family}
    (hcap : ∀ T γ, (F.D T).H γ ≤ 3) (h : NoSmallHaunted F 5) : NoHaunted F :=
  noHaunted_of_boundedMult_of_noSmallHaunted hcap (by omega) h

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

/-- **The exchange map is complete: one genuine crossover, two identities** —
`SESSION 192`.

`191` found the two `StarBound` exchanges crossing at `C = 1.393` and observed
that the board is a set of *exchanges* with ranges of validity.  Enumerating
every pair that consumes the **same** input settles how many such ranges there
are:

| input | routes | relation |
|---|---|---|
| `ProportionStd κ` | `(3κ−1)/2` direct, or via `OffLineImport (1−κ)` | **identical** (below) |
| `OffLineImport β` | `κ − β/2` direct, or via `HauntedDensity (β/2)` | **identical** — same formula |
| `StarBound C` | `2 − C` direct, or via `HauntedDensity ((C−1)/6)` | **crosses at `1.393`** |
| `atomCount ≥ c·N` | via `HauntedDensity ((1−c)/2)` only | single route |

So the board has **one** place where the choice of exchange matters, and it is
`191`'s.  Everywhere else the two ways of spending an input agree by
construction — which is why no earlier cycle ever had to choose.

The `ProportionStd` identity is the one worth writing down: routing the baseline
through the off-line shelf and back returns `084`'s formula exactly, which is
`162`'s circularity as an equation rather than as an observation. -/
theorem proportionStd_exchange_identity (κ : ℝ) :
    κ - (1 - κ) / 2 = (3 * κ - 1) / 2 := by ring

/-! ### What a rung of the ladder buys — `SESSION 236`

`certified_nsc_ladder` prices rung `m` at `(m·κ − 1)/(m − 1)`.  `234` listed the
rungs and `235` showed only the odd ones are distinct hypotheses.  Neither said
what a rung *buys*, and both closed forms are one line.

The side condition is `m ≠ 1` in both, which the ladder supplies since it starts
at `m = 3` — stated rather than assumed. -/

/-- **The distance from rung `m` to `NoHaunted` is `(1 − κ)/(m − 1)`.**
`SESSION 236`.

`NoHaunted` is the ladder's limit at `κ`, so this is what is still unbought at
rung `m`.  It falls like `1/(m − 1)`, which is why the rungs crowd: rung `3`
leaves a sixth of a point of `κ` on the table and rung `11` a thirtieth. -/
theorem ladder_gap {κ m : ℝ} (hm : m ≠ 1) :
    κ - (m * κ - 1) / (m - 1) = (1 - κ) / (m - 1) := by
  field_simp
  ring

/-- **Climbing two rungs buys `2(1 − κ)/(m² − 1)`.**  `SESSION 236`.  Two,
because `235` showed the intervening even rung is the same hypothesis. -/
theorem ladder_step {κ m : ℝ} (h1 : m ≠ 1) (h2 : m + 1 ≠ 0) :
    ((m + 2) * κ - 1) / ((m + 2) - 1) - (m * κ - 1) / (m - 1)
      = 2 * (1 - κ) / ((m - 1) * (m + 1)) := by
  have h3 : m + 2 - 1 ≠ 0 := by intro h; apply h2; linarith
  have h4 : m - 1 ≠ 0 := sub_ne_zero.2 h1
  field_simp
  ring

/-- **The off-line bound `β = 1 − κ`, at both baselines.**  `SESSION 237`.

`offLineImport_of_proportionStd` gives `β = 1 − κ` for any family, and the
development carries the two instances as separate named constants: `0.3275` at
zeta-23's `κ = 0.6725`, and `0.14162` at `ξ'`'s `κ' = 0.85838`.  They are one
formula read at two families. -/
theorem offLine_bound_at_both_baselines :
    (1 : ℝ) - 0.6725 = 0.3275 ∧ (1 : ℝ) - 0.85838 = 0.14162 := by
  constructor <;> norm_num

/-- **The unconditional row and the `ξ'` route are one formula.**  `SESSION 238`.

`proportion_of_offLineImport` prices any off-line import at `κ − β/2`.  The
development evaluates it twice and names the results separately:

* `β = 1 − κ` — the import a `ProportionStd κ` gives about **its own** family —
  returns `0.50875`, `certified_nsc_unconditional`;
* `β = 1 − κ'` — the import carried over from `ξ'` — returns `0.60169`,
  `certified_nsc_via_xiPrime`.

So the `ξ'` route is not a different mechanism.  It is the unconditional route
with a better `β`, bought with two more axioms, and `237`'s reading of
`0.3275` against `0.14162` repeats one level up: those are the two `β`s. -/
theorem exchange_at_both_imports :
    (0.6725 : ℝ) - (1 - 0.6725) / 2 = 0.50875
      ∧ (0.6725 : ℝ) - (1 - 0.85838) / 2 = 0.60169 := by
  constructor <;> norm_num

/-- **The off-line currency's whole range.**  `SESSION 239`.

`proportion_of_offLineImport` pays `κ − β/2`, and `β` is a proportion bound, so
`0 ≤ β`.  The best import a `ProportionStd κ` gives about its own family is
`β = 1 − κ` (`offLineImport_of_proportionStd`).  Between those two ends the
currency buys exactly

    (3κ − 1)/2   ≤   κ − β/2   ≤   κ.

At the certified `κ` that is `[0.50875, 0.6725]`: from the free row to the
`NoHaunted` row and no further.  The floor `β ≥ 0` is what pins the top. -/
theorem offLineImport_range {κ β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1 - κ) :
    (3 * κ - 1) / 2 ≤ κ - β / 2 ∧ κ - β / 2 ≤ κ := by
  constructor <;> linarith

/-- **What a target costs, in off-line control.**  `SESSION 239`.  Inverting the
exchange: reaching `T` through this currency needs `β = 2(κ − T)`, and nothing
else about `T` matters. -/
theorem offLineImport_inverse {κ β T : ℝ} : κ - β / 2 = T ↔ β = 2 * (κ - T) := by
  constructor <;> intro h <;> linarith

/-- **The board's rows, priced in `β`.**  `SESSION 239`.

The free row costs the free import; `ξ'` costs `1 − κ'`; Route III's `2/3` costs
`7/600`, a twenty-eight-fold improvement on the free bound; and `NoHaunted`'s
`0.6725` costs `β = 0` — **no off-line zeros at all**.

That last is the sharp one.  Reaching the `NoHaunted` row *through this currency*
is exactly as expensive as ruling out off-line zeros outright, which is why the
board buys it as a multiplicity hypothesis instead. -/
theorem offLineImport_board_prices :
    (2 : ℝ) * (0.6725 - 0.50875) = 0.3275
      ∧ (2 : ℝ) * (0.6725 - 0.60169) = 0.14162
      ∧ (2 : ℝ) * (0.6725 - 2/3) = 7/600
      ∧ (2 : ℝ) * (0.6725 - 0.6725) = 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Every finite rung is strictly below `κ`.**  `SESSION 240`.

`(m·κ − 1)/(m − 1) < κ` reduces to `κ < 1` after clearing the denominator — the
`m` cancels entirely.  So no rung of the multiplicity ladder reaches the
certified `NscStd` row, at any `m`; `236`'s gap `(1 − κ)/(m − 1)` shrinks without
closing.  `NoHaunted`, the limit, is what reaches `κ`. -/
theorem ladder_lt_kappa {κ m : ℝ} (hκ : κ < 1) (hm : 1 < m) :
    (m * κ - 1) / (m - 1) < κ := by
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < m - 1)]
  nlinarith

/-- **The ladder's supremum *is* `κ`, over the rungs that actually exist.**
`SESSION 254`.

`239` proved every rung is `< κ`.  That alone leaves open how much `NoHaunted`
buys over the whole ladder: strictly-less-than is compatible with stopping at
`0.62`.  It does not — the rungs come arbitrarily close.

The quantifier runs over the rungs the hypotheses admit, which is the point of
stating it this way.  `235` showed the even rungs are the same hypothesis as the
odd one below, so the realisable rungs are the odd integers `m ≥ 3`; here they
are written `2n + 3`.  Nothing appeals to a real `m`.

Together with `ladder_lt_kappa`: `κ` is the least upper bound of the ladder and
no rung attains it.  So `NoHaunted` buys exactly one point over the entire
multiplicity ladder — the limit — and every finite approximation to it is
already available at some `NoSmallHaunted (2n+3)`. -/
theorem ladder_approaches_kappa {κ ε : ℝ} (hκ : κ < 1) (hε : 0 < ε) :
    ∃ n : ℕ, κ - ε < ((2 * n + 3) * κ - 1) / ((2 * n + 3) - 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - κ) / ε)
  refine ⟨n, ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm1 : (2 * (n : ℝ) + 3) ≠ 1 := by intro h; linarith
  have hgap := ladder_gap (κ := κ) (m := 2 * (n : ℝ) + 3) hm1
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 3 - 1 := by linarith
  have hlt : (1 - κ) / (2 * (n : ℝ) + 3 - 1) < ε := by
    rw [div_lt_iff₀ hden]
    have hnε : (1 - κ) < ε * n := by
      rw [div_lt_iff₀ hε] at hn; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith [hgap]

/-- **Both currencies saturate at `κ`.**  `SESSION 240`.

Put `239` and the line above together.  Off-line control buys at most `κ`, and
only at `β = 0`; the multiplicity ladder buys strictly less than `κ` at every
finite rung, and exactly `κ` in the `NoHaunted` limit.  Neither currency the
project owns passes the certified `NscStd` row.

The board's shape follows: any row promising more than `κ` on the `Nsc` line —
Route I, `[OPEN D]` — is buying a third thing, and that is a fact about the two
exchanges rather than a gap in the search. -/
theorem currencies_saturate_at_kappa {κ β m : ℝ} (hκ : κ < 1) (hm : 1 < m)
    (h0 : 0 ≤ β) :
    κ - β / 2 ≤ κ ∧ (m * κ - 1) / (m - 1) < κ :=
  ⟨by linarith, ladder_lt_kappa hκ hm⟩

/-! ### What the odd-atom class does to `prop1`'s LP — `SESSION 249`

`247` showed a bound `oddAtoms ≥ c·N` excludes `Gauge.pairOnly`, the
configuration that makes `prop1` tight.  Excluding a binding witness is exactly
what `200`–`202` showed can free the LP, so the question is whether it does.

Work on the mass-`{1,2}` family, which is where `prop1` is tight: `k` on-line
atoms of mass `1` and `j` mirror pairs of mass `2`.  Then `N = k + 2j`,
`N⊛ = k + 4j`, `N_sc = k`, `oddAtoms = k`, and the class constraint
`k ≥ c(k + 2j)` caps the ratio at `r := j/k ≤ (1 − c)/(2c)`.  Per mass-one atom
the linear bound reads `a(1 + 2r) + b(1 + 4r) ≤ 1`.

Two identities settle the shape of that, and both are one line. -/

/-- **`prop1` saturates the mass-`{1,2}` constraint at every ratio.**
`SESSION 249`.  `(a, b) = (2, −1)` gives `2(1+2r) − (1+4r) = 1` for all `r`, so
no member of this family separates `prop1` from the bound — which is
`Gauge.prop1_tight` seen along the whole family rather than at one point. -/
theorem prop1_saturates_mass_two_family (r : ℝ) :
    2 * (1 + 2 * r) + (-1) * (1 + 4 * r) = 1 := by ring

/-- **The class's binding ratio reproduces `2 − c`.**  `SESSION 249`.

At the extreme ratio `r = (1 − c)/(2c)` the two coefficients are
`1 + 2r = 1/c` and `1 + 4r = (2 − c)/c`, so their quotient is exactly `2 − c` —
the star-bound break-even (`242`), and at the certified `κ` the number
`1.3275`.

**The reading, which is not proved here.**  The unrestricted LP forces
`a + 2b ≤ 0`, obtained as `r → ∞`; capping `r` replaces it by
`a(1+2r) + b(1+4r) ≤ 1`, whose boundary direction turns at `C = (1+4r)/(1+2r)`.
So the odd-atom class leaves `prop1` optimal for `C ≤ 2 − c` and stops
constraining above it.  That the class is *not* free is `247`'s point: `c = κ`
is bought from the baseline. -/
theorem oddAtom_class_ratio {c : ℝ} (hc : 0 < c) :
    (1 + 4 * ((1 - c) / (2 * c))) / (1 + 2 * ((1 - c) / (2 * c))) = 2 - c := by
  have h2 : (2 : ℝ) * c ≠ 0 := by positivity
  have hnum : 1 + 4 * ((1 - c) / (2 * c)) = (2 - c) / c := by field_simp; ring
  have hden : 1 + 2 * ((1 - c) / (2 * c)) = 1 / c := by field_simp; ring
  rw [hnum, hden]
  field_simp

/-- **One constant governs the whole ladder.**  `SESSION 236`.

At the certified `κ = 0.6725` the numerator `1 − κ` is `131/400 = 0.3275` — the
project's certified off-line bound — and the gap at the ladder's free first rung
is `131/800 = 0.16375`, the haunted-density constant.  `190` found that number
wearing four hats; this is the fifth, and it is the general formula's `m = 3`
case rather than another coincidence. -/
theorem ladder_gap_at_three :
    (1 : ℝ) - 0.6725 = 0.3275 ∧ ((1 : ℝ) - 0.6725) / (3 - 1) = 0.16375 := by
  constructor <;> norm_num

/-- **Which star-bound exchange to use, and where they cross** — `SESSION 191`.

A `StarBound C` reaches the `Nsc` row two ways:

* **direct** — `proportion_of_starBound` gives `Proportion (2 − C)`;
* **via haunting** — `hauntedDensity_of_starBound` gives `HauntedDensity
  ((C−1)/6)`, then `proportion_of_hauntedDensity` gives `Proportion (κ − (C−1)/6)`.

They cross at `C = 1.393` (exactly, `κ` being rational). Below it the direct
exchange is better; above it the haunted one is, because `2 − C` degrades at rate
`1` in `C` while the haunted route degrades at rate `1/6`.

**Route III's `C = 4/3 ≈ 1.3333` sits below the crossover**, so its `2/3` is the
right reading there — the haunted route would give only `0.61694`. That is worth
recording because `hauntedDensity_of_starBound` is the **one** haunted-density
bound in the development whose input is not minted from `κ` (`190`), and it is
still dominated at the only `C` the board actually offers. -/
theorem starBound_exchange_crossover {C : ℝ} :
    (0.6725 : ℝ) - (C - 1) / 6 ≤ 2 - C ↔ C ≤ 1.393 := by
  constructor <;> intro h <;> linarith

/-- **The off-line exchange, fed the only `β` the machinery makes, strictly
loses** — `SESSION 162`.

`161` found the `NscAny` route tying at `κ = 1` because the only unconditional
off-line bound available is `β = 1 − κ`, minted from the row being improved.
That is not an accident of one instance: the development has exactly **two**
producers of `OffLineImport`, `offLineImport_of_proportionStd` and
`offLineImport_of_derivative`, and **both** yield `1 − κ` by construction.

Feed that back through `proportion_of_offLineImport` and the return is
`κ − (1 − κ)/2 = (3κ − 1)/2`, which is `< κ` for every `κ < 1`.  So the canonical
off-line round trip is a **strict loss** at every constant below `1`, closing at
equality only in the world where every zero is simple.

This is also the identity behind `084`: `(3·0.6725 − 1)/2 = 0.50875` is not a
separate route's number, it is the baseline having gone once around this loop —
which is why `111`/`112` find the row unimprovable from the baseline alone. -/
theorem offline_roundtrip_loses {κ : ℝ} (hκ : κ < 1) : (3 * κ - 1) / 2 < κ := by
  linarith

/-- …and it is an equality exactly at `κ = 1`. -/
theorem offline_roundtrip_eq_iff {κ : ℝ} : (3 * κ - 1) / 2 = κ ↔ κ = 1 := by
  constructor <;> intro h <;> linarith

/-- The constant family on one configuration.  `Proportion` and `ProportionStd`
are asymptotic predicates on families, so a `ZeroData` witness only refutes a
`Family`-level claim once it is placed in a family — which is what this is for. -/
noncomputable def constFamily (D : ZeroData) (h : 0 < D.N) : Family where
  D := fun _ => D
  nonempty := Filter.Eventually.of_forall fun _ => h

/-- **`255`'s implication is sharp, at the level the board works at.**
`SESSION 260`.

`Family.noHaunted_of_boundedMult_two` lifts `H ≤ 2 → NoHaunted` to families.
This is the matching negative one step up: a family capped at `H ≤ 3` that is
haunted, so the cap cannot be relaxed at all.

Placed after `constFamily` rather than beside `255`'s block, per `R23` — the
pointwise content is `Blindness.noHaunted_fails_at_mult_three` and this is only
its transport. -/
theorem Family.noHaunted_sharp_at_two {a : ℝ} (ha : a ≠ 1/2)
    (hpos : 0 < (Blindness.configAt 0 1 1 a).N) :
    (∀ T γ, ((constFamily (Blindness.configAt 0 1 1 a) hpos).D T).H γ ≤ 3)
      ∧ ¬ NoHaunted (constFamily (Blindness.configAt 0 1 1 a) hpos) := by
  obtain ⟨hle, hbad⟩ := Blindness.noHaunted_fails_at_mult_three ha
  exact ⟨fun _ γ => hle γ, fun hcon => hbad fun γ => hcon 0 γ⟩

/-- **The family-level genre wall is attained.**  `SESSION 218`.

`214` proved `ProportionAny κ` plus an off-line import at `β` delivers
`ProportionStd (κ − β)` and no more.  A ceiling nobody reaches says less than
one that is met, and `197` supplied the pointwise witness; this is the family
one, which is the level `ProportionStd` lives at.

The constant family on `config 1 1 a` — one on-line zero, one off-line pair —
has `N = 3`, `NscAny = 3`, `NscStd = 1`, `N_off = 2`.  So `κ = 1` and `β = 2/3`
are both admissible, the wall predicts `ProportionStd (1/3)`, and the family's
actual standard-simple ratio **is** `1/3`.

Placed after `constFamily` rather than beside `214`'s block, per `R23`. -/
theorem proportionAny_wall_attained {a : ℝ} (ha : a ≠ 1/2)
    (hpos : 0 < (Blindness.config 1 1 a).N) :
    (constFamily (Blindness.config 1 1 a) hpos).ProportionAny 1
      ∧ OffLineImport (constFamily (Blindness.config 1 1 a) hpos) (2/3)
      ∧ (constFamily (Blindness.config 1 1 a) hpos).ProportionStd (1 - 2/3)
      ∧ ((Blindness.config 1 1 a).NscStd : ℝ) / ((Blindness.config 1 1 a).N : ℝ)
          = 1 - 2/3 := by
  have hN : (Blindness.config 1 1 a).N = 3 := by
    rw [Blindness.config_N]
  have hAny : (Blindness.config 1 1 a).NscAny = 3 := by
    rw [Blindness.config_NscAny 1 1 ha]; norm_num
  have hStd : (Blindness.config 1 1 a).NscStd = 1 := by
    rw [Blindness.config_NscStd 1 1 ha]; norm_num
  have hOff : (Blindness.config 1 1 a).Noff = 2 := by
    rw [Blindness.config_Noff ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    refine Filter.Eventually.of_forall fun T => ?_
    show (1 - ε) * ((Blindness.config 1 1 a).N : ℝ)
        ≤ ((Blindness.config 1 1 a).NscAny : ℝ)
    rw [hN, hAny]; push_cast; linarith
  · intro ε hε
    refine Filter.Eventually.of_forall fun T => ?_
    show ((Blindness.config 1 1 a).Noff : ℝ)
        ≤ (2/3 + ε) * ((Blindness.config 1 1 a).N : ℝ)
    rw [hN, hOff]; push_cast; linarith
  · intro ε hε
    refine Filter.Eventually.of_forall fun T => ?_
    show (1 - 2/3 - ε) * ((Blindness.config 1 1 a).N : ℝ)
        ≤ ((Blindness.config 1 1 a).NscStd : ℝ)
    rw [hN, hStd]; push_cast; linarith
  · rw [hN, hStd]; norm_num

/-- The single-ordinate witness clears rung `1 + 2j`.  Extracted in `SESSION 158`
so that strictness and non-vacuity rest on one construction rather than two
copies of it. -/
lemma configAt_noSmallHaunted {a : ℝ} (_ha : a ≠ 1/2) {j : ℕ} (hj : 1 ≤ j)
    (hN : 0 < (Blindness.configAt 0 1 j a).N) :
    NoSmallHaunted (constFamily (Blindness.configAt 0 1 j a) hN) (1 + 2 * j) := by
  classical
  intro T γ hg
  by_cases hγ : γ = 0
  · subst hγ
    right
    show (1 + 2 * j) ≤ (Blindness.configAt 0 1 j a).H 0
    rw [Blindness.configAt_H]
    simp
  · exfalso
    have hH : (Blindness.configAt 0 1 j a).H γ = 0 := by
      rw [Blindness.configAt_H]; simp [hγ]
    have hsplit := Blindness.H_eq_onAt_add_offAt (Blindness.configAt 0 1 j a) γ
    have : (Blindness.configAt 0 1 j a).H γ
        - Blindness.offAt (Blindness.configAt 0 1 j a) γ = 1 := hg
    omega

/-- **No rung of the menu is secretly RH** — `SESSION 158`.

`108`/`116` proved the *top* rung strictly weaker than RH-in-window
(`Blindness.noHaunted_strictly_weaker_than_RH`).  The intermediate rungs had no
such check, and `144` is the reason one is owed: a hypothesis can be precise
enough to look valuable and still empty the thing it would buy.  If some rung
forced `Noff = 0`, that row would be RH in disguise and worthless as a route.

None does.  The same witness that makes the chain strict carries `2j` off-line
zeros, so every rung admits off-line mass. -/
theorem noSmallHaunted_admits_offline {a : ℝ} (ha : a ≠ 1/2) {j : ℕ}
    (hj : 1 ≤ j) (hN : 0 < (Blindness.configAt 0 1 j a).N) :
    NoSmallHaunted (constFamily (Blindness.configAt 0 1 j a) hN) (1 + 2 * j)
      ∧ (Blindness.configAt 0 1 j a).Noff ≠ 0 := by
  refine ⟨configAt_noSmallHaunted ha hj hN, ?_⟩
  rw [Blindness.configAt_Noff ha]
  omega

/-- **And the chain is strict at every rung** — `SESSION 157`, closing the scope
note `156` left open.

`156` proved the rungs nested (`≤`) and explicitly declined `<`, which needs, for
each `m`, a configuration satisfying rung `m` and failing rung `m + 1`.  The
witness is the obvious one and it exists at every level: a single ordinate
carrying one critical zero and `j` off-line pairs has `H = 1 + 2j`,
`offAt = 2j`, hence `H − offAt = 1` — haunted, of mass exactly `1 + 2j`.  It
clears rung `1 + 2j` by `le_refl` and fails rung `2 + 2j` because `H` is one
short.

So no two rungs of `PRICES.md`'s menu are the same hypothesis, and the dial has a
distinct detent at every odd mass. -/
theorem noSmallHaunted_strict {a : ℝ} (ha : a ≠ 1/2) {j : ℕ} (hj : 1 ≤ j) :
    ∃ F : Family, NoSmallHaunted F (1 + 2 * j)
      ∧ ¬ NoSmallHaunted F (2 + 2 * j) := by
  classical
  have hN : 0 < (Blindness.configAt 0 1 j a).N := by
    rw [Blindness.configAt_N]; omega
  refine ⟨constFamily (Blindness.configAt 0 1 j a) hN,
    configAt_noSmallHaunted ha hj hN, ?_⟩
  · intro hcon
    have hg : (Blindness.configAt 0 1 j a).H 0
        - Blindness.offAt (Blindness.configAt 0 1 j a) 0 = 1 := by
      rw [Blindness.configAt_H, Blindness.offAt_configAt_self ha]
      simp
    rcases hcon 0 0 hg with h1 | h2
    · have h1' : (Blindness.configAt 0 1 j a).H 0 = 1 := h1
      rw [Blindness.configAt_H] at h1'
      simp at h1'
      omega
    · have h2' : 2 + 2 * j ≤ (Blindness.configAt 0 1 j a).H 0 := h2
      rw [Blindness.configAt_H] at h2'
      simp at h2'

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

/-- **A bound on the haunted density** — the quantitative form of `NoHaunted`,
and the currency `109`'s identity trades in. -/
def HauntedDensity (F : Family) (δ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ) ≤ (δ + ε) * F.Nz T

/-- **The canonical conditional row: `ProportionStd κ` and `hauntedCount ≤ δ·N`
give `Proportion (κ − δ)`.**

Immediate from `Blindness.NscStd_eq_Nsc_add_haunted`: the row is
`Nsc/N = NscStd/N − hauntedCount/N`, an identity, so a density bound subtracts
directly.  `NoHaunted` is the case `δ = 0`. -/
theorem proportion_of_hauntedDensity {F : Family} {κ δ : ℝ}
    (hh : HauntedDensity F δ) (hstd : F.ProportionStd κ) :
    F.toCounts.Proportion (κ - δ) := by
  intro ε hε
  filter_upwards [hstd (ε / 2) (by linarith), hh (ε / 2) (by linarith),
    F.toCounts.pos] with T hT hH hpos
  have hpos' : 0 < F.Nz T := hpos
  have hid : F.NscStd T
      = F.Nsc T + ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ) := by
    have := Blindness.NscStd_eq_Nsc_add_haunted (F.D T)
    unfold Family.NscStd Family.Nsc
    exact_mod_cast this
  show κ - δ - ε ≤ F.Nsc T / F.Nz T
  rw [le_div_iff₀ hpos']
  linarith [hT, hH, hid]

/-- **`087`'s off-line route is the special case `δ = β/2`.**  A haunted ordinate
carries at least two off-line zeros (`Blindness.two_mul_haunted_add_NscStd_le_N`
via the coupling), so an off-line import at `β` is a haunted density at `β/2`. -/
theorem hauntedDensity_of_offLineImport {F : Family} {β : ℝ}
    (h : OffLineImport F β) : HauntedDensity F (β / 2) := by
  intro ε hε
  filter_upwards [h ε (by linarith), F.toCounts.pos] with T hO hpos
  have hcoup : 2 * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ) ≤ F.Noff T := by
    have hnat := Blindness.NscStd_eq_Nsc_add_haunted (F.D T)
    have hcp := Blindness.two_mul_NscStd_le_Noff_add_two_mul_Nsc (F.D T)
    have : 2 * Blindness.hauntedCount (F.D T) ≤ (F.D T).Noff := by omega
    unfold Family.Noff
    exact_mod_cast this
  have hnn := F.Nz_nonneg T
  nlinarith [hO, hcoup, hnn, hε.le]

/-- **The off-line currency sharpens with the rung: `δ = β/(m − 1)`.**
`SESSION 262`.

`hauntedDensity_of_offLineImport` charges each haunted ordinate two off-line
zeros, which is the free rung `m = 3`.  Under `NoSmallHaunted m` it carries
`m − 1` of them (`Blindness.pred_mul_haunted_le_Noff`), so the same import buys
`(m − 1)/2` times as much density.

**This is a third route, not a restatement of the second.**
`hauntedDensity_of_noSmallHaunted` reaches `(1 − κ)/(m − 1)` by charging the rung
against `N` and needs `ProportionStd κ` to cap it; this charges it against
`N_off` and needs no proportion at all.  At the project's certified constants the
two agree — `237` puts the off-line bound at `β = 1 − κ` — so the numbers on the
board do not move, and what changes is the hypothesis you must hold to get them.

At `m = 3` it is `β/2` and the older theorem is recovered. -/
theorem hauntedDensity_of_offLineImport_at_rung {F : Family} {β : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (ho : OffLineImport F β) (hh : NoSmallHaunted F m) :
    HauntedDensity F (β / ((m : ℝ) - 1)) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  intro ε hε
  filter_upwards [ho (ε * ((m : ℝ) - 1)) (by positivity), F.toCounts.pos]
    with T hO hpos
  have hnat := Blindness.pred_mul_haunted_le_Noff (F.D T) m (fun γ => hh T γ)
  have hcoup : ((m : ℝ) - 1) * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ)
      ≤ F.Noff T := by
    have : (((m - 1) * Blindness.hauntedCount (F.D T) : ℕ) : ℝ)
        ≤ ((F.D T).Noff : ℝ) := by exact_mod_cast hnat
    unfold Family.Noff
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)] at this
    linarith
  have key : ((m : ℝ) - 1) * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ)
      ≤ (β + ε * ((m : ℝ) - 1)) * F.Nz T := le_trans hcoup hO
  rw [← sub_nonneg]
  have hsplit : (β / ((m : ℝ) - 1) + ε) * F.Nz T
        - ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ)
      = ((β + ε * ((m : ℝ) - 1)) * F.Nz T
          - ((m : ℝ) - 1) * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ))
        / ((m : ℝ) - 1) := by
    field_simp
  rw [hsplit]
  exact div_nonneg (by linarith) hm0.le

/-- **`105`'s ladder is the density instrument at `δ = (1 − κ)/(m − 1)`.**

`Blindness.pred_mul_haunted_add_NscStd_le_N` gives
`(m−1)·hauntedCount ≤ N − NscStd`, and `ProportionStd κ` caps the right side by
`(1 − κ)·N`.  At `m = 3` this is `0.16375` — the ledger's `δ`; at `m = 5`,
`0.081875`, and `0.6725 − 0.081875 = 0.590625`, which is exactly `105`'s number.

**`263`: this is not a second derivation, and the twenty lines that used to be
here have gone.**  `262` added the off-line-resource ladder as what it took to be
a spare route.  It is not spare: `offLineImport_of_proportionStd` turns
`ProportionStd κ` into an off-line import at exactly `β = 1 − κ`, and feeding
that to `hauntedDensity_of_offLineImport_at_rung` reproduces this statement on
the nose.  So the ladder is an off-line phenomenon throughout — the proportion
enters only by being converted into an off-line bound — and the theorem is now
that composite.  The `N`-resource lemma above is kept and no longer consumed;
see its own docstring. -/
theorem hauntedDensity_of_noSmallHaunted {F : Family} {m : ℕ} {κ : ℝ}
    (hm : 2 ≤ m) (hh : NoSmallHaunted F m) (hstd : F.ProportionStd κ) :
    HauntedDensity F ((1 - κ) / ((m : ℝ) - 1)) :=
  hauntedDensity_of_offLineImport_at_rung hm (offLineImport_of_proportionStd hstd) hh
/-- **The `/6` bridge is the density instrument at `δ = (C−1)/6`.**

`nscStd_le_nsc_add` above extracts `NscStd − Nsc ≤ (C−1)/6 · N` from a star
bound.  Through `109`'s identity that difference *is* the haunted count, so the
`/6` bridge is `HauntedDensity ((C−1)/6)` — the fifth and last instance of the
one conditional instrument, and the only one that consumes `(★)`. -/
theorem hauntedDensity_of_starBound {F : Family} {C : ℝ}
    (h : F.toCounts.StarBound C) : HauntedDensity F ((C - 1) / 6) := by
  intro ε hε
  filter_upwards [h (6 * ε) (by linarith), F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have hbase : 6 * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ) + F.Nz T
      ≤ F.Ns T := by
    have := Blindness.six_mul_haunted_add_N_le_Nstar (F.D T)
    unfold Family.Ns Family.Nz
    exact_mod_cast this
  have hstar : F.Ns T ≤ (C + 6 * ε) * F.Nz T := hT
  have hsplit : (C - 1) / 6 + ε = (C - 1 + 6 * ε) / 6 := by ring
  rw [hsplit, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 6)]
  nlinarith [hbase, hstar, hpos']

/-- The number of **odd-mass** ordinates at height `T`. -/
noncomputable def Family.oddAtoms (F : Family) (T : ℝ) : ℝ :=
  ((Blindness.oddAtoms (F.D T) : ℕ) : ℝ)

/-- **The literature's row is also a lower bound on the odd-mass ordinates.**
Every standard-simple ordinate has odd mass (`Blindness.haunted_odd`), so
`ProportionStd κ` forces at least `κ·N` of them. -/
theorem oddAtoms_ge_of_proportionStd {F : Family} {κ : ℝ}
    (hstd : F.ProportionStd κ) :
    ∀ ε > 0, ∀ᶠ T in atTop, (κ - ε) * F.Nz T ≤ F.oddAtoms T := by
  intro ε hε
  filter_upwards [hstd ε hε] with T hT
  have h : F.NscStd T ≤ F.oddAtoms T := by
    have := Blindness.NscStd_le_oddAtoms (F.D T)
    unfold Family.NscStd Family.oddAtoms
    exact_mod_cast this
  linarith

/-- **A distinct-zeros proportion is a haunted-density bound, at rate `(1−c)/2`.**

`N − atomCount` is the **distinct-zeros deficit** `N(T) − N_d(T)`, a quantity the
literature names and studies (Cheer–Goldston and descendants).  A haunted
ordinate contributes at least `2` to it
(`Blindness.two_mul_haunted_add_atomCount_le_N`), so `atomCount ≥ c·N` gives
`HauntedDensity ((1−c)/2)`.

This is the convertible currency for the haunting problem: the literature cannot
bound haunting directly — by `Blindness` it cannot even see it — but it can bound
the deficit, and the deficit pays at rate one-half. -/
theorem hauntedDensity_of_distinctZeros {F : Family} {c : ℝ}
    (h : ∀ ε > 0, ∀ᶠ T in atTop, (c - ε) * F.Nz T ≤ F.atomCount T) :
    HauntedDensity F ((1 - c) / 2) := by
  intro ε hε
  filter_upwards [h ε hε, F.toCounts.pos] with T hT hpos
  have hpos' : 0 < F.Nz T := hpos
  have hbase : 2 * ((Blindness.hauntedCount (F.D T) : ℕ) : ℝ) + F.atomCount T
      ≤ F.Nz T := by
    have := Blindness.two_mul_haunted_add_atomCount_le_N (F.D T)
    unfold Family.atomCount Family.Nz
    exact_mod_cast this
  have hsplit : (1 - c) / 2 + ε = (1 - c + 2 * ε) / 2 := by ring
  rw [hsplit, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [hT, hbase, hpos']

/-- **The distinct-zeros rate `(1−c)/2` is attained.**  `SESSION 219`.

`hauntedDensity_of_distinctZeros` converts a distinct-zeros proportion `c` into
`HauntedDensity ((1−c)/2)`, at rate one half.  A conversion rate matters only if
something reaches it.

The mass-three haunted atom does.  `2·hauntedCount + atomCount ≤ N` is equality
exactly when every haunted ordinate has `H = 3` and every other has `H = 1`, and
`configAt 0 1 1 a` — one on-line zero, one off-line pair, at a single
ordinate — is that configuration: `N = 3`, `atomCount = 1`, `hauntedCount = 1`
(`Blindness.mass_three_atom_attains_all`).

So `c = 1/3` holds, the theorem predicts `HauntedDensity (1/3)`, and the actual
haunted density is `1/3`.  This is the third of the three literature genres to
be shown walled by a bound that is met, after the moment routes (`211`) and the
simple-zero counts (`218`). -/
theorem hauntedDensity_distinctZeros_attained {a : ℝ} (ha : a ≠ 1/2)
    (hpos : 0 < (Blindness.configAt 0 1 1 a).N) :
    (∀ ε > 0, ∀ᶠ T in atTop,
        ((1:ℝ)/3 - ε) * (constFamily (Blindness.configAt 0 1 1 a) hpos).Nz T
          ≤ (constFamily (Blindness.configAt 0 1 1 a) hpos).atomCount T)
      ∧ HauntedDensity (constFamily (Blindness.configAt 0 1 1 a) hpos)
          ((1 - (1:ℝ)/3) / 2)
      ∧ ((Blindness.hauntedCount (Blindness.configAt 0 1 1 a) : ℝ)
          / ((Blindness.configAt 0 1 1 a).N : ℝ)) = (1 - (1:ℝ)/3) / 2 := by
  obtain ⟨hN, -, -, -, -, hHnt, hAtom⟩ := Blindness.mass_three_atom_attains_all ha
  have hc : ∀ ε > 0, ∀ᶠ T in atTop,
      ((1:ℝ)/3 - ε) * (constFamily (Blindness.configAt 0 1 1 a) hpos).Nz T
        ≤ (constFamily (Blindness.configAt 0 1 1 a) hpos).atomCount T := by
    intro ε hε
    refine Filter.Eventually.of_forall fun T => ?_
    show ((1:ℝ)/3 - ε) * ((Blindness.configAt 0 1 1 a).N : ℝ)
        ≤ ((Blindness.atomCount (Blindness.configAt 0 1 1 a) : ℕ) : ℝ)
    rw [hN, hAtom]; push_cast; linarith
  refine ⟨hc, hauntedDensity_of_distinctZeros hc, ?_⟩
  rw [hHnt, hN]; norm_num

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
