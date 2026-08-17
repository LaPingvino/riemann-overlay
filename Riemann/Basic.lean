/-
# Horizontal multiplicity and the GLSS reduction

This file formalises §1 of the program document: the "master coordinate"
`H(γ)` (horizontal multiplicity) and Proposition 1,

  `N_sc(T) ≥ 2 N(T) - N⊛(T)`.

Everything here is **fully proved**: it is finite combinatorics on a multiset.
The only analytic input is the reflection symmetry of the zero set, which is
the defining hypothesis of `ZeroData` (it is the functional equation
`ζ(s) = 0 ↔ ζ(1-s) = 0` together with `ζ(s̄) = conj (ζ s)`, both classical
and *not* re-proved here).

Reference: Goldston–Lee–Schettler–Suriajaya, arXiv:2503.15449, Thm 2.
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical

namespace Riemann

/-! ### Multiset arithmetic helpers -/

theorem natCast_sum_map {α : Type*} (s : Multiset α) (f : α → ℕ) :
    ((s.map f).sum : ℤ) = (s.map fun a => (f a : ℤ)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

theorem sum_two_sub {α : Type*} (s : Multiset α) (f : α → ℕ) :
    2 * (Multiset.card s : ℤ) - ((s.map f).sum : ℤ)
      = (s.map fun a => (2 : ℤ) - (f a : ℤ)).sum := by
  rw [natCast_sum_map]
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      push_cast
      linarith [ih]

theorem card_eq_sum_one {α : Type*} (s : Multiset α) :
    (Multiset.card s : ℤ) = (s.map fun _ => (1 : ℤ)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      push_cast
      linarith [ih]

/-- Counting by a predicate is summing its indicator. -/
theorem card_filter_eq_sum {α : Type*} (s : Multiset α) (q : α → Prop)
    [DecidablePred q] :
    (Multiset.card (s.filter q) : ℤ)
      = (s.map fun a => if q a then (1 : ℤ) else 0).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      by_cases h : q a
      · rw [Multiset.filter_cons_of_pos _ h, Multiset.card_cons, Multiset.map_cons,
          Multiset.sum_cons, if_pos h]
        push_cast
        linarith [ih]
      · rw [Multiset.filter_cons_of_neg _ h, Multiset.map_cons, Multiset.sum_cons,
          if_neg h]
        linarith [ih]

theorem two_le_card_of_two_mem {α : Type*} {S : Multiset α} {a b : α}
    (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) : 2 ≤ Multiset.card S := by
  have herase : b ∈ S.erase a := (Multiset.mem_erase_of_ne hab).2 hb
  have h1 : 0 < Multiset.card (S.erase a) :=
    Multiset.card_pos_iff_exists_mem.2 ⟨b, herase⟩
  have h2 : Multiset.card (S.erase a) = Multiset.card S - 1 :=
    Multiset.card_erase_of_mem ha
  have h3 : 0 < Multiset.card S := Multiset.card_pos_iff_exists_mem.2 ⟨a, ha⟩
  omega

theorem three_le_card_of_three_mem {α : Type*} {S : Multiset α} {a b c : α}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    3 ≤ Multiset.card S := by
  have h1 : b ∈ S.erase a := (Multiset.mem_erase_of_ne hba).2 hb
  have h2 : c ∈ (S.erase a).erase b :=
    (Multiset.mem_erase_of_ne hcb).2 ((Multiset.mem_erase_of_ne hca).2 hc)
  have c1 : Multiset.card (S.erase a) = Multiset.card S - 1 := Multiset.card_erase_of_mem ha
  have c2 : Multiset.card ((S.erase a).erase b) = Multiset.card (S.erase a) - 1 :=
    Multiset.card_erase_of_mem h1
  have p0 : 0 < Multiset.card S := Multiset.card_pos_iff_exists_mem.2 ⟨a, ha⟩
  have p1 : 0 < Multiset.card (S.erase a) := Multiset.card_pos_iff_exists_mem.2 ⟨b, h1⟩
  have p2 : 0 < Multiset.card ((S.erase a).erase b) := Multiset.card_pos_iff_exists_mem.2 ⟨c, h2⟩
  omega

/-! ### The zero data -/

/-- Reflection in the critical line: `(β, γ) ↦ (1 - β, γ)`. -/
def refl (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, p.2)

@[simp] lemma refl_snd (p : ℝ × ℝ) : (refl p).2 = p.2 := rfl

@[simp] lemma refl_refl (p : ℝ × ℝ) : refl (refl p) = p := by
  simp [refl]

lemma refl_injective : Function.Injective refl := fun a b h => by
  have := congrArg refl h; simpa using this

lemma refl_ne_self {p : ℝ × ℝ} (h : p.1 ≠ 1 / 2) : refl p ≠ p := by
  intro hp
  apply h
  have : 1 - p.1 = p.1 := congrArg Prod.fst hp
  linarith

/--
The zeros of `ζ` in a height window: a finite multiset of points `(β, γ)` of
the critical strip, counted **with multiplicity**, closed under reflection in
the critical line.
-/
structure ZeroData where
  /-- The zeros `(β, γ)`, with multiplicity. -/
  Z : Multiset (ℝ × ℝ)
  /-- Functional-equation symmetry: the zero multiset is reflection invariant. -/
  refl_inv : Z.map refl = Z

namespace ZeroData

/-- **Build zero data from a finite set of zeros with multiplicities.**

This is the shape an analytic source supplies: a finite set of points in the
window, a multiplicity function (zeta-23's `zeroMult`, i.e. Mathlib's
`analyticOrderAt`), closure of the set under `ρ ↦ 1 - conj ρ`, and invariance
of the multiplicity under it.  Discharging `Assumptions.zetaFamily` reduces to
exactly these four inputs. -/
noncomputable def ofMult (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℕ)
    (hclosed : ∀ p ∈ s, refl p ∈ s) (hm : ∀ p ∈ s, m (refl p) = m p) : ZeroData where
  Z := s.val.bind fun p => Multiset.replicate (m p) p
  refl_inv := by
    have himg : s.image refl = s := by
      apply Finset.Subset.antisymm
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        exact hclosed p hp
      · intro q hq
        exact Finset.mem_image.2 ⟨refl q, hclosed q hq, by simp⟩
    have hval : s.val.map refl = s.val := by
      rw [← Finset.image_val_of_injOn refl_injective.injOn, himg]
    calc (s.val.bind fun p => Multiset.replicate (m p) p).map refl
        = s.val.bind fun p => Multiset.replicate (m p) (refl p) := by
          rw [Multiset.map_bind]; simp [Multiset.map_replicate]
      _ = s.val.bind fun p => Multiset.replicate (m (refl p)) (refl p) := by
          refine Multiset.bind_congr fun p hp => ?_
          rw [hm p hp]
      _ = (s.val.map refl).bind fun p => Multiset.replicate (m p) p := by
          rw [Multiset.bind_map]
      _ = s.val.bind fun p => Multiset.replicate (m p) p := by rw [hval]

variable (D : ZeroData)

/-- `H γ`: horizontal multiplicity — the number of zeros (with multiplicity)
at ordinate `γ`.  `H γ = 1` fuses "simple" and "on the critical line". -/
noncomputable def H (γ : ℝ) : ℕ := Multiset.card (D.Z.filter fun p => p.2 = γ)

/-- `N`: the number of zeros in the window, with multiplicity. -/
def N : ℕ := Multiset.card D.Z

/-- `N⊛ = Σ_ρ H(γ_ρ) = #{(ρ, ρ') : γ = γ'}`. -/
noncomputable def Nstar : ℕ := (D.Z.map fun p => D.H p.2).sum

/-- `N_sc`: the number of simple zeros on the critical line. -/
noncomputable def Nsc : ℕ :=
  Multiset.card (D.Z.filter fun p => p.1 = 1 / 2 ∧ D.H p.2 = 1)

/-- **`μ_T`, the vertical multiplicity measure**, as a multiset of ordinates:
each zero contributes its ordinate, with multiplicity.  This is the object the
pair-correlation/signature class provably sees (see LEADS.md, "X"), and `H` is
its counting function. -/
def ordinates : Multiset ℝ := D.Z.map Prod.snd

/-- `N_sc^std`: the **standard** notion of "simple and on the critical line" — a
zero with `β = 1/2` whose multiplicity in `Z` is one.  This is character-for-
character zeta-23's `N0simple` (`comparator/ChallengeDeps.lean`) and GLSS's
`N_sc`.

`Nsc` (with `H γ = 1`) is **strictly stronger**: it additionally demands that
no *other* zero shares the ordinate.  Under RH the two coincide; without RH a
simple on-line zero sharing its ordinate with an off-line pair is counted by
`NscStd` and not by `Nsc`.  See ISSUES.md #13 — the two must never be compared
as though they were the same quantity. -/
noncomputable def NscStd : ℕ :=
  Multiset.card (D.Z.filter fun p => p.1 = 1 / 2 ∧ D.Z.count p = 1)

/-- **`NscAny`: simple zeros anywhere in the strip** — multiplicity one, with no
demand that the zero be on the critical line.

`SESSION 160`.  This is a *third* simplicity notion and the registers had only
two.  It exists because Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh
(arXiv:2306.04799) bound exactly this: their Theorems 2 and 3 give "at least
`61.7%` of the nontrivial zeros are simple", and their own remark is that the
method "neither requires nor provides any information on whether any of these
zeros are on or not on the critical line".

So it is **weaker than both `Nsc` and `NscStd`**, each of which additionally
demands `p.1 = 1/2`.  `NscStd_le_NscAny` below is the dictionary entry, and it is
what makes their `61.7%` comparable to our rows at all. -/
noncomputable def NscAny : ℕ :=
  Multiset.card (D.Z.filter fun p => D.Z.count p = 1)

/-! **Why these entries are inequalities and stay that way** — `SESSION 222`.

`Blindness.no_profile_function_computes_NscAny`: no function of the profile
computes `NscAny`.  The profile determines every ledger entry
(`Blindness.N_from_profile` and its four companions), so no ledger quantity
determines `NscAny` either.  The three bounds below are therefore not a first
approximation to an identity — there is no identity to reach.  `196` proved each
attained and each strict somewhere; `222` says the strictness is structural. -/

/-- **The dictionary entry: `NscStd ≤ NscAny`.**

An on-line zero of multiplicity one *is* a zero of multiplicity one, so every
zero our `NscStd` row counts is counted by the literature quantity that
arXiv:2306.04799 bounds.  Hence a certified `NscStd/Nz ≥ κ` transfers to their
quantity at the same `κ`, and the two numbers can finally be put side by side.

The consequence is recorded in `PRICES.md`: the project's `67.25%` already
exceeds their conditional `61.7%` **on the very quantity they bound**, and does
so without their thin-box or zero-density hypothesis. -/
theorem NscStd_le_NscAny (D : ZeroData) : D.NscStd ≤ D.NscAny := by
  classical
  refine Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)
  intro p hp
  exact hp.2

/-- `N_off`: the number of zeros off the critical line — the zeros RH denies. -/
noncomputable def Noff : ℕ := Multiset.card (D.Z.filter fun p => p.1 ≠ 1 / 2)

/-- **Simple zeros off the critical line** — `SESSION 311`, applying `R29` to
`NscStd_le_NscAny`.

`222` computed this quantity inside `NscAny_le_NscStd_add_Noff`'s proof, as an
unnamed `have`, and discarded it.  It is the gap between the literature's
"simple" (`NscAny`, anywhere in the strip) and ours (`NscStd`, on the line), and
`RH` sets it to zero. -/
noncomputable def simpleOffLine (D : ZeroData) : ℕ :=
  Multiset.card (D.Z.filter fun p => p.1 ≠ 1/2 ∧ D.Z.count p = 1)

/-- **The partition `222` had and did not keep.** -/
theorem NscStd_add_simpleOffLine (D : ZeroData) :
    D.NscStd + simpleOffLine D = D.NscAny := by
  classical
  rw [ZeroData.NscStd, simpleOffLine, ZeroData.NscAny]
  have e1 : (D.Z.filter fun p => p.1 = 1/2 ∧ D.Z.count p = 1)
      = (D.Z.filter fun p => D.Z.count p = 1).filter fun p => p.1 = 1/2 := by
    rw [Multiset.filter_filter]
  have e2 : (D.Z.filter fun p => p.1 ≠ 1/2 ∧ D.Z.count p = 1)
      = (D.Z.filter fun p => D.Z.count p = 1).filter fun p => ¬ (p.1 = 1/2) := by
    rw [Multiset.filter_filter]
  rw [e1, e2, ← Multiset.card_add, Multiset.filter_add_not]

/-- Each such zero is an off-line zero, so the gap costs off-line mass. -/
theorem simpleOffLine_le_Noff (D : ZeroData) : simpleOffLine D ≤ D.Noff := by
  classical
  rw [simpleOffLine, ZeroData.Noff]
  exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun p hp => hp.1)

/-- **The reverse dictionary entry: `NscAny ≤ NscStd + Noff`.**

`SESSION 161`.  `160` gave the forward direction (`NscStd ≤ NscAny`), which lets
*our* row be read as a statement about *their* quantity.  This is the exchange
rate in the other direction — the mechanism by which any location-hypothesis
result about `NscAny` could feed the ledger's own rows.

Split the simple zeros by whether they lie on the line: those that do are counted
by `NscStd`, those that do not are counted by `Noff`.

**And it walls the whole genre.**  Rearranged, `NscStd ≥ NscAny − Noff`.  With
`Noff ≤ 0.3275·N` (`certified_offline`) and `NscAny ≤ N` (`NscAny_le_N`), any
lower bound `NscAny ≥ κ·N` yields only `NscStd/N ≥ κ − 0.3275`, so beating the
certified `0.6725` through this route needs `κ > 1` — **more simple zeros than
there are zeros.**  No result of the arXiv:2306.04799 genre can improve the
ledger this way, at any strength, unconditionally. -/
theorem NscAny_le_NscStd_add_Noff (D : ZeroData) :
    D.NscAny ≤ D.NscStd + D.Noff := by
  have h1 := NscStd_add_simpleOffLine D
  have h2 := simpleOffLine_le_Noff D
  omega

/-- **With no off-line mass the two notions of "simple" coincide.**
`SESSION 311`.  `CLAIMS.md`'s arXiv:2306.04799 comparison rests on
`NscStd ≤ NscAny`; this says the inequality is an equality exactly where `RH`
puts us. -/
theorem NscAny_eq_NscStd_of_Noff_zero {D : ZeroData} (h : D.Noff = 0) :
    D.NscAny = D.NscStd := by
  have h1 := NscStd_add_simpleOffLine D
  have h2 := simpleOffLine_le_Noff D
  omega

/-- `NscAny` counts a sub-multiset of the zeros, so it never exceeds `N`. -/
theorem NscAny_le_N (D : ZeroData) : D.NscAny ≤ D.N :=
  Multiset.card_le_card (Multiset.filter_le _ _)

/-- **The genre wall, as arithmetic rather than as a paragraph.**  `SESSION 197`.

`NscAny_le_NscStd_add_Noff`'s docstring argues in prose that no lower bound on
`NscAny` — the arXiv:2306.04799 genre — can improve the certified `NscStd` row.
This is that argument, machine-checked at the level of a single `ZeroData`.

Given an import `NscAny ≥ κ·N` and an off-line bound `Noff ≤ c·N`, all that
reaches `NscStd` is `κ − c`. -/
theorem nscAny_import_transfer (D : ZeroData) {κ c : ℝ}
    (hκ : κ * D.N ≤ D.NscAny) (hoff : (D.Noff : ℝ) ≤ c * D.N) :
    (κ - c) * D.N ≤ D.NscStd := by
  have h : (D.NscAny : ℝ) ≤ (D.NscStd : ℝ) + (D.Noff : ℝ) := by
    exact_mod_cast Nat.cast_le.2 (NscAny_le_NscStd_add_Noff D)
  nlinarith [hκ, hoff, h]

/-- **…and the import's own constant can never exceed `1`.**  `SESSION 197`.

`NscAny ≤ N`, so a hypothesis `NscAny ≥ κ·N` with `N > 0` forces `κ ≤ 1`.  This
is the half that makes the wall a wall rather than a discouraging estimate: the
genre cannot supply a `κ` large enough, because `κ > 1` would assert more simple
zeros than zeros. -/
theorem nscAny_import_kappa_le_one (D : ZeroData) {κ : ℝ}
    (hN : 0 < (D.N : ℝ)) (hκ : κ * D.N ≤ D.NscAny) : κ ≤ 1 := by
  have h : (D.NscAny : ℝ) ≤ (D.N : ℝ) := by
    exact_mod_cast Nat.cast_le.2 (NscAny_le_N D)
  nlinarith [hκ, h]

/-- **The ceiling of the whole genre.**  `SESSION 197`.

Combining the two: whatever the import, what reaches `NscStd` is at most
`1 − c`.  With the certified off-line bound `c = 0.3275` that ceiling is
`0.6725` — **numerically the row the ledger already carries**
(`nscAny_ceiling_is_the_certified_row` below).  So the genre's best possible
outcome is the row it would have to beat. -/
theorem nscAny_import_ceiling (D : ZeroData) {κ c : ℝ}
    (hN : 0 < (D.N : ℝ)) (hκ : κ * D.N ≤ D.NscAny)
    (hoff : (D.Noff : ℝ) ≤ c * D.N) :
    (κ - c) * D.N ≤ D.NscStd ∧ κ - c ≤ 1 - c :=
  ⟨nscAny_import_transfer D hκ hoff,
   by have := nscAny_import_kappa_le_one D hN hκ; linarith⟩

/-- The ceiling and the certified row are the same number.  `SESSION 197`. -/
theorem nscAny_ceiling_is_the_certified_row : (1 : ℝ) - 0.3275 = 0.6725 := by
  norm_num

-- **SUPERSEDED, `SESSION 214`.**  The family version exists:
-- `Gaps.Family.proportionStd_of_proportionAny`, with
-- `Gaps.Family.proportionAny_le_one` for the `κ ≤ 1` half.  Both axiom-free.
--
-- `197`'s note below looked at the wrong structure.  `Transfer.Counts` does
-- carry only `Nz`, `Ns`, `Nsc` — but `Family`'s counts are **derived
-- definitions over `F.D T`, not fields**, so `Family.NscAny` is one more `def`
-- and changes nothing that exists.  The cycle that added it was 57 inserted
-- lines and no deleted ones.
--
-- The original note, kept because the reasoning is the thing that was wrong:
--
-- > **What a family-level version would cost, stated rather than attempted**
-- > (`SESSION 197`).  `Transfer.Counts` carries `Nz`, `Ns`, `Nsc` and nothing
-- > else; a family-level `NscAnyProportion` would need two further fields
-- > (`NscAny` and `Noff`) on the structure every route theorem in the
-- > development is stated over.  The wall above is therefore proved pointwise,
-- > at a single `ZeroData`, and the passage to a family is not claimed.  This
-- > is a comment and not a `theorem … : True`, which is the vacuity shape
-- > `provenance_lint` exists to catch — a scope note is documentation, not a
-- > result.


/-- **The multiplicity of a point of `ofMult` is the multiplicity it was given.**
`SESSION 273`.

`ofMult_N` reads the *total*; this reads a single fibre, which is what any
`NscStd`-side bridge to zeta-23 needs — their `N0simple` filters on
`zeroMult ρ = 1`, and ours filters on `Z.count p = 1`, so the two only meet once
`count` is known to be `m`. -/
lemma ofMult_count (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℕ)
    (hclosed : ∀ p ∈ s, refl p ∈ s) (hm : ∀ p ∈ s, m (refl p) = m p) (p : ℝ × ℝ) :
    (ofMult s m hclosed hm).Z.count p = if p ∈ s then m p else 0 := by
  classical
  show Multiset.count p (s.val.bind fun q => Multiset.replicate (m q) q) = _
  rw [Multiset.count_bind]
  have hmap : (s.val.map fun q => Multiset.count p (Multiset.replicate (m q) q))
      = s.val.map (fun q => if p = q then m q else 0) := by
    refine Multiset.map_congr rfl fun q _ => ?_
    simp [Multiset.count_replicate, eq_comm]
  rw [hmap]
  show (Finset.sum s fun q => if p = q then m q else 0) = _
  rw [Finset.sum_ite_eq s p m]

/-- **`NscStd` of `ofMult` counts the points of multiplicity one on the line.**
`SESSION 274`.

The `NscStd`-side counterpart of `ofMult_N`, and the shape zeta-23's `N0simple`
is in: their filter is on `zeroMult ρ = 1`, ours on `Z.count p = 1`, and
`ofMult_count` is what identifies the two.

`273` failed at this twice by rewriting under `Multiset.filter`, whose
`DecidablePred` instance depends on the term being rewritten — *motive is not
type correct*. The way through is not to rewrite the filter at all: prove the
filtered multiset **is** the filtered `Finset`'s `val`, by `ext` on counts, where
`Multiset.count_filter` and `ofMult_count` do all the work. -/
lemma ofMult_NscStd (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℕ)
    (hclosed : ∀ p ∈ s, refl p ∈ s) (hm : ∀ p ∈ s, m (refl p) = m p) :
    (ofMult s m hclosed hm).NscStd
      = (s.filter fun p => p.1 = 1 / 2 ∧ m p = 1).card := by
  classical
  set D := ofMult s m hclosed hm with hD
  have key : D.Z.filter (fun p => p.1 = 1 / 2 ∧ D.Z.count p = 1)
      = (s.filter fun p => p.1 = 1 / 2 ∧ m p = 1).val := by
    ext p
    rw [Multiset.count_filter, hD, ofMult_count]
    by_cases hps : p ∈ s
    · simp only [if_pos hps]
      by_cases hc : p.1 = 1 / 2 ∧ m p = 1
      · rw [if_pos ⟨hc.1, hc.2⟩, hc.2]
        rw [Multiset.count_eq_one_of_mem (s.filter _).nodup
          (Finset.mem_filter.2 ⟨hps, hc⟩)]
      · rw [if_neg (fun h => hc ⟨h.1, h.2⟩)]
        rw [Multiset.count_eq_zero_of_notMem]
        intro hmem
        exact hc (Finset.mem_filter.1 hmem).2
    · simp only [if_neg hps]
      rw [if_neg (by rintro ⟨-, h⟩; exact absurd h (by norm_num))]
      rw [Multiset.count_eq_zero_of_notMem]
      intro hmem
      exact hps (Finset.mem_filter.1 hmem).1
  show Multiset.card (D.Z.filter _) = _
  rw [key]
  rfl

/-- The total count of `ofMult` is the sum of the multiplicities — the
Riemann–von Mangoldt side of the interface. -/
lemma ofMult_N (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℕ)
    (hclosed : ∀ p ∈ s, refl p ∈ s) (hm : ∀ p ∈ s, m (refl p) = m p) :
    (ofMult s m hclosed hm).N = ∑ p ∈ s, m p := by
  show Multiset.card (s.val.bind fun p => Multiset.replicate (m p) p)
      = Multiset.sum (Multiset.map m s.val)
  rw [Multiset.card_bind]
  congr 1
  exact Multiset.map_congr rfl fun p _ => Multiset.card_replicate _ _

variable {D}

lemma refl_mem {p : ℝ × ℝ} (hp : p ∈ D.Z) : refl p ∈ D.Z := by
  have : refl p ∈ D.Z.map refl := Multiset.mem_map_of_mem _ hp
  rwa [D.refl_inv] at this

lemma mem_filter_self {p : ℝ × ℝ} (hp : p ∈ D.Z) :
    p ∈ D.Z.filter fun q => q.2 = p.2 :=
  Multiset.mem_filter.2 ⟨hp, rfl⟩

/-- Every zero contributes at least one to its own horizontal multiplicity. -/
lemma one_le_H {p : ℝ × ℝ} (hp : p ∈ D.Z) : 1 ≤ D.H p.2 :=
  Multiset.card_pos_iff_exists_mem.2 ⟨p, mem_filter_self hp⟩

/-- **The key symmetry step.**  A zero off the critical line has horizontal
multiplicity at least `2`: its mirror image sits at the same ordinate.  This
is the whole reason `H` fuses the two failure modes of RH. -/
lemma two_le_H_of_off_line {p : ℝ × ℝ} (hp : p ∈ D.Z) (hoff : p.1 ≠ 1 / 2) :
    2 ≤ D.H p.2 :=
  two_le_card_of_two_mem (mem_filter_self hp)
    (Multiset.mem_filter.2 ⟨refl_mem hp, rfl⟩) (refl_ne_self hoff)

/-- If a zero has horizontal multiplicity `1`, it lies on the critical line
(and is simple). -/
lemma on_line_of_H_eq_one {p : ℝ × ℝ} (hp : p ∈ D.Z) (h : D.H p.2 = 1) :
    p.1 = 1 / 2 := by
  by_contra hoff
  have := two_le_H_of_off_line hp hoff
  omega

/-- **`H` is the counting function of `μ_T`.**  `H γ = μ_T({γ})`. -/
lemma H_eq_count (γ : ℝ) : D.H γ = D.ordinates.count γ := by
  classical
  rw [ZeroData.H, ZeroData.ordinates, Multiset.count_map]
  congr 1
  exact Multiset.filter_congr fun p _ => by constructor <;> exact fun h => h.symm

/-- **`N_sc` is a functional of `μ_T` alone.**

`Nsc` counts the ordinates whose `μ_T`-mass is exactly one — no reference to
`β` survives.  The reflection symmetry is what makes this work: an ordinate of
mass one *must* carry an on-line zero (`on_line_of_H_eq_one`), so the on-line
condition in the definition of `Nsc` is redundant.

This is the project's half of the characterization "X": the certificate class
sees only bandwidth-limited functionals of `μ_T`, and `Nsc` is one of them.
`NscStd` is **not** — it asks for the multiplicity of a *point*, which is
horizontal information `μ_T` has thrown away.  That is the structural reason
the two rows differ, and why the transfer costs `(C-1)/2`: the transfer is
buying back horizontal information. -/
theorem Nsc_eq_ordinate_functional (D : ZeroData) :
    D.Nsc = Multiset.card (D.ordinates.filter fun γ => D.ordinates.count γ = 1) := by
  classical
  have hpred : ∀ p ∈ D.Z, ((p.1 = 1 / 2 ∧ D.H p.2 = 1) ↔ D.H p.2 = 1) := by
    intro p hp
    exact ⟨fun h => h.2, fun h => ⟨on_line_of_H_eq_one hp h, h⟩⟩
  have h1 : D.Nsc = Multiset.card (D.Z.filter fun p => D.H p.2 = 1) := by
    unfold ZeroData.Nsc
    congr 1
    exact Multiset.filter_congr hpred
  have h2 : (D.Z.filter fun p => D.H p.2 = 1).map Prod.snd
      = D.ordinates.filter fun γ => D.H γ = 1 := by
    rw [ZeroData.ordinates, Multiset.filter_map]
    rfl
  calc D.Nsc = Multiset.card (D.Z.filter fun p => D.H p.2 = 1) := h1
    _ = Multiset.card ((D.Z.filter fun p => D.H p.2 = 1).map Prod.snd) := by
        rw [Multiset.card_map]
    _ = Multiset.card (D.ordinates.filter fun γ => D.H γ = 1) := by rw [h2]
    _ = Multiset.card (D.ordinates.filter fun γ => D.ordinates.count γ = 1) := by
        congr 1
        exact Multiset.filter_congr fun γ _ => by rw [H_eq_count]

/-- `N` and `N⊛` are `μ_T`-functionals too: total mass, and the sum of the
masses over the atoms.  Together with `Nsc_eq_ordinate_functional` this says
the whole `Basic.lean` layer factors through `μ_T`. -/
theorem N_Nstar_ordinate_functional (D : ZeroData) :
    D.N = Multiset.card D.ordinates ∧
      D.Nstar = (D.ordinates.map fun γ => D.ordinates.count γ).sum := by
  constructor
  · rw [ZeroData.N, ZeroData.ordinates, Multiset.card_map]
  · rw [ZeroData.Nstar, ZeroData.ordinates, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun p _ => H_eq_count p.2

lemma Nsc_eq_sum (D : ZeroData) :
    (D.Nsc : ℤ) =
      (D.Z.map fun p => if p.1 = 1 / 2 ∧ D.H p.2 = 1 then (1 : ℤ) else 0).sum := by
  unfold ZeroData.Nsc
  exact card_filter_eq_sum _ _

lemma Noff_eq_sum (D : ZeroData) :
    (D.Noff : ℤ) = (D.Z.map fun p => if p.1 ≠ 1 / 2 then (1 : ℤ) else 0).sum := by
  unfold ZeroData.Noff
  exact card_filter_eq_sum _ _

lemma two_N_sub_Nstar_eq_sum (D : ZeroData) :
    (2 * D.N : ℤ) - D.Nstar = (D.Z.map fun p => (2 : ℤ) - (D.H p.2 : ℤ)).sum := by
  unfold ZeroData.N ZeroData.Nstar
  exact sum_two_sub _ _

/--
**Proposition 1 (GLSS).**  `N_sc ≥ 2N - N⊛`.

Hence `N⊛ ≤ C·N` gives at least a proportion `2 - C` of simple critical
zeros.  The whole program is the pursuit of `C < 2`.
-/
theorem prop1 (D : ZeroData) : (2 * D.N : ℤ) - D.Nstar ≤ D.Nsc := by
  rw [two_N_sub_Nstar_eq_sum, Nsc_eq_sum]
  refine Multiset.sum_map_le_sum_map _ _ ?_
  intro p hp
  by_cases h1 : D.H p.2 = 1
  · have honline : p.1 = 1 / 2 := on_line_of_H_eq_one hp h1
    simp [h1, honline]
  · have h2 : 2 ≤ D.H p.2 := by
      have := one_le_H hp
      omega
    have hz : ((D.H p.2 : ℤ)) ≥ 2 := by exact_mod_cast h2
    split_ifs with h <;> linarith

/--
**A zero-density theorem for free.**  `N + N_off ≤ N⊛`: every off-line zero
contributes an *extra* unit to the horizontal multiplicity, because its
mirror image sits at the same ordinate.

So `(★)` with constant `C` does not merely give a proportion `2 - C` of
simple critical zeros; it simultaneously caps the off-line zeros at a
proportion `C - 1`.  This is the bridge the narrow-box splitting of Route III
wants, and it is elementary.
-/
theorem N_add_Noff_le_Nstar (D : ZeroData) : (D.N : ℤ) + D.Noff ≤ D.Nstar := by
  have hN : (D.N : ℤ) = (D.Z.map fun _ => (1 : ℤ)).sum := card_eq_sum_one _
  have hstar : (D.Nstar : ℤ) = (D.Z.map fun p => (D.H p.2 : ℤ)).sum := by
    unfold ZeroData.Nstar
    exact natCast_sum_map _ _
  rw [Noff_eq_sum, hN, hstar, ← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ ?_
  intro p hp
  by_cases hoff : p.1 ≠ 1 / 2
  · have h2 : 2 ≤ D.H p.2 := two_le_H_of_off_line hp hoff
    have hz : ((D.H p.2 : ℤ)) ≥ 2 := by exact_mod_cast h2
    rw [if_pos hoff]
    linarith
  · have h1 : 1 ≤ D.H p.2 := one_le_H hp
    have hz : ((D.H p.2 : ℤ)) ≥ 1 := by exact_mod_cast h1
    rw [if_neg hoff]
    linarith

/-- A zero whose ordinate carries nothing else has multiplicity one. -/
lemma count_eq_one_of_H_eq_one {p : ℝ × ℝ} (hp : p ∈ D.Z) (h : D.H p.2 = 1) :
    D.Z.count p = 1 := by
  have hfil : Multiset.count p (D.Z.filter fun q => q.2 = p.2) = Multiset.count p D.Z :=
    Multiset.count_filter_of_pos rfl
  have hle : Multiset.count p (D.Z.filter fun q => q.2 = p.2)
      ≤ Multiset.card (D.Z.filter fun q => q.2 = p.2) := Multiset.count_le_card _ _
  have h1 : 1 ≤ D.Z.count p := Multiset.one_le_count_iff_mem.2 hp
  rw [ZeroData.H] at h
  omega

/-- **`Nsc ≤ NscStd`.**  The project's routes deliver a bound on the *stronger*
quantity; an external result stated for the standard notion does not transfer
backwards.  (ISSUES.md #13.) -/
theorem Nsc_le_NscStd (D : ZeroData) : D.Nsc ≤ D.NscStd := by
  have h : (D.Nsc : ℤ) ≤ (D.NscStd : ℤ) := by
    unfold ZeroData.Nsc ZeroData.NscStd
    rw [card_filter_eq_sum, card_filter_eq_sum]
    refine Multiset.sum_map_le_sum_map _ _ ?_
    intro p hp
    by_cases hc : p.1 = 1 / 2 ∧ D.H p.2 = 1
    · rw [if_pos hc, if_pos ⟨hc.1, count_eq_one_of_H_eq_one hp hc.2⟩]
    · rw [if_neg hc]
      split_ifs <;> norm_num
  exact_mod_cast h

/-- **A haunted ordinate has `H ≥ 3`** — the ghosts come in pairs.

If `p` is on the critical line with multiplicity one and its ordinate carries
anything else, then it carries at least *two* things else: any other zero `q`
at that ordinate is off-line (two on-line zeros at one ordinate are the same
point), so its mirror `refl q` is a third, distinct zero at the same ordinate.

This is the parity of `H` in the only form the accounting needs, and it is
what lets the link theorem charge a haunted zero **2** rather than `1`. -/
lemma three_le_H_of_haunted {p : ℝ × ℝ} (hp : p ∈ D.Z) (hon : p.1 = 1 / 2)
    (hcount : D.Z.count p = 1) (h2 : 2 ≤ D.H p.2) : 3 ≤ D.H p.2 := by
  classical
  set S := D.Z.filter fun q => q.2 = p.2 with hS
  have hpS : p ∈ S := mem_filter_self hp
  have hcS : Multiset.count p S = 1 := by
    have hfil : Multiset.count p (D.Z.filter fun q => q.2 = p.2) = Multiset.count p D.Z :=
      Multiset.count_filter_of_pos rfl
    rw [hS, hfil]; exact hcount
  -- some other zero shares the ordinate
  have hex : ∃ q ∈ S, q ≠ p := by
    by_contra hcon
    push_neg at hcon
    have hrep : S = Multiset.replicate (Multiset.card S) p :=
      Multiset.eq_replicate_card.2 hcon
    have hcc : Multiset.count p S = Multiset.card S := by
      conv_lhs => rw [hrep]
      simp
    rw [hcS] at hcc
    rw [hS] at hcc
    rw [ZeroData.H] at h2
    omega
  obtain ⟨q, hqS, hqp⟩ := hex
  have hqZ : q ∈ D.Z := (Multiset.mem_filter.1 hqS).1
  have hqγ : q.2 = p.2 := (Multiset.mem_filter.1 hqS).2
  -- it is off the line: two on-line zeros at one ordinate coincide
  have hqoff : q.1 ≠ 1 / 2 := by
    intro hq
    exact hqp (Prod.ext (by rw [hq, hon]) hqγ)
  -- its mirror is a third
  have hrZ : refl q ∈ D.Z := refl_mem hqZ
  have hrS : refl q ∈ S := Multiset.mem_filter.2 ⟨hrZ, by simpa using hqγ⟩
  have hrq : refl q ≠ q := refl_ne_self hqoff
  have hrp : refl q ≠ p := by
    intro h
    apply hqoff
    have : (refl q).1 = p.1 := by rw [h]
    rw [refl] at this
    simp only at this
    rw [hon] at this
    linarith
  have := three_le_card_of_three_mem hpS hqS hrS hqp hrp hrq
  rwa [ZeroData.H]

/-- **The two notions of "simple and on the critical line" differ by at most
`(N⊛ - N)/2`** — ghosts are charged double, because they come in pairs.

`NscStd - Nsc` counts the *haunted* zeros: on-line, of multiplicity one, but
sharing their ordinate with off-line zeros (which the functional equation
forces to come in pairs, so a haunted ordinate has `H ≥ 3`).  Each such zero
contributes at least `1` to `Σ_ρ (H(γ_ρ) - 1) = N⊛ - N`.

This resolves ISSUES.md #13 structurally rather than by convention: the gap
between the project's notion and the literature's is **the same coordinate the
whole program is about**.  Under `(★)` with constant `C` it is at most
`(C - 1)·N`, so any `C < 2` bounds it, and `C → 1` closes it.  No extra
analytic input is needed to compare the two numbers — only `(★)` itself. -/
theorem two_NscStd_le (D : ZeroData) :
    2 * (D.NscStd : ℤ) ≤ 2 * (D.Nsc : ℤ) + ((D.Nstar : ℤ) - (D.N : ℤ)) := by
  have hstd : (D.NscStd : ℤ)
      = (D.Z.map fun p => if p.1 = 1 / 2 ∧ D.Z.count p = 1 then (1 : ℤ) else 0).sum := by
    unfold ZeroData.NscStd; exact card_filter_eq_sum _ _
  have hsc : (D.Nsc : ℤ)
      = (D.Z.map fun p => if p.1 = 1 / 2 ∧ D.H p.2 = 1 then (1 : ℤ) else 0).sum :=
    Nsc_eq_sum D
  have hstar : (D.Nstar : ℤ) - (D.N : ℤ)
      = (D.Z.map fun p => ((D.H p.2 : ℤ) - 1)).sum := by
    have h1 : (D.Nstar : ℤ) = (D.Z.map fun p => (D.H p.2 : ℤ)).sum := by
      unfold ZeroData.Nstar; exact natCast_sum_map _ _
    have h2 : (D.N : ℤ) = (D.Z.map fun _ => (1 : ℤ)).sum := card_eq_sum_one _
    rw [h1, h2, ← Multiset.sum_map_sub]
  rw [hstd, hsc, hstar, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left,
    ← Multiset.sum_map_add]
  refine Multiset.sum_map_le_sum_map _ _ ?_
  intro p hp
  by_cases h1 : D.H p.2 = 1
  · have hz : ((D.H p.2 : ℤ)) - 1 = 0 := by rw [h1]; norm_num
    by_cases hstd' : p.1 = 1 / 2 ∧ D.Z.count p = 1
    · rw [if_pos hstd', if_pos ⟨hstd'.1, h1⟩, hz]; norm_num
    · rw [if_neg hstd', hz]; split_ifs <;> norm_num
  · have h2 : 2 ≤ D.H p.2 := by have := one_le_H hp; omega
    by_cases hstd' : p.1 = 1 / 2 ∧ D.Z.count p = 1
    · -- the haunted case: ghosts come in pairs, so H ≥ 3 and the term charges 2
      have h3 : 3 ≤ D.H p.2 := three_le_H_of_haunted hp hstd'.1 hstd'.2 h2
      have hz : (2 : ℤ) ≤ (D.H p.2 : ℤ) - 1 := by
        have : (3 : ℤ) ≤ (D.H p.2 : ℤ) := by exact_mod_cast h3
        linarith
      rw [if_pos hstd']; split_ifs <;> linarith
    · have hz : (1 : ℤ) ≤ (D.H p.2 : ℤ) - 1 := by
        have : (2 : ℤ) ≤ (D.H p.2 : ℤ) := by exact_mod_cast h2
        linarith
      rw [if_neg hstd']; split_ifs <;> linarith

/-- The zeros at a fixed ordinate, as a multiset; it is reflection-invariant. -/
lemma fiber_refl_inv (D : ZeroData) (γ : ℝ) :
    (D.Z.filter fun q => q.2 = γ).map refl = D.Z.filter fun q => q.2 = γ := by
  classical
  have h1 : (D.Z.filter fun q => q.2 = γ).map refl
      = (D.Z.map refl).filter fun q => q.2 = γ := by
    rw [Multiset.filter_map]
    rfl
  rw [h1, D.refl_inv]

/-- **The fiber structure `m = k + 2j` (List E, E14).**  At each ordinate the
off-line zeros come in mirror pairs, so the mass splits as
`(on-line mass) + 2·(mirror pairs)`.  Hence `k ≡ m (mod 2)`: **the parity of an
atom's mass is gauge-invariant**, and it reports the parity of the critical
mass sitting inside it. -/
lemma H_eq_online_add_two_mul (D : ZeroData) (γ : ℝ) :
    ∃ j : ℕ, D.H γ
      = Multiset.card ((D.Z.filter fun q => q.2 = γ).filter fun q => q.1 = 1 / 2) + 2 * j := by
  classical
  have hHS : D.H γ = Multiset.card (D.Z.filter fun q => q.2 = γ) := rfl
  set S := D.Z.filter (fun q => q.2 = γ) with hS
  have hSrefl : S.map refl = S := by rw [hS]; exact fiber_refl_inv D γ
  clear_value S
  refine ⟨Multiset.card (S.filter fun q => q.1 < 1 / 2), ?_⟩
  have hcardA : Multiset.card (S.filter fun q => 1 / 2 < q.1)
      = Multiset.card (S.filter fun q => q.1 < 1 / 2) := by
    conv_lhs => rw [← hSrefl]
    rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun q _ => ?_
    constructor
    · intro h; have h' : (1:ℝ)/2 < 1 - q.1 := h; linarith
    · intro h; show (1:ℝ)/2 < 1 - q.1; linarith
  have hsplit1 : S.filter (fun q => q.1 = 1 / 2) + S.filter (fun q => ¬ q.1 = 1 / 2) = S :=
    Multiset.filter_add_not _ _
  have hsplit2 : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => q.1 < 1 / 2)
      + (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => ¬ q.1 < 1 / 2)
      = S.filter fun q => ¬ q.1 = 1 / 2 := Multiset.filter_add_not _ _
  have hlt : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => q.1 < 1 / 2)
      = S.filter fun q => q.1 < 1 / 2 := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun q _ =>
      ⟨fun h => h.1, fun h => ⟨h, by intro he; rw [he] at h; linarith⟩⟩
  have hgt : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => ¬ q.1 < 1 / 2)
      = S.filter fun q => 1 / 2 < q.1 := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun q _ => ?_
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.1 h.1) (Ne.symm h.2)
    · intro h; exact ⟨not_lt.2 h.le, by intro he; rw [he] at h; exact lt_irrefl _ h⟩
  have hcards := congrArg Multiset.card hsplit1
  rw [Multiset.card_add, ← hsplit2, Multiset.card_add, hlt, hgt, hcardA] at hcards
  rw [hHS, ← hcards]
  ring

/-- **Every odd-mass atom contains a critical zero** (W1's parity, landed).
`k ≡ m (mod 2)`, so an ordinate of odd mass has odd — hence nonzero — critical
mass.  This is a bound on *critical* zeros that reads only the gauge-invariant
data, the first in the project. -/
theorem odd_mass_inhabited (D : ZeroData) {γ : ℝ} (h : Odd (D.H γ)) :
    ∃ p ∈ D.Z, p.1 = 1 / 2 ∧ p.2 = γ := by
  classical
  obtain ⟨j, hj⟩ := H_eq_online_add_two_mul D γ
  set k := Multiset.card ((D.Z.filter fun q => q.2 = γ).filter fun q => q.1 = 1 / 2) with hk
  have hkpos : 0 < k := by
    rcases h with ⟨t, ht⟩
    omega
  obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.1 hkpos
  have h1 := Multiset.mem_filter.1 hp
  have h2 := Multiset.mem_filter.1 h1.1
  exact ⟨p, h2.1, h1.2, h2.2⟩

/-- **`N_critical ≥ #{odd atoms}`.**  Distinct odd-mass ordinates house
distinct critical zeros, so the count of critical zeros dominates the number of
odd atoms — a lower bound on a *horizontal* quantity read entirely off the
gauge-invariant data `μ_T`.

Stated for any finite set `G` of odd-mass ordinates. -/
theorem card_odd_atoms_le_critical (D : ZeroData) (G : Finset ℝ)
    (hG : ∀ γ ∈ G, Odd (D.H γ)) :
    G.card ≤ Multiset.card (D.Z.filter fun p => p.1 = 1 / 2) := by
  classical
  have hex : ∀ γ : ℝ, ∃ p : ℝ × ℝ, γ ∈ G → (p ∈ D.Z ∧ p.1 = 1 / 2 ∧ p.2 = γ) := by
    intro γ
    by_cases hγ : γ ∈ G
    · obtain ⟨p, h1, h2, h3⟩ := odd_mass_inhabited D (hG γ hγ)
      exact ⟨p, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨((0:ℝ), (0:ℝ)), fun h => absurd h hγ⟩
  choose f hf using hex
  have hmaps : ∀ γ ∈ G, f γ ∈ (D.Z.filter fun p => p.1 = 1 / 2).toFinset := by
    intro γ hγ
    obtain ⟨h1, h2, _⟩ := hf γ hγ
    exact Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨h1, h2⟩)
  have hinj : ∀ γ₁ ∈ G, ∀ γ₂ ∈ G, f γ₁ = f γ₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hfe
    have e₁ := (hf γ₁ h₁).2.2
    have e₂ := (hf γ₂ h₂).2.2
    rw [← e₁, ← e₂, hfe]
  calc G.card ≤ (D.Z.filter fun p => p.1 = 1 / 2).toFinset.card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ Multiset.card (D.Z.filter fun p => p.1 = 1 / 2) := Multiset.toFinset_card_le _

/-- **The haunted-ordinate census (W6).**  A haunted ordinate costs **six**,
not two, in `N⊛ - N`.

A haunted ordinate has mass `m ≥ 3` (parity: `m = 1 + 2j`, `j ≥ 1`), and an
ordinate of mass `m` contributes `m(m-1)` to `Σ_ρ (H(γ_ρ) - 1) = N⊛ - N` — so
`m(m-1) ≥ 6`, while the census counts it once.  The termwise proof of
`two_NscStd_le` could only charge the haunted zero's *own* term; grouping by
ordinate collects its neighbours' terms too.

Stated for any finite set `G` of ordinates of mass `≥ 3`. -/
theorem six_mul_card_le_Nstar_sub_N (D : ZeroData) (G : Finset ℝ)
    (hG : ∀ γ ∈ G, 3 ≤ D.H γ) (hsub : G ⊆ D.ordinates.toFinset) :
    6 * G.card + D.N ≤ D.Nstar := by
  classical
  have hcount : ∀ γ ∈ G, 3 ≤ D.ordinates.count γ := by
    intro γ hγ; rw [← H_eq_count]; exact hG γ hγ
  -- `N⊛` and `N` as sums over the distinct ordinates
  have hNstar : D.Nstar = ∑ γ ∈ D.ordinates.toFinset,
      D.ordinates.count γ * D.ordinates.count γ := by
    obtain ⟨-, h2⟩ := N_Nstar_ordinate_functional D
    rw [h2, Finset.sum_multiset_map_count]
    simp [smul_eq_mul]
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.ordinates.count γ := by
    obtain ⟨h1, -⟩ := N_Nstar_ordinate_functional D
    rw [h1, ← Multiset.toFinset_sum_count_eq]
  -- termwise: an atom of mass `c` pays `c²`, which covers `c` plus `6` when `c ≥ 3`
  have key : ∑ γ ∈ D.ordinates.toFinset,
      (D.ordinates.count γ + if γ ∈ G then 6 else 0)
      ≤ ∑ γ ∈ D.ordinates.toFinset, D.ordinates.count γ * D.ordinates.count γ := by
    refine Finset.sum_le_sum fun γ _ => ?_
    by_cases hγ : γ ∈ G
    · have h3 : 3 ≤ D.ordinates.count γ := hcount γ hγ
      simp only [hγ, if_pos]
      nlinarith [h3]
    · simp only [hγ, if_neg, add_zero, not_false_iff]
      nlinarith [Nat.zero_le (D.ordinates.count γ)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    Finset.sum_const] at key
  rw [hNstar, hN]
  simpa [Nat.smul_one_eq_cast, mul_comm, add_comm] using key

/-- The haunted zeros: on-line, multiplicity one, ordinate not alone. -/
noncomputable def hauntedSet (D : ZeroData) : Multiset (ℝ × ℝ) :=
  (D.Z.filter fun p => p.1 = 1 / 2 ∧ D.Z.count p = 1).filter fun p => ¬ D.H p.2 = 1

/-- `NscStd = Nsc + #haunted` — the row gap *is* the haunted count. -/
theorem NscStd_eq_Nsc_add_haunted (D : ZeroData) :
    D.NscStd = D.Nsc + Multiset.card D.hauntedSet := by
  classical
  set S := D.Z.filter (fun p => p.1 = 1 / 2 ∧ D.Z.count p = 1) with hS
  have hNsc : D.Nsc = Multiset.card (S.filter fun p => D.H p.2 = 1) := by
    rw [hS, Multiset.filter_filter, ZeroData.Nsc]
    congr 1
    refine Multiset.filter_congr fun p hp => ?_
    have hkey : D.H p.2 = 1 → Multiset.count p D.Z = 1 := count_eq_one_of_H_eq_one hp
    constructor
    · intro h; tauto
    · intro h
      have hH : D.H p.2 = 1 := by tauto
      have hc := hkey hH
      tauto
  have hsplit : (S.filter fun p => D.H p.2 = 1) + (S.filter fun p => ¬ D.H p.2 = 1) = S :=
    Multiset.filter_add_not _ _
  have := congrArg Multiset.card hsplit
  rw [Multiset.card_add] at this
  rw [ZeroData.NscStd, ← hS, ← this, hNsc, ZeroData.hauntedSet, ← hS]

/-- Every haunted zero has multiplicity one, so the haunted set is duplicate-free. -/
lemma hauntedSet_nodup (D : ZeroData) : D.hauntedSet.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro p
  by_cases hp : p ∈ D.hauntedSet
  · have h1 := Multiset.mem_filter.1 hp
    have h2 := Multiset.mem_filter.1 h1.1
    calc Multiset.count p D.hauntedSet ≤ Multiset.count p D.Z := by
          refine Multiset.count_le_of_le _ ?_
          exact le_trans (Multiset.filter_le _ _) (Multiset.filter_le _ _)
      _ = 1 := h2.2.2
  · simp [Multiset.count_eq_zero.2 hp]

/-- **The census bound, cashed: a haunted ordinate costs six.**

`6·(NscStd − Nsc) + N ≤ N⊛`, i.e. the row gap is at most `(N⊛ − N)/6` — three
times sharper than `two_NscStd_le`, because grouping by ordinate collects the
ghosts' terms as well as the haunted zero's own. -/
theorem six_mul_NscStd_le (D : ZeroData) :
    6 * D.NscStd + D.N ≤ 6 * D.Nsc + D.Nstar := by
  classical
  set G := D.hauntedSet.toFinset.image Prod.snd with hG
  have hinj : Set.InjOn Prod.snd (↑D.hauntedSet.toFinset : Set (ℝ × ℝ)) := by
    intro a ha b hb hab
    have ha' := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 (Finset.mem_coe.1 ha))
    have hb' := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 (Finset.mem_coe.1 hb))
    exact Prod.ext (by rw [(Multiset.mem_filter.1 ha'.1).2.1,
      (Multiset.mem_filter.1 hb'.1).2.1]) hab
  have hcard : Multiset.card D.hauntedSet = G.card := by
    rw [hG, Finset.card_image_of_injOn hinj,
      Multiset.toFinset_card_of_nodup (hauntedSet_nodup D)]
  have hG3 : ∀ γ ∈ G, 3 ≤ D.H γ := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hγ
    have hp' := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hp)
    have hpZ := Multiset.mem_filter.1 hp'.1
    have h2 : 2 ≤ D.H p.2 := by
      have := one_le_H hpZ.1
      omega
    exact three_le_H_of_haunted hpZ.1 hpZ.2.1 hpZ.2.2 h2
  have hsub : G ⊆ D.ordinates.toFinset := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hγ
    have hp' := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hp)
    have hpZ := Multiset.mem_filter.1 hp'.1
    exact Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem _ hpZ.1)
  have hkey := six_mul_card_le_Nstar_sub_N D G hG3 hsub
  rw [NscStd_eq_Nsc_add_haunted, hcard]
  omega

/-! ### Resolution independence (List A, A2)

`H` counts zeros at *exactly* one ordinate.  A2 asks whether that infinite
vertical resolution is load-bearing, given that the certificate class cannot
resolve below `1/log T` anyway.  It is not: the mirror map preserves ordinates
**exactly**, so an off-line zero's twin lies at distance `0` and is therefore
inside *every* cluster containing it.  Both structural facts below hold at every
radius `r ≥ 0`, with `H = Hr 0`. -/

/-- `Hr r γ`: the mass of the cluster of radius `r` around `γ`. -/
noncomputable def Hr (D : ZeroData) (r γ : ℝ) : ℕ :=
  Multiset.card (D.Z.filter fun p => |p.2 - γ| ≤ r)

lemma Hr_zero (D : ZeroData) (γ : ℝ) : D.Hr 0 γ = D.H γ := by
  classical
  rw [Hr, ZeroData.H]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  constructor
  · intro h
    have h0 : p.2 - γ = 0 := by
      have := abs_nonneg (p.2 - γ); have := abs_le.1 h; linarith [this.1, this.2]
    linarith [sub_eq_zero.1 h0]
  · intro h; simp [h]

/-- **An `r`-isolated zero is critical, at every radius.**  The mirror sits at
vertical distance `0`, so it would be in the same cluster. -/
theorem on_line_of_Hr_eq_one {D : ZeroData} {p : ℝ × ℝ} (hp : p ∈ D.Z) {r : ℝ}
    (hr : 0 ≤ r) (h : D.Hr r p.2 = 1) : p.1 = 1 / 2 := by
  classical
  by_contra hoff
  have hmem : p ∈ D.Z.filter fun q => |q.2 - p.2| ≤ r :=
    Multiset.mem_filter.2 ⟨hp, by simpa using hr⟩
  have hmem' : refl p ∈ D.Z.filter fun q => |q.2 - p.2| ≤ r :=
    Multiset.mem_filter.2 ⟨refl_mem hp, by simpa using hr⟩
  have h2 : 2 ≤ D.Hr r p.2 :=
    two_le_card_of_two_mem hmem hmem' (refl_ne_self hoff)
  omega

/-- **A cluster of odd mass contains a critical zero, at every radius** — the
off-line zeros of a cluster pair up *inside* it, so parity is
resolution-independent. -/
theorem odd_Hr_inhabited {D : ZeroData} {r γ : ℝ} (h : Odd (D.Hr r γ)) :
    ∃ p ∈ D.Z, p.1 = 1 / 2 ∧ |p.2 - γ| ≤ r := by
  classical
  set S := D.Z.filter (fun q => |q.2 - γ| ≤ r) with hS
  have hSrefl : S.map refl = S := by
    have h1 : S.map refl = (D.Z.map refl).filter fun q => |q.2 - γ| ≤ r := by
      rw [hS, Multiset.filter_map]; rfl
    rw [h1, D.refl_inv]
  have hHS : D.Hr r γ = Multiset.card S := by rw [Hr, hS]
  clear_value S
  have hcardA : Multiset.card (S.filter fun q => 1 / 2 < q.1)
      = Multiset.card (S.filter fun q => q.1 < 1 / 2) := by
    conv_lhs => rw [← hSrefl]
    rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun q _ => ?_
    constructor
    · intro h'; have h'' : (1:ℝ)/2 < 1 - q.1 := h'; linarith
    · intro h'; show (1:ℝ)/2 < 1 - q.1; linarith
  have h1 : S.filter (fun q => q.1 = 1 / 2) + S.filter (fun q => ¬ q.1 = 1 / 2) = S :=
    Multiset.filter_add_not _ _
  have h2 : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => q.1 < 1 / 2)
      + (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => ¬ q.1 < 1 / 2)
      = S.filter fun q => ¬ q.1 = 1 / 2 := Multiset.filter_add_not _ _
  have hlt : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => q.1 < 1 / 2)
      = S.filter fun q => q.1 < 1 / 2 := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun q _ =>
      ⟨fun h' => h'.1, fun h' => ⟨h', by intro he; rw [he] at h'; linarith⟩⟩
  have hgt : (S.filter fun q => ¬ q.1 = 1 / 2).filter (fun q => ¬ q.1 < 1 / 2)
      = S.filter fun q => 1 / 2 < q.1 := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun q _ => ?_
    constructor
    · intro h'; exact lt_of_le_of_ne (not_lt.1 h'.1) (Ne.symm h'.2)
    · intro h'; exact ⟨not_lt.2 h'.le, by intro he; rw [he] at h'; exact lt_irrefl _ h'⟩
  have hc := congrArg Multiset.card h1
  rw [Multiset.card_add, ← h2, Multiset.card_add, hlt, hgt, hcardA] at hc
  have hpos : 0 < Multiset.card (S.filter fun q => q.1 = 1 / 2) := by
    rcases h with ⟨t, ht⟩
    rw [hHS] at ht
    omega
  obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have hf := Multiset.mem_filter.1 hp
  rw [hS] at hf
  have hf2 := Multiset.mem_filter.1 hf.1
  exact ⟨p, hf2.1, hf.2, hf2.2⟩

/-- **Single occupancy (List E, E15).**  `μ_T` is a *simple* measure — every
ordinate carries exactly one zero — if and only if every zero is on the
critical line **and** simple.

One condition on one object yields both classical conclusions of RH: the
criticality is not a second demand but a corollary of the loneliness, because a
zero alone at its height has nowhere to put its reflection but on itself.

(Note the equivalence is with RH **and** simplicity: RH alone permits an atom
of mass two — a double zero on the line — so simplicity of `μ_T` is strictly
the stronger statement.  The project's `N_sc` is exactly the count of
single-occupancy ordinates, so `N_sc = N` *is* this condition.) -/
theorem ordinates_simple_iff (D : ZeroData) :
    (∀ γ ∈ D.ordinates, D.ordinates.count γ = 1) ↔
      (∀ p ∈ D.Z, p.1 = 1 / 2 ∧ D.Z.count p = 1) := by
  constructor
  · intro h p hp
    have hγ : p.2 ∈ D.ordinates := Multiset.mem_map_of_mem _ hp
    have hH : D.H p.2 = 1 := by rw [H_eq_count]; exact h _ hγ
    exact ⟨on_line_of_H_eq_one hp hH, count_eq_one_of_H_eq_one hp hH⟩
  · intro h γ hγ
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hγ
    rw [← H_eq_count]
    by_contra hne
    have h2 : 2 ≤ D.H p.2 := by have := one_le_H hp; omega
    -- a second zero at this ordinate must be on-line too, hence equal to `p`
    obtain ⟨q, hqS, hqp⟩ : ∃ q ∈ D.Z.filter fun r => r.2 = p.2, q ≠ p := by
      by_contra hcon
      push_neg at hcon
      have hrep : D.Z.filter (fun r => r.2 = p.2)
          = Multiset.replicate (Multiset.card (D.Z.filter fun r => r.2 = p.2)) p :=
        Multiset.eq_replicate_card.2 hcon
      have hcc : Multiset.count p (D.Z.filter fun r => r.2 = p.2)
          = Multiset.card (D.Z.filter fun r => r.2 = p.2) := by
        conv_lhs => rw [hrep]
        simp
      have hfil : Multiset.count p (D.Z.filter fun r => r.2 = p.2) = Multiset.count p D.Z :=
        Multiset.count_filter_of_pos rfl
      rw [hfil, (h p hp).2] at hcc
      rw [ZeroData.H] at h2
      omega
    have hqZ : q ∈ D.Z := (Multiset.mem_filter.1 hqS).1
    have hqγ : q.2 = p.2 := (Multiset.mem_filter.1 hqS).2
    exact hqp (Prod.ext (by rw [(h q hqZ).1, (h p hp).1]) hqγ)

/-- The ledger's target, in the native coordinate: `N_sc = N` **is** single
occupancy.  `(★)` with `C → 1` is its averaged form. -/
theorem Nsc_eq_N_iff (D : ZeroData) :
    D.Nsc = D.N ↔ ∀ p ∈ D.Z, p.1 = 1 / 2 ∧ D.Z.count p = 1 := by
  rw [← ordinates_simple_iff]
  constructor
  · intro h γ hγ
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hγ
    rw [← H_eq_count]
    by_contra hne
    have hsub : D.Z.filter (fun r => r.1 = 1 / 2 ∧ D.H r.2 = 1) ≤ D.Z := Multiset.filter_le _ _
    have heq : D.Z.filter (fun r => r.1 = 1 / 2 ∧ D.H r.2 = 1) = D.Z :=
      Multiset.eq_of_le_of_card_le hsub (le_of_eq h.symm)
    have : p ∈ D.Z.filter fun r => r.1 = 1 / 2 ∧ D.H r.2 = 1 := by rw [heq]; exact hp
    exact hne (Multiset.mem_filter.1 this).2.2
  · intro h
    have heq : D.Z.filter (fun r => r.1 = 1 / 2 ∧ D.H r.2 = 1) = D.Z := by
      refine Multiset.filter_eq_self.2 fun p hp => ?_
      have hγ : p.2 ∈ D.ordinates := Multiset.mem_map_of_mem _ hp
      have hH : D.H p.2 = 1 := by rw [H_eq_count]; exact h _ hγ
      exact ⟨on_line_of_H_eq_one hp hH, hH⟩
    unfold ZeroData.Nsc ZeroData.N
    rw [heq]

/-- The trivial floor `N⊛ ≥ N`: every zero sees itself.  This pins `C ≥ 1`
and, in `Fujii.lean`, forces a lower bound on any effective constant. -/
theorem N_le_Nstar (D : ZeroData) : (D.N : ℤ) ≤ D.Nstar := by
  have := N_add_Noff_le_Nstar D
  have : (0 : ℤ) ≤ D.Noff := Int.natCast_nonneg _
  omega

end ZeroData

end Riemann
