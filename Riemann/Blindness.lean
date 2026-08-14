/-
# The blindness cluster, made relative (W28, tri-read `{4,7,8}`)

Three of the census's eleven deaths were classified *identically* by three
independent readers with three different axes — the plane, the Fable blind
dichotomy, and the context-v2 coupling read.  They are:

* `#4` — the certificate provably cannot separate a double zero from an
  off-line pair, **at depth → 0**;
* `#7` — the price of depth-shaped input is exactly zero: `μ_T` has no `β`
  coordinate;
* `#8` — the mirror preserves ordinates *exactly*, so no vertical smoothing
  separates a zero from its twin.

`Gauge.lean` exhibits the boundary for one pair.  What W28 predicts, and what
this file proves, is stronger and is the reason the cluster is stable: the
inability is **not** a property of the axioms currently assumed.  It survives
adding *any* further hypothesis that is itself a functional of `μ_T` — which is
what both candidate atom bundles are, until one of them is shown not to be.

Nothing here is about `ζ`.  That is the point: the statements hold for every
reflection-symmetric configuration, Davenport–Heilbronn included.
-/
import Riemann.Gauge

namespace Riemann
namespace Blindness

open Multiset

/-! ### The relativisation

A hypothesis is `μ_T`-invariant when it cannot itself tell two configurations
with the same ordinate measure apart.  Every functional of `μ_T` — every
pair-correlation statement, every bandwidth-limited certificate, everything
`Basic.lean` proves — is of this kind. -/

/-- `B` is a `μ_T`-invariant hypothesis: it factors through the ordinate
measure. -/
def MuInvariant (B : ZeroData → Prop) : Prop :=
  ∀ D D' : ZeroData, D.ordinates = D'.ordinates → (B D ↔ B D')

/-- Anything that factors through `μ_T` is `μ_T`-invariant.  This is the
sanity check that the definition is not vacuous: it is satisfied by every
predicate the certificate class can express. -/
theorem muInvariant_of_factors {α : Type*} (g : Multiset ℝ → α) (p : α → Prop) :
    MuInvariant fun D => p (g D.ordinates) := by
  intro D D' h
  show p (g D.ordinates) ↔ p (g D'.ordinates)
  rw [h]

/-! #### The class is deductively closed

This is what upgrades a *blindness* result into an *independence* result.  A
statement "no hypothesis of class `𝒞` decides `P`" is only as strong as `𝒞`'s
closure properties: if `𝒞` is not closed under conjunction and implication,
then a *consequence* of several `𝒞`-hypotheses might decide `P` even though no
single one does.  The `μ_T`-invariant predicates are a Boolean subalgebra and
are closed under arbitrary conjunction, so no theory axiomatised by them
decides what none of them decides. -/

theorem MuInvariant.and {B C : ZeroData → Prop} (hB : MuInvariant B)
    (hC : MuInvariant C) : MuInvariant fun D => B D ∧ C D :=
  fun D D' h => and_congr (hB D D' h) (hC D D' h)

theorem MuInvariant.or {B C : ZeroData → Prop} (hB : MuInvariant B)
    (hC : MuInvariant C) : MuInvariant fun D => B D ∨ C D :=
  fun D D' h => or_congr (hB D D' h) (hC D D' h)

theorem MuInvariant.not {B : ZeroData → Prop} (hB : MuInvariant B) :
    MuInvariant fun D => ¬ B D :=
  fun D D' h => not_congr (hB D D' h)

theorem MuInvariant.imp {B C : ZeroData → Prop} (hB : MuInvariant B)
    (hC : MuInvariant C) : MuInvariant fun D => B D → C D :=
  fun D D' h => imp_congr (hB D D' h) (hC D D' h)

/-- **Closed under arbitrary conjunction** — so a whole *theory* of
`μ_T`-invariant axioms is itself a `μ_T`-invariant hypothesis. -/
theorem MuInvariant.forall {ι : Sort*} {B : ι → ZeroData → Prop}
    (h : ∀ i, MuInvariant (B i)) : MuInvariant fun D => ∀ i, B i D :=
  fun D D' hD => forall_congr' fun i => h i D D' hD

/-- **The gauge pair is invisible to every `μ_T`-invariant hypothesis.** -/
theorem muInvariant_blind {B : ZeroData → Prop} (hB : MuInvariant B) :
    B Gauge.triple ↔ B Gauge.haunted :=
  hB _ _ Gauge.ordinates_eq

/-- **`#7`, relativised.**  No `μ_T`-invariant hypothesis, however strong, lets
`NscStd` be computed from `μ_T` — *provided the hypothesis admits either of the
two configurations at all*.  Adding axioms about the source cannot help unless
those axioms are themselves able to see `β`.

This is the exact sense in which the price of depth-shaped input is zero: the
obstruction is a property of the *functional*, and hypotheses of the class
compose with it without moving it. -/
theorem no_muInvariant_bundle_computes_NscStd
    (B : ZeroData → Prop) (hB : MuInvariant B)
    (hne : B Gauge.triple ∨ B Gauge.haunted) :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, B D → D.NscStd = f D.ordinates := by
  rintro ⟨f, hf⟩
  have ht : B Gauge.triple := hne.elim id fun h => (muInvariant_blind hB).2 h
  have hh : B Gauge.haunted := (muInvariant_blind hB).1 ht
  have h0 : (0 : ℕ) = f Gauge.triple.ordinates := by
    rw [← Gauge.NscStd_triple]; exact hf _ ht
  have h1 : (1 : ℕ) = f Gauge.haunted.ordinates := by
    rw [← Gauge.NscStd_haunted]; exact hf _ hh
  rw [← Gauge.ordinates_eq, ← h0] at h1
  exact absurd h1 (by norm_num)

/-- The unconditional corollary: with no hypothesis at all (`B = True`),
`NscStd` is not an ordinate functional. -/
theorem NscStd_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, D.NscStd = f D.ordinates := by
  intro ⟨f, hf⟩
  exact no_muInvariant_bundle_computes_NscStd (fun _ => True)
    (fun _ _ _ => Iff.rfl) (Or.inl trivial) ⟨f, fun D _ => hf D⟩

/-- **The positive form — what a bundle's work actually is.**  If a hypothesis
`B` does determine `NscStd` from `μ_T`, then `B` must *exclude* one of the two
legitimate reflection-symmetric configurations.  A useful atom bundle does not
compute the missing coordinate; it rules out the world in which the coordinate
is ambiguous. -/
theorem separating_bundle_excludes (B : ZeroData → Prop)
    (hsep : ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, B D → D.NscStd = f D.ordinates) :
    ¬ (B Gauge.triple ∧ B Gauge.haunted) := by
  rintro ⟨ht, hh⟩
  obtain ⟨f, hf⟩ := hsep
  have h0 : (0 : ℕ) = f Gauge.triple.ordinates := by
    rw [← Gauge.NscStd_triple]; exact hf _ ht
  have h1 : (1 : ℕ) = f Gauge.haunted.ordinates := by
    rw [← Gauge.NscStd_haunted]; exact hf _ hh
  rw [← Gauge.ordinates_eq, ← h0] at h1
  exact absurd h1 (by norm_num)

/-- **Independence, properly stated.**  No theory axiomatised by
`μ_T`-invariant sentences computes `NscStd` from `μ_T` — not merely no single
axiom.  This is the two-model argument at certificate scale: `Gauge.triple` and
`Gauge.haunted` are two structures agreeing on everything the class can state
and disagreeing on the target. -/
theorem no_muInvariant_theory_computes_NscStd {ι : Sort*} (B : ι → ZeroData → Prop)
    (h : ∀ i, MuInvariant (B i))
    (hne : (∀ i, B i Gauge.triple) ∨ (∀ i, B i Gauge.haunted)) :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, (∀ i, B i D) → D.NscStd = f D.ordinates :=
  no_muInvariant_bundle_computes_NscStd _ (MuInvariant.forall h) hne

/-! ### `#4` — the double zero and the mirror pair, uniformly in the depth

`Gauge.lean` fixes one off-line pair at `1/4, 3/4`.  The certified reason for
`#4` says the degeneracy persists *as the depth tends to zero*, so the witness
must be a family, not a point. -/

/-- A double zero on the critical line at height `0`. -/
noncomputable def doubleZero : ZeroData where
  Z := Multiset.replicate 2 ((1/2 : ℝ), (0 : ℝ))
  refl_inv := by
    rw [Multiset.map_replicate]
    norm_num [refl]

/-- A mirror pair at height `0` with abscissae `a` and `1 - a`: the depth is
`|a - 1/2|`, and `a → 1/2` is the depth-zero limit. -/
noncomputable def depthPair (a : ℝ) : ZeroData where
  Z := {(a, (0 : ℝ)), (1 - a, (0 : ℝ))}
  refl_inv := by
    show Multiset.map refl ((a, (0:ℝ)) ::ₘ ((1 - a : ℝ), (0:ℝ)) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_cons]
    have h1 : refl (a, (0:ℝ)) = ((1 - a : ℝ), (0:ℝ)) := rfl
    have h2 : refl ((1 - a : ℝ), (0:ℝ)) = (a, (0:ℝ)) := by
      show ((1 - (1 - a) : ℝ), (0:ℝ)) = (a, (0:ℝ))
      norm_num
    rw [h1, h2, Multiset.map_zero]
    exact Multiset.cons_swap _ _ _

@[simp] lemma doubleZero_ordinates : doubleZero.ordinates = Multiset.replicate 2 (0:ℝ) := by
  show Multiset.map Prod.snd (Multiset.replicate 2 ((1/2 : ℝ), (0:ℝ))) = _
  rw [Multiset.map_replicate]

@[simp] lemma depthPair_ordinates (a : ℝ) :
    (depthPair a).ordinates = Multiset.replicate 2 (0:ℝ) := by
  show Multiset.map Prod.snd ((a, (0:ℝ)) ::ₘ ((1 - a : ℝ), (0:ℝ)) ::ₘ 0) = _
  simp [Multiset.replicate_succ]

lemma doubleZero_Noff : doubleZero.Noff = 0 := by
  classical
  unfold ZeroData.Noff
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro p hp hc
  exact hc (congrArg Prod.fst (Multiset.eq_of_mem_replicate hp))

lemma depthPair_Noff {a : ℝ} (ha : a ≠ 1/2) : (depthPair a).Noff = 2 := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.1 ≠ 1/2)
      ((a, (0:ℝ)) ::ₘ ((1 - a : ℝ), (0:ℝ)) ::ₘ 0)) = 2
  norm_num [Multiset.filter_cons, Multiset.filter_singleton, ha, ha']

/-- **`#4`, uniformly in the depth.**  For *every* `a ≠ 1/2` — however close to
the critical line — the mirror pair and the double zero carry the same `μ_T`
and different off-line content.  There is no depth at which the ordinate
measure begins to separate them, so no limit is available: the degeneracy is
not a small-parameter artefact but an identity. -/
theorem double_vs_pair_indistinguishable (a : ℝ) (ha : a ≠ 1/2) :
    doubleZero.ordinates = (depthPair a).ordinates ∧
      doubleZero.Noff ≠ (depthPair a).Noff := by
  refine ⟨by simp, ?_⟩
  rw [doubleZero_Noff, depthPair_Noff ha]
  norm_num

/-- And the relativised form: `N_off` is not computable from `μ_T` under any
`μ_T`-invariant hypothesis admitting a single mirror pair. -/
theorem no_muInvariant_bundle_computes_Noff
    (B : ZeroData → Prop) (hB : MuInvariant B) {a : ℝ} (ha : a ≠ 1/2)
    (hne : B doubleZero ∨ B (depthPair a)) :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, B D → D.Noff = f D.ordinates := by
  rintro ⟨f, hf⟩
  have hord : doubleZero.ordinates = (depthPair a).ordinates := by simp
  have hd : B doubleZero := hne.elim id fun h => (hB _ _ hord).2 h
  have hp : B (depthPair a) := (hB _ _ hord).1 hd
  have h0 : (0 : ℕ) = f doubleZero.ordinates := by
    rw [← doubleZero_Noff]; exact hf _ hd
  have h2 : (2 : ℕ) = f (depthPair a).ordinates := by
    rw [← depthPair_Noff ha]; exact hf _ hp
  rw [← hord, ← h0] at h2
  exact absurd h2 (by norm_num)

/-! ### `#8` — the mirror is vertically invisible at every resolution -/

/-- **The mirror preserves `μ_T` exactly.**  Reflection is a symmetry of the
ordinate measure, not merely of the zero set: it acts trivially on everything
the certificate class can see. -/
theorem ordinates_refl_invariant (D : ZeroData) :
    (D.Z.map refl).map Prod.snd = D.ordinates := by
  rw [D.refl_inv]
  rfl

/-- **No vertical smoothing separates a zero from its twin.**  At *every*
radius `r ≥ 0`, an off-line zero's cluster already contains its mirror, because
the mirror sits at vertical distance exactly `0`.  Widening the window cannot
create the separation; `r = 0` is not a degenerate case but the general one. -/
theorem two_le_Hr_of_off_line {D : ZeroData} {p : ℝ × ℝ} (hp : p ∈ D.Z)
    (hoff : p.1 ≠ 1/2) {r : ℝ} (hr : 0 ≤ r) : 2 ≤ D.Hr r p.2 := by
  classical
  have hmem : p ∈ D.Z.filter fun q => |q.2 - p.2| ≤ r :=
    Multiset.mem_filter.2 ⟨hp, by simpa using hr⟩
  have hmem' : refl p ∈ D.Z.filter fun q => |q.2 - p.2| ≤ r :=
    Multiset.mem_filter.2 ⟨ZeroData.refl_mem hp, by simpa using hr⟩
  exact two_le_card_of_two_mem hmem hmem' (refl_ne_self hoff)


/-! ### What a bundle must look like to help

`separating_bundle_excludes` says the work is exclusion.  This section exhibits
the exclusion that actually does the job, and identifies its defining feature:
**it is not `μ_T`-invariant.**  That is the shape the atom bundles must have if
they are to matter, and it is a checkable condition rather than a slogan. -/

/-- The Riemann hypothesis, as a predicate on a configuration. -/
def OnLine (D : ZeroData) : Prop := ∀ p ∈ D.Z, p.1 = 1/2

/-- **RH is not a `μ_T`-invariant hypothesis**, and the gauge pair is the
witness: `triple` satisfies it, `haunted` does not, and they carry the same
ordinate measure.  This is the certified form of "RH is outside the certificate
class" — not a claim about proof technique, but a property of the predicate. -/
theorem onLine_not_muInvariant : ¬ MuInvariant OnLine := by
  intro h
  have hh : OnLine Gauge.haunted := (h _ _ Gauge.ordinates_eq).1 (by
    intro p hp
    exact congrArg Prod.fst (Multiset.eq_of_mem_replicate hp))
  have : ((1/4 : ℝ), (0:ℝ)).1 = 1/2 := hh _ (by
    show ((1/4 : ℝ), (0:ℝ)) ∈ (((1/2 : ℝ), (0:ℝ)) ::ₘ ((1/4 : ℝ), (0:ℝ)) ::ₘ
      ((3/4 : ℝ), (0:ℝ)) ::ₘ 0)
    simp)
  norm_num at this

/-- Under `OnLine`, two zeros sharing an ordinate share their abscissa too, so
they are the same point: horizontal multiplicity collapses onto vertical. -/
lemma H_eq_count_of_onLine {D : ZeroData} (h : OnLine D) {p : ℝ × ℝ}
    (hp : p ∈ D.Z) : D.H p.2 = D.Z.count p := by
  classical
  have hfil : (D.Z.filter fun q => q.2 = p.2) = D.Z.filter fun q => q = p := by
    refine Multiset.filter_congr fun q hq => ?_
    constructor
    · intro hq2
      exact Prod.ext ((h q hq).trans (h p hp).symm) hq2
    · intro hqp; rw [hqp]
  rw [ZeroData.H, hfil, Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun q _ => eq_comm

/-- **The exclusion works.**  Under `OnLine` the two rows of the ledger
coincide, so `NscStd` *becomes* an ordinate functional — the very thing
`no_muInvariant_bundle_computes_NscStd` forbids for every `μ_T`-invariant
hypothesis.

Read together, the two theorems are a specification — and a narrow one, stated
carefully.  **Non-`μ_T`-invariance is necessary to compute `NscStd` (or `N_off`)
from `μ_T` exactly.**  It is *not* necessary to be useful: an effective Fujii
constant is `μ_T`-invariant and would move both rows of the ledger.  What a
`μ_T`-invariant hypothesis can never do, however deep its arithmetic, is close
the row gap identically — it composes with the blindness and inherits it. -/
theorem NscStd_eq_Nsc_of_onLine {D : ZeroData} (h : OnLine D) :
    D.NscStd = D.Nsc := by
  classical
  unfold ZeroData.NscStd ZeroData.Nsc
  congr 1
  refine Multiset.filter_congr fun p hp => ?_
  rw [H_eq_count_of_onLine h hp]

/-- …and therefore, under `OnLine`, it is computed from `μ_T` alone. -/
theorem NscStd_ordinate_functional_of_onLine {D : ZeroData} (h : OnLine D) :
    D.NscStd = Multiset.card (D.ordinates.filter fun γ => D.ordinates.count γ = 1) := by
  rw [NscStd_eq_Nsc_of_onLine h, ZeroData.Nsc_eq_ordinate_functional]

end Blindness
end Riemann
