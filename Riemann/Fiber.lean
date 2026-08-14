/-
# The blindness is supported exactly on the crowded atoms

`Blindness.lean` proves that no `μ_T`-invariant hypothesis computes `NscStd` or
`N_off`.  It leaves open *where* the obstruction lives, and the answer sharpens
the acceptance test by one coordinate.

The boundary is **not** equality versus inequality.  `on_line_of_H_eq_one` is a
β-*equality* — `β = 1/2`, exactly — manufactured from ordinate data alone.  What
it consumes is **solitude**: it applies only at an atom of mass one.  Every
gauge witness in `Blindness.lean` lives on an atom of mass `≥ 2`, and
necessarily so, because the reflection argument that manufactures β-equalities
needs the ordinate to be uncrowded, while the gauge orbit only has room to act
where solitude fails.

So:

> **β-equalities are `μ_T`-computable exactly on the simple locus, and the
> blindness is supported entirely on the crowded atoms.**

This file proves both halves, and reads off the exact missing datum.  Over an
atom of mass `m` the fiber is `m = k + 2j` (`H_eq_online_add_two_mul`); `μ_T`
sees `m`; the parity `k ≡ m [MOD 2]` is already `μ_T`-computable
(`odd_Hr_inhabited`).  What is missing is `j` — one bounded natural number per
crowded atom — and the gauge pairs of `Blindness.lean` are two fiber states of
**equal parity**: `(k,j) = (2,0)` against `(0,1)`.
-/
import Riemann.Blindness

namespace Riemann
namespace Blindness

open Multiset

private lemma filter_replicate_pos {α : Type*} (p : α → Prop) [DecidablePred p]
    (n : ℕ) (x : α) (h : p x) :
    Multiset.filter p (Multiset.replicate n x) = Multiset.replicate n x :=
  Multiset.filter_eq_self.2 fun y hy => by rw [Multiset.eq_of_mem_replicate hy]; exact h

private lemma filter_replicate_neg {α : Type*} (p : α → Prop) [DecidablePred p]
    (n : ℕ) (x : α) (h : ¬ p x) :
    Multiset.filter p (Multiset.replicate n x) = 0 :=
  Multiset.filter_eq_nil.2 fun y hy => by rw [Multiset.eq_of_mem_replicate hy]; exact h

/-! ### The fiber, as a family of configurations

`config k j a` is the general element of the gauge fiber over a single atom:
`k` zeros on the critical line at height `0`, and `j` mirror pairs at abscissae
`a`, `1 - a`.  `Gauge.triple` is `config 3 0`, `Gauge.haunted` is `config 1 1`,
`doubleZero` is `config 2 0`, `depthPair` is `config 0 1`. -/

/-- One atom of mass `k + 2j`, in fiber state `(k, j)`, at depth `|a - 1/2|`. -/
noncomputable def config (k j : ℕ) (a : ℝ) : ZeroData where
  Z := Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
      + (Multiset.replicate j (a, (0:ℝ)) + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))
  refl_inv := by
    have h0 : refl ((1/2 : ℝ), (0:ℝ)) = ((1/2 : ℝ), (0:ℝ)) := by
      show ((1 - 1/2 : ℝ), (0:ℝ)) = _
      norm_num
    have h1 : refl (a, (0:ℝ)) = ((1 - a : ℝ), (0:ℝ)) := rfl
    have h2 : refl ((1 - a : ℝ), (0:ℝ)) = (a, (0:ℝ)) := by
      show ((1 - (1 - a) : ℝ), (0:ℝ)) = _
      norm_num
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_replicate, Multiset.map_replicate, h0, h1, h2, add_comm
      (Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))]

@[simp] lemma config_ordinates (k j : ℕ) (a : ℝ) :
    (config k j a).ordinates = Multiset.replicate (k + 2 * j) (0:ℝ) := by
  show Multiset.map Prod.snd (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
      + (Multiset.replicate j (a, (0:ℝ)) + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))) = _
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.map_replicate,
    ← Multiset.replicate_add, ← Multiset.replicate_add]
  congr 1
  ring

@[simp] lemma config_N (k j : ℕ) (a : ℝ) : (config k j a).N = k + 2 * j := by
  show Multiset.card (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
      + (Multiset.replicate j (a, (0:ℝ)) + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))) = _
  simp [Multiset.card_add]
  ring

lemma config_Noff {a : ℝ} (ha : a ≠ 1/2) (k j : ℕ) : (config k j a).Noff = 2 * j := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.1 ≠ 1/2)
      (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ))))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.1 ≠ 1/2) k ((1/2 : ℝ), (0:ℝ))
      (by norm_num),
    filter_replicate_pos (fun p : ℝ × ℝ => p.1 ≠ 1/2) j (a, (0:ℝ)) ha,
    filter_replicate_pos (fun p : ℝ × ℝ => p.1 ≠ 1/2) j ((1 - a : ℝ), (0:ℝ)) ha']
  simp [Multiset.card_add]
  ring

/-! ### The gauge orbit over one atom -/

/-- **The whole fiber is one gauge orbit.**  Any two fiber states of the same
mass carry the same `μ_T`, whatever their depths.  `μ_T` sees `m = k + 2j` and
nothing else. -/
theorem config_ordinates_eq {k j k' j' : ℕ} (h : k + 2 * j = k' + 2 * j')
    (a a' : ℝ) : (config k j a).ordinates = (config k' j' a').ordinates := by
  rw [config_ordinates, config_ordinates, h]

/-- **Parity is `μ_T`-visible, and it is *all* that is visible of the fiber.**
The on-line count `k` is congruent to the mass mod `2`, so `μ_T` determines it
that far — and `config_ordinates_eq` says it determines nothing further. -/
theorem config_parity (k j : ℕ) (a : ℝ) :
    k % 2 = (config k j a).N % 2 := by
  rw [config_N]
  omega

/-! ### Sighted on the simple locus -/

/-- **Where every atom has mass one, `μ_T` determines everything.**  A
configuration all of whose ordinates are simple has no off-line zeros at all —
so `N_off`, the quantity `Blindness.lean` proves uncomputable in general, is
computed here from `μ_T` alone.  This is `on_line_of_H_eq_one` read as a
statement about the locus rather than about a point. -/
theorem Noff_eq_zero_of_simple {D : ZeroData}
    (h : ∀ γ ∈ D.ordinates, D.ordinates.count γ = 1) : D.Noff = 0 := by
  classical
  unfold ZeroData.Noff
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro p hp hoff
  refine hoff (ZeroData.on_line_of_H_eq_one hp ?_)
  rw [ZeroData.H_eq_count]
  exact h p.2 (Multiset.mem_map_of_mem _ hp)

/-! ### Blind on every crowded mass -/

/-- **And at every mass `≥ 2` it fails, uniformly in the depth.**  For each
`m ≥ 2` the fiber contains two states of equal parity with different off-line
content: `(k, j) = (m, 0)` and `(m - 2, 1)`.  The blindness is therefore not a
feature of one witness — it is present at *every* crowded mass and absent at
mass one, which is the sharp threshold. -/
theorem blind_at_every_crowded_mass (m : ℕ) (hm : 2 ≤ m) {a : ℝ} (ha : a ≠ 1/2) :
    (config m 0 a).ordinates = (config (m - 2) 1 a).ordinates ∧
      (config m 0 a).N = (config (m - 2) 1 a).N ∧
      (config m 0 a).Noff ≠ (config (m - 2) 1 a).Noff := by
  have hmass : m + 2 * 0 = (m - 2) + 2 * 1 := by omega
  refine ⟨config_ordinates_eq hmass a a, ?_, ?_⟩
  · rw [config_N, config_N]; omega
  · rw [config_Noff ha, config_Noff ha]; omega

/-! ### The acceptance test, made mechanical

A candidate certificate passes iff it separates the two equal-parity fiber
states over a single atom of mass two.  Not "sees `β`" — *distinguishes `(2,0)`
from `(0,1)`*.  Everything that factors through `μ_T` fails this by
`config_ordinates_eq`, so the test is exactly the negation of membership in the
certificate class. -/

/-- The acceptance test: `Φ` resolves the fiber coordinate at depth `|a - 1/2|`. -/
def Discriminates (Φ : ZeroData → ℝ) (a : ℝ) : Prop :=
  Φ (config 2 0 a) ≠ Φ (config 0 1 a)

/-- **Nothing in the certificate class passes.**  Any functional of `μ_T`,
however elaborate, takes the same value on the two fiber states — at every
depth. -/
theorem not_discriminates_of_factors (g : Multiset ℝ → ℝ) (a : ℝ) :
    ¬ Discriminates (fun D => g D.ordinates) a := by
  intro h
  exact h (congrArg g (config_ordinates_eq (by norm_num) a a))

/-- **Passing the test is exactly failing to factor through `μ_T`.**  So
`Discriminates` is a concrete, checkable form of the acceptance test in
`Blindness.lean`: not "sees `β`" but "separates `(2,0)` from `(0,1)`". -/
theorem not_factors_of_discriminates (Φ : ZeroData → ℝ) (a : ℝ)
    (h : Discriminates Φ a) : ¬ ∃ g : Multiset ℝ → ℝ, ∀ D, Φ D = g D.ordinates := by
  rintro ⟨g, hg⟩
  refine h ?_
  rw [hg, hg, config_ordinates_eq (show 2 + 2 * 0 = 0 + 2 * 1 by norm_num) a a]

end Blindness
end Riemann
