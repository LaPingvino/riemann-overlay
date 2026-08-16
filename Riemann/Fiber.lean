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


/-! ### The first functional to pass the acceptance test

`Discriminates` is a specification; a specification with no known passing
instance is a wish.  Here is one, and its proof is the strict
arithmetic–geometric mean inequality.

`landau x D := Σ_{ρ ∈ Z} x^β` is the Landau weight evaluated on a
configuration — a finite sum, no analytic content.  All `config` zeros sit at
ordinate `0`, so the oscillating factor `e^{iγ log x}` is a common unit and the
real part carries everything; that is why a real-valued functional suffices for
the test.

On the two fiber states of mass two:

* `landau x (config 2 0 a) = 2 * x^(1/2)`
* `landau x (config 0 1 a) = x^a + x^(1-a)`

and `x^a + x^(1-a) > 2 x^(1/2)` for every `x > 1` and `a ≠ 1/2` — strict AM–GM,
nothing more.  **The discrimination that no functional of `μ_T` can make is
performed by an inequality older than the Hypothesis**, at every `x`, with the
excess growing in `log x`.  E16's `cosh` is AM–GM's excess.

*Honesty clause, so the result stays its own size.*  This certifies that the
**functional** discriminates.  It does not certify that we can **evaluate** it on
`ζ`'s actual zeros to the needed precision — that is `W16`'s separability
problem, untouched.  What changes is that the acceptance test now has a
known-passing calibration input, and every later candidate is measured against
it. -/

/-- The Landau weight of a configuration: `Σ_ρ x^β`. -/
noncomputable def landau (x : ℝ) (D : ZeroData) : ℝ :=
  (D.Z.map fun p => x ^ p.1).sum

@[simp] lemma landau_config (x : ℝ) (k j : ℕ) (a : ℝ) :
    landau x (config k j a) = k * x ^ ((1:ℝ)/2) + j * (x ^ a + x ^ (1 - a)) := by
  show (Multiset.map (fun p : ℝ × ℝ => x ^ p.1)
      (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ))))).sum = _
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate,
    Multiset.sum_replicate]
  push_cast
  ring

/-- `x^a ≠ x^(1/2)` when `a ≠ 1/2` and `x > 1`: the exponent map is injective. -/
private lemma rpow_ne {x : ℝ} (hx : 1 < x) {a : ℝ} (ha : a ≠ 1/2) :
    x ^ a ≠ x ^ ((1:ℝ)/2) := by
  rcases lt_trichotomy a (1/2 : ℝ) with h | h | h
  · exact ne_of_lt ((Real.rpow_lt_rpow_left_iff hx).2 h)
  · exact absurd h ha
  · exact ne_of_gt ((Real.rpow_lt_rpow_left_iff hx).2 h)

/-- **The Landau weight passes the acceptance test**, at every `x > 1` and every
depth — by strict AM–GM. -/
theorem landau_discriminates {x : ℝ} (hx : 1 < x) {a : ℝ} (ha : a ≠ 1/2) :
    Discriminates (landau x) a := by
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  set s : ℝ := x ^ ((1:ℝ)/2) with hs
  set u : ℝ := x ^ a with hu
  have hspos : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hupos : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hvpos : 0 < x ^ (1 - a) := Real.rpow_pos_of_pos hx0 _
  have hss : s * s = x := by
    rw [hs, ← Real.rpow_add hx0]
    norm_num
  have huv : u * x ^ (1 - a) = x := by
    rw [hu, ← Real.rpow_add hx0]
    norm_num
  have hne : u ≠ s := rpow_ne hx ha
  show landau x (config 2 0 a) ≠ landau x (config 0 1 a)
  rw [landau_config, landau_config]
  push_cast
  intro hcon
  have hkey : x ^ (1 - a) = s * s / u := by
    field_simp
    rw [mul_comm, huv]
    nlinarith [hss]
  rw [hkey] at hcon
  have hsub : (u - s) * (u - s) = 0 := by
    field_simp at hcon
    nlinarith [hcon, hupos, hspos]
  have : u - s = 0 := by nlinarith [hsub]
  exact hne (by linarith)


/-! ### A second calibration family, at distinct ordinates

The first family lives at a single ordinate, so every zero shares the factor
`e^{iγ log x}` and a real-valued functional suffices.  That makes the test
*narrow*: it exercises only functionals that read the `β` multiset, and it
cannot tell whether a candidate depends on the configuration being **one atom**.

So the suite gains a second family with a **spectator**: the mass-two gauge pair
at height `0`, plus a simple on-line zero at a different height `γ`.  The two
members still share `μ_T` and still differ in off-line content, but now the
ordinate measure is genuinely spread and the candidate must survive a
configuration it does not exhaust.

A candidate must declare which family it discriminates on. -/

/-- `configAt γ k j a`: the fiber state `(k, j)` at height `γ` rather than `0`. -/
noncomputable def configAt (γ : ℝ) (k j : ℕ) (a : ℝ) : ZeroData where
  Z := Multiset.replicate k ((1/2 : ℝ), γ)
      + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ))
  refl_inv := by
    have h0 : refl ((1/2 : ℝ), γ) = ((1/2 : ℝ), γ) := by
      show ((1 - 1/2 : ℝ), γ) = _
      norm_num
    have h1 : refl (a, γ) = ((1 - a : ℝ), γ) := rfl
    have h2 : refl ((1 - a : ℝ), γ) = (a, γ) := by
      show ((1 - (1 - a) : ℝ), γ) = _
      norm_num
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_replicate, Multiset.map_replicate, h0, h1, h2, add_comm
      (Multiset.replicate j ((1 - a : ℝ), γ))]

lemma config_eq_configAt (k j : ℕ) (a : ℝ) : config k j a = configAt 0 k j a := rfl

/-- Superposition of two configurations. -/
noncomputable def superpose (D D' : ZeroData) : ZeroData where
  Z := D.Z + D'.Z
  refl_inv := by rw [Multiset.map_add, D.refl_inv, D'.refl_inv]

@[simp] lemma add_ordinates (D D' : ZeroData) :
    (superpose D D').ordinates = D.ordinates + D'.ordinates := by
  show Multiset.map Prod.snd (D.Z + D'.Z) = _
  rw [Multiset.map_add]; rfl

@[simp] lemma add_Noff (D D' : ZeroData) : (superpose D D').Noff = D.Noff + D'.Noff := by
  classical
  show Multiset.card (Multiset.filter (fun p => p.1 ≠ 1/2) (D.Z + D'.Z)) = _
  rw [Multiset.filter_add, Multiset.card_add]; rfl

@[simp] lemma landau_add (x : ℝ) (D D' : ZeroData) :
    landau x (superpose D D') = landau x D + landau x D' := by
  show (Multiset.map (fun p : ℝ × ℝ => x ^ p.1) (D.Z + D'.Z)).sum = _
  rw [Multiset.map_add, Multiset.sum_add]; rfl

@[simp] lemma configAt_ordinates (γ : ℝ) (k j : ℕ) (a : ℝ) :
    (configAt γ k j a).ordinates = Multiset.replicate (k + 2 * j) γ := by
  show Multiset.map Prod.snd (Multiset.replicate k ((1/2 : ℝ), γ)
      + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ))) = _
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.map_replicate,
    ← Multiset.replicate_add, ← Multiset.replicate_add]
  congr 1
  ring

@[simp] lemma configAt_N (γ : ℝ) (k j : ℕ) (a : ℝ) :
    (configAt γ k j a).N = k + 2 * j := by
  show Multiset.card (Multiset.replicate k ((1/2 : ℝ), γ)
      + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ))) = _
  simp [Multiset.card_add]
  ring

lemma configAt_Noff {a : ℝ} (ha : a ≠ 1/2) (γ : ℝ) (k j : ℕ) :
    (configAt γ k j a).Noff = 2 * j := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.1 ≠ 1/2)
      (Multiset.replicate k ((1/2 : ℝ), γ)
        + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ)))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.1 ≠ 1/2) k ((1/2 : ℝ), γ) (by norm_num),
    filter_replicate_pos (fun p : ℝ × ℝ => p.1 ≠ 1/2) j (a, γ) ha,
    filter_replicate_pos (fun p : ℝ × ℝ => p.1 ≠ 1/2) j ((1 - a : ℝ), γ) ha']
  simp [Multiset.card_add]
  ring

@[simp] lemma landau_configAt (x : ℝ) (γ : ℝ) (k j : ℕ) (a : ℝ) :
    landau x (configAt γ k j a) = k * x ^ ((1:ℝ)/2) + j * (x ^ a + x ^ (1 - a)) := by
  show (Multiset.map (fun p : ℝ × ℝ => x ^ p.1)
      (Multiset.replicate k ((1/2 : ℝ), γ)
        + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ)))).sum = _
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate,
    Multiset.sum_replicate]
  push_cast
  ring

/-- Family 2, member A: the crowded atom in state `(2,0)` at height `0`, plus a
simple on-line spectator at height `γ`. -/
noncomputable def spectatorA (γ a : ℝ) : ZeroData :=
  superpose (configAt 0 2 0 a) (configAt γ 1 0 a)

/-- Family 2, member B: the same, with the crowded atom in state `(0,1)`. -/
noncomputable def spectatorB (γ a : ℝ) : ZeroData :=
  superpose (configAt 0 0 1 a) (configAt γ 1 0 a)

/-- **Family 2 is a genuine gauge pair**, and its ordinate measure is spread
over two heights rather than concentrated on one. -/
theorem spectator_gauge_pair {a : ℝ} (ha : a ≠ 1/2) (γ : ℝ) :
    (spectatorA γ a).ordinates = (spectatorB γ a).ordinates ∧
      (spectatorA γ a).Noff ≠ (spectatorB γ a).Noff := by
  refine ⟨?_, ?_⟩
  · simp [spectatorA, spectatorB]
  · simp [spectatorA, spectatorB, configAt_Noff ha]

/-- The acceptance test on family 2. -/
def Discriminates₂ (Φ : ZeroData → ℝ) (γ a : ℝ) : Prop :=
  Φ (spectatorA γ a) ≠ Φ (spectatorB γ a)

/-- **Nothing factoring through `μ_T` passes family 2 either** — as it must be,
since family 2 is a gauge pair. -/
theorem not_discriminates₂_of_factors (g : Multiset ℝ → ℝ) {a : ℝ} (ha : a ≠ 1/2)
    (γ : ℝ) : ¬ Discriminates₂ (fun D => g D.ordinates) γ a := by
  intro h
  exact h (congrArg g (spectator_gauge_pair ha γ).1)

/-- **The Landau weight passes family 2 as well**, at every `x > 1`, every depth
and every spectator height: the spectator contributes the same `x^(1/2)` to
both members and cancels, leaving strict AM–GM. -/
theorem landau_discriminates₂ {x : ℝ} (hx : 1 < x) {a : ℝ} (ha : a ≠ 1/2)
    (γ : ℝ) : Discriminates₂ (landau x) γ a := by
  have hcore : landau x (config 2 0 a) ≠ landau x (config 0 1 a) :=
    landau_discriminates hx ha
  rw [landau_config, landau_config] at hcore
  simp only [Discriminates₂, spectatorA, spectatorB, landau_add, landau_configAt]
  push_cast at hcore ⊢
  intro hcon
  exact hcore (by linarith)


/-! ### A test-design rule, learned by building an invalid test

The obvious third family is the **swap**: the crowded state `(2,0)` at height
`0` with `(0,1)` at height `γ`, against the same two states exchanged.  It looks
like a sharper test — the ordinate measure is identical and the *phase*
structure differs — and the real-valued Landau weight does not discriminate it.

That is not a defect in the Landau weight.  The swap pair agrees on **every
target count**: same `μ_T`, same `N_off`, same `NscStd`.  It is a symmetry of
the configuration space (relabelling heights), not a gauge pair, and *every*
functional ought to agree on it.

So the rule the suite needs, stated before someone reads a failure on this
family as evidence:

> **A calibration input must be two configurations agreeing on `μ_T` and
> disagreeing on a target.** Same-`μ_T` pairs that also agree on the targets are
> symmetries, and discriminating them is not a virtue.

Whether the phase channel is *necessary* is therefore still open — this family
does not decide it, and no family built from a single height can. -/

/-- The swap pair agrees on off-line content, so it is a symmetry rather than a
gauge pair. -/
theorem swap_not_a_gauge_pair {a : ℝ} (ha : a ≠ 1/2) (γ : ℝ) :
    (superpose (configAt 0 2 0 a) (configAt γ 0 1 a)).Noff
      = (superpose (configAt 0 0 1 a) (configAt γ 2 0 a)).Noff := by
  simp [configAt_Noff ha]

/-- …and the real Landau weight agrees on it, as it should. -/
theorem landau_swap_invariant (x a γ : ℝ) :
    landau x (superpose (configAt 0 2 0 a) (configAt γ 0 1 a))
      = landau x (superpose (configAt 0 0 1 a) (configAt γ 2 0 a)) := by
  simp [landau_add, landau_configAt]
  ring


/-! ### The residue, from the other side

`Blindness.lean` proves **necessity**: `μ_T` alone does not determine `NscStd`.
`config_parity` shows `μ_T` fixes the fiber's parity and nothing more.  What was
never proved is **sufficiency** — that the fiber coordinate is the *whole*
residue, i.e. that `μ_T` together with it determines the targets exactly.

This section supplies the pointwise half.  Split each ordinate's mass into its
on-line and off-line parts:

* `onAt γ` — zeros at `γ` with `β = 1/2` (this is `k`);
* `offAt γ` — zeros at `γ` with `β ≠ 1/2` (this is `2j`).

`H = onAt + offAt` is the fiber decomposition, and the theorem below says
**`NscStd` reads `onAt` and nothing else**.  Since `onAt = H − offAt`, that makes
`NscStd` a functional of `(μ_T, offAt)` pointwise — exactly complementary to the
blindness result, which says `μ_T` alone will not do.

**Kill condition, stated before the section was written:** *if `NscStd` cannot
be expressed through the on-line counts alone — if some further feature of the
configuration enters — then the sufficiency direction fails and `j` is not the
whole residue.*  It did not fire. -/

/-- `onAt γ`: zeros at ordinate `γ` lying on the critical line — the `k` of the
fiber decomposition. -/
noncomputable def onAt (D : ZeroData) (γ : ℝ) : ℕ :=
  Multiset.card (D.Z.filter fun p => p.2 = γ ∧ p.1 = 1/2)

/-- `offAt γ`: zeros at ordinate `γ` off the critical line — the `2j`. -/
noncomputable def offAt (D : ZeroData) (γ : ℝ) : ℕ :=
  Multiset.card (D.Z.filter fun p => p.2 = γ ∧ p.1 ≠ 1/2)

/-- `H` of a single-ordinate configuration — `SESSION 157`. -/
@[simp] lemma configAt_H (γ γ' : ℝ) (k j : ℕ) (a : ℝ) :
    (configAt γ k j a).H γ' = if γ' = γ then k + 2 * j else 0 := by
  classical
  rw [(configAt γ k j a).H_eq_count γ', configAt_ordinates]
  simp [Multiset.count_replicate, eq_comm]

/-- `offAt` of a single-ordinate configuration — `SESSION 157`.  All the
off-line mass sits at `γ`, so this is `configAt_Noff` localised. -/
lemma configAt_offAt {a : ℝ} (ha : a ≠ 1/2) (γ : ℝ) (k j : ℕ) :
    offAt (configAt γ k j a) γ = 2 * j := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.2 = γ ∧ p.1 ≠ 1/2)
      (Multiset.replicate k ((1/2 : ℝ), γ)
        + (Multiset.replicate j (a, γ)
          + Multiset.replicate j ((1 - a : ℝ), γ)))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) k
      ((1/2 : ℝ), γ) (fun h => h.2 rfl),
    filter_replicate_pos (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) j
      (a, γ) ⟨rfl, ha⟩,
    filter_replicate_pos (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) j
      ((1 - a : ℝ), γ) ⟨rfl, ha'⟩]
  simp [Multiset.card_add]
  ring

/-- **The fiber decomposition, pointwise:** `H = onAt + offAt`. -/
theorem H_eq_onAt_add_offAt (D : ZeroData) (γ : ℝ) :
    D.H γ = onAt D γ + offAt D γ := by
  classical
  set S := D.Z.filter (fun p => p.2 = γ) with hS
  have h1 : onAt D γ = Multiset.card (S.filter fun p => p.1 = 1/2) := by
    rw [onAt, hS, Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun _ _ => and_comm
  have h2 : offAt D γ = Multiset.card (S.filter fun p => ¬ (p.1 = 1/2)) := by
    rw [offAt, hS, Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun _ _ => and_comm
  rw [ZeroData.H, ← hS, h1, h2, ← Multiset.card_add, Multiset.filter_add_not]

/-- On the critical line, a zero's multiplicity **is** the on-line count at its
ordinate: all on-line zeros sharing an ordinate are literally the same point. -/
theorem count_eq_onAt (D : ZeroData) {p : ℝ × ℝ} (hp : p.1 = 1/2) :
    D.Z.count p = onAt D p.2 := by
  classical
  rw [onAt, Multiset.count_eq_card_filter_eq]
  congr 1
  refine Multiset.filter_congr fun q _ => ?_
  constructor
  · intro hq; exact ⟨by rw [← hq], by rw [← hq]; exact hp⟩
  · rintro ⟨h2, h1⟩
    exact (Prod.ext (h1.trans hp.symm) h2).symm

/-- **`NscStd` reads the on-line counts and nothing else.**

Together with `H_eq_onAt_add_offAt` this makes `NscStd` a pointwise functional
of `(μ_T, offAt)` — the sufficiency direction complementing
`Blindness.no_muInvariant_theory_computes_NscStd`'s necessity: supply the fiber
coordinate and the target is determined; withhold it and no `μ_T`-invariant
theory can recover it.

⚠️ **Corrected here (SESSION 089):** this read "the fiber coordinate really is
the *whole residue*", which `offAt_not_minimal` refutes — `(μ_T, offAt)` is
sufficient, not minimal (`SURPRISES` S26). -/
theorem NscStd_eq_onAt_functional (D : ZeroData) :
    D.NscStd = Multiset.card (D.Z.filter fun p => p.1 = 1/2 ∧ onAt D p.2 = 1) := by
  classical
  rw [ZeroData.NscStd]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← count_eq_onAt D h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [count_eq_onAt D h1]; exact h2⟩

/-- And `Nsc` reads the *total* mass — which is why it is `μ_T`-visible and
`NscStd` is not.  The two rows of the ledger differ by exactly which part of the
fiber decomposition they consult. -/
theorem Nsc_reads_total (D : ZeroData) :
    D.Nsc = Multiset.card (D.Z.filter fun p => D.H p.2 = 1) := by
  classical
  rw [ZeroData.Nsc]
  congr 1
  refine Multiset.filter_congr fun p hp => ?_
  exact ⟨fun h => h.2, fun h => ⟨ZeroData.on_line_of_H_eq_one hp h, h⟩⟩


/-! #### From pointwise to global

The pointwise results say `NscStd` reads `onAt`.  To say the fiber coordinate is
the **whole** residue we need the packaged form: two configurations agreeing on
`μ_T` and on `offAt` have the same `NscStd`.

The route is the on-line ordinate multiset `onOrd`, whose multiplicity at `γ` is
exactly `onAt γ`.  A multiset over `ℝ` is determined by its counts, so `onOrd`
is determined by `onAt`, and `NscStd` is a functional of `onOrd`. -/

/-- The ordinates of the **on-line** zeros, with multiplicity. -/
noncomputable def onOrd (D : ZeroData) : Multiset ℝ :=
  (D.Z.filter fun p => p.1 = 1/2).map Prod.snd

lemma count_onOrd (D : ZeroData) (γ : ℝ) : (onOrd D).count γ = onAt D γ := by
  classical
  rw [onOrd, Multiset.count_map, onAt, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- **`NscStd` is a functional of the on-line ordinate multiset alone.** -/
theorem NscStd_eq_onOrd_functional (D : ZeroData) :
    D.NscStd = Multiset.card ((onOrd D).filter fun γ => (onOrd D).count γ = 1) := by
  classical
  have h1 : D.NscStd
      = Multiset.card ((D.Z.filter fun p => p.1 = 1/2).filter
          fun p => onAt D p.2 = 1) := by
    rw [NscStd_eq_onAt_functional, Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun _ _ => and_comm
  rw [h1, ← Multiset.card_map Prod.snd]
  congr 1
  rw [onOrd, Multiset.filter_map]
  refine congrArg _ (Multiset.filter_congr fun p _ => ?_)
  show onAt D p.2 = 1 ↔ Multiset.count p.2 (onOrd D) = 1
  rw [count_onOrd]

/-- `onAt` is determined by `μ_T` together with `offAt` — immediately, from the
fiber decomposition. -/
theorem onAt_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) (γ : ℝ) : onAt D γ = onAt D' γ := by
  have hH : D.H γ = D'.H γ := by
    rw [ZeroData.H_eq_count, ZeroData.H_eq_count, hord]
  have h1 := H_eq_onAt_add_offAt D γ
  have h2 := H_eq_onAt_add_offAt D' γ
  have h3 := hoff γ
  omega

/-- **`(μ_T, offAt)` is a sufficient statistic for the residue.**  Two
configurations agreeing on `μ_T` and on the off-line mass at every ordinate have
the same `NscStd`.

⚠️ **Corrected at this location (SESSION 089).**  This docstring read "the
residue is **exactly** the fiber coordinate … nothing beyond `(μ_T, offAt)` is
needed — which is what 'the whole residue' means".  The forward direction is
this theorem; the converse is **false**, and `offAt_not_minimal` below refutes
it — `(μ_T, offAt)` is sufficient but *not* minimal.  That retraction was
recorded as `SURPRISES` S26 and lives 150 lines further down, which left the
superlative standing here unqualified for twelve cycles.  A retraction belongs
above what it retracts.

What is true, in both directions: with
`Blindness.no_muInvariant_theory_computes_NscStd` this brackets `X` — **withhold
the fiber coordinate and no `μ_T`-invariant theory recovers the target; supply it
and the target is determined.**  Sufficiency, not minimality. -/
theorem onOrd_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) : onOrd D = onOrd D' := by
  classical
  refine Multiset.ext.2 fun γ => ?_
  rw [count_onOrd, count_onOrd]
  exact onAt_determined hord hoff γ

theorem NscStd_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) : D.NscStd = D'.NscStd := by
  rw [NscStd_eq_onOrd_functional, NscStd_eq_onOrd_functional,
    onOrd_determined hord hoff]

/-! #### The complete ledger

Every quantity the project counts is now shown to be a functional of
`(μ_T, offAt)`.  `N`, `N⊛` and `Nsc` need only `μ_T` (they were already known to
factor through it); `NscStd` and `N_off` need the fiber coordinate as well, and
nothing beyond it. -/

/-- The on-line and off-line zeros partition the configuration. -/
theorem card_onOrd_add_Noff (D : ZeroData) :
    Multiset.card (onOrd D) + D.Noff = D.N := by
  classical
  rw [onOrd, Multiset.card_map, ZeroData.Noff, ZeroData.N,
    ← Multiset.card_add, Multiset.filter_add_not]

theorem Noff_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) : D.Noff = D'.Noff := by
  have hN : D.N = D'.N := by
    rw [(ZeroData.N_Nstar_ordinate_functional D).1,
      (ZeroData.N_Nstar_ordinate_functional D').1, hord]
  have h1 := card_onOrd_add_Noff D
  have h2 := card_onOrd_add_Noff D'
  rw [onOrd_determined hord hoff] at h1
  omega

/-- **The complete `X` theorem.**  `(μ_T, offAt)` determines the entire ledger.

Read with `Blindness.no_muInvariant_theory_computes_NscStd`, this is the exact
statement of what the certificate class is missing: **the ordinate measure plus
one bounded natural number per crowded atom, and nothing else at all.** -/
theorem ledger_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) :
    D.N = D'.N ∧ D.Nstar = D'.Nstar ∧ D.Nsc = D'.Nsc ∧
      D.NscStd = D'.NscStd ∧ D.Noff = D'.Noff := by
  refine ⟨?_, ?_, ?_, NscStd_determined hord hoff, Noff_determined hord hoff⟩
  · rw [(ZeroData.N_Nstar_ordinate_functional D).1,
      (ZeroData.N_Nstar_ordinate_functional D').1, hord]
  · rw [(ZeroData.N_Nstar_ordinate_functional D).2,
      (ZeroData.N_Nstar_ordinate_functional D').2, hord]
  · rw [ZeroData.Nsc_eq_ordinate_functional, ZeroData.Nsc_eq_ordinate_functional,
      hord]


/-! #### Is `offAt` *minimal*?  No — and the Landau weight cannot see it

`ledger_determined` says `(μ_T, offAt)` **suffices**.  It does not say `offAt` is
the least information that suffices, and the swap family settles that: two
configurations with the *same ledger* but *different* `offAt`.  So `offAt` is an
**upper bound** on the residue, not a tight one.

The same pair answers the evaluation question negatively.  The real Landau
weight `Σ_ρ x^β` agrees on the swap pair at **every** `x`
(`landau_swap_invariant`), while their `offAt` differs — so no amount of
sampling the real Landau weight recovers `offAt`.  That is census `#1`'s
separability problem restated as a determination failure, and it is consistent
with `w16_price.py`: what the swap pair differs in is *which ordinate carries the
crowd*, i.e. exactly the information the phase `e^{iγ log x}` carries and the
real weight discards. -/

lemma offAt_superpose (D D' : ZeroData) (γ : ℝ) :
    offAt (superpose D D') γ = offAt D γ + offAt D' γ := by
  classical
  show Multiset.card (Multiset.filter _ (D.Z + D'.Z)) = _
  rw [Multiset.filter_add, Multiset.card_add]
  rfl

lemma offAt_configAt_self {a : ℝ} (ha : a ≠ 1/2) (γ : ℝ) (k j : ℕ) :
    offAt (configAt γ k j a) γ = 2 * j := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.2 = γ ∧ p.1 ≠ 1/2)
      (Multiset.replicate k ((1/2 : ℝ), γ)
        + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ)))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) k ((1/2 : ℝ), γ)
      (by simp),
    filter_replicate_pos (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) j (a, γ)
      ⟨rfl, ha⟩,
    filter_replicate_pos (fun p : ℝ × ℝ => p.2 = γ ∧ p.1 ≠ 1/2) j
      ((1 - a : ℝ), γ) ⟨rfl, ha'⟩]
  simp [Multiset.card_add]
  ring

lemma offAt_configAt_other {a : ℝ} {γ γ' : ℝ} (hne : γ' ≠ γ) (k j : ℕ) :
    offAt (configAt γ k j a) γ' = 0 := by
  classical
  show Multiset.card (Multiset.filter (fun p => p.2 = γ' ∧ p.1 ≠ 1/2)
      (Multiset.replicate k ((1/2 : ℝ), γ)
        + (Multiset.replicate j (a, γ) + Multiset.replicate j ((1 - a : ℝ), γ)))) = 0
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = γ' ∧ p.1 ≠ 1/2) k ((1/2 : ℝ), γ)
      (by simp [hne]),
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = γ' ∧ p.1 ≠ 1/2) j (a, γ)
      (by simp [Ne.symm hne]),
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = γ' ∧ p.1 ≠ 1/2) j
      ((1 - a : ℝ), γ) (by simp [Ne.symm hne])]
  simp

/-- **The Landau weight cannot recover `offAt`.**  The swap pair agrees on the
real Landau weight at *every* `x` and differs in `offAt` at the ordinate `0`.
So no amount of sampling `Σ_ρ x^β` determines the fiber coordinate: the
information that distinguishes them is *which ordinate carries the crowd*, which
the real weight discards along with the phase. -/
theorem landau_cannot_determine_offAt {a : ℝ} (ha : a ≠ 1/2) {γ : ℝ}
    (hγ : γ ≠ 0) :
    (∀ x : ℝ, landau x (superpose (configAt 0 2 0 a) (configAt γ 0 1 a))
        = landau x (superpose (configAt 0 0 1 a) (configAt γ 2 0 a))) ∧
      offAt (superpose (configAt 0 2 0 a) (configAt γ 0 1 a)) 0
        ≠ offAt (superpose (configAt 0 0 1 a) (configAt γ 2 0 a)) 0 := by
  refine ⟨fun x => landau_swap_invariant x a γ, ?_⟩
  rw [offAt_superpose, offAt_superpose, offAt_configAt_self ha,
    offAt_configAt_self ha,
    offAt_configAt_other (a := a) (Ne.symm hγ) 0 1,
    offAt_configAt_other (a := a) (Ne.symm hγ) 2 0]
  omega

/-- **`offAt` is sufficient but not minimal.**  The same pair has the *same*
ledger (`swap_not_a_gauge_pair` for `N_off`; the rest by symmetry of the
construction) and *different* `offAt`.  So `ledger_determined` gives an upper
bound on the residue, and this says the bound is not tight: some coarsening of
`offAt` would still suffice. -/
theorem offAt_not_minimal {a : ℝ} (ha : a ≠ 1/2) {γ : ℝ} (hγ : γ ≠ 0) :
    (superpose (configAt 0 2 0 a) (configAt γ 0 1 a)).Noff
        = (superpose (configAt 0 0 1 a) (configAt γ 2 0 a)).Noff ∧
      offAt (superpose (configAt 0 2 0 a) (configAt γ 0 1 a)) 0
        ≠ offAt (superpose (configAt 0 0 1 a) (configAt γ 2 0 a)) 0 :=
  ⟨swap_not_a_gauge_pair ha γ, (landau_cannot_determine_offAt ha hγ).2⟩


/-! #### Coarsening the residue: ordinate identity is irrelevant

`offAt_not_minimal` showed `(μ_T, offAt)` is more than the ledger needs, using
the swap pair.  What the swap pair actually exploits is that the *names* of the
ordinates carry no information: exchanging which height hosts which fiber state
changes `offAt` as a function and changes nothing the ledger reports.

Proved here in general: **the entire ledger is invariant under any injective
relabelling of ordinates.**  So the residue is at most the *profile* — the
multiset of `(mass, off-line mass)` pairs — and never the labelled function
`offAt`. -/

/-- Relabel the ordinates by an injective `σ`, leaving abscissae alone. -/
noncomputable def relabel (D : ZeroData) (σ : ℝ → ℝ) : ZeroData where
  Z := D.Z.map fun p => (p.1, σ p.2)
  refl_inv := by
    have hcomm : refl ∘ (fun p : ℝ × ℝ => (p.1, σ p.2))
        = (fun p : ℝ × ℝ => (p.1, σ p.2)) ∘ refl := by
      funext p; rfl
    rw [Multiset.map_map, hcomm, ← Multiset.map_map, D.refl_inv]

@[simp] lemma relabel_N (D : ZeroData) (σ : ℝ → ℝ) : (relabel D σ).N = D.N := by
  show Multiset.card (D.Z.map _) = _
  rw [Multiset.card_map]; rfl

lemma relabel_H (D : ZeroData) {σ : ℝ → ℝ} (hσ : Function.Injective σ) (γ : ℝ) :
    (relabel D σ).H (σ γ) = D.H γ := by
  classical
  show Multiset.card (Multiset.filter _ (D.Z.map fun p => (p.1, σ p.2))) = _
  rw [Multiset.filter_map, Multiset.card_map, ZeroData.H]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  exact ⟨fun h => hσ h, fun h => congrArg σ h⟩

lemma relabel_Noff (D : ZeroData) (σ : ℝ → ℝ) : (relabel D σ).Noff = D.Noff := by
  classical
  show Multiset.card (Multiset.filter _ (D.Z.map fun p => (p.1, σ p.2))) = _
  rw [Multiset.filter_map, Multiset.card_map, ZeroData.Noff]
  congr 1

lemma relabel_count (D : ZeroData) {σ : ℝ → ℝ} (hσ : Function.Injective σ)
    (p : ℝ × ℝ) : (relabel D σ).Z.count (p.1, σ p.2) = D.Z.count p := by
  classical
  show Multiset.count _ (D.Z.map fun q => (q.1, σ q.2)) = _
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  refine Multiset.filter_congr fun q _ => ?_
  constructor
  · intro h
    have h1 : q.1 = p.1 := (Prod.ext_iff.1 h).1.symm
    have h2 : q.2 = p.2 := hσ (Prod.ext_iff.1 h).2.symm
    exact (Prod.ext h1 h2).symm
  · intro h; rw [← h]

lemma relabel_Nstar (D : ZeroData) {σ : ℝ → ℝ} (hσ : Function.Injective σ) :
    (relabel D σ).Nstar = D.Nstar := by
  classical
  show (((D.Z.map fun p => (p.1, σ p.2))).map fun p => (relabel D σ).H p.2).sum = _
  rw [Multiset.map_map, ZeroData.Nstar]
  refine congrArg _ (Multiset.map_congr rfl fun p _ => ?_)
  exact relabel_H D hσ p.2

lemma relabel_Nsc (D : ZeroData) {σ : ℝ → ℝ} (hσ : Function.Injective σ) :
    (relabel D σ).Nsc = D.Nsc := by
  classical
  show Multiset.card (Multiset.filter _ (D.Z.map fun p => (p.1, σ p.2))) = _
  rw [Multiset.filter_map, Multiset.card_map, ZeroData.Nsc]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  show (p.1 = 1/2 ∧ (relabel D σ).H (σ p.2) = 1) ↔ (p.1 = 1/2 ∧ D.H p.2 = 1)
  rw [relabel_H D hσ]

lemma relabel_NscStd (D : ZeroData) {σ : ℝ → ℝ} (hσ : Function.Injective σ) :
    (relabel D σ).NscStd = D.NscStd := by
  classical
  show Multiset.card (Multiset.filter _ (D.Z.map fun p => (p.1, σ p.2))) = _
  rw [Multiset.filter_map, Multiset.card_map, ZeroData.NscStd]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  show (p.1 = 1/2 ∧ (relabel D σ).Z.count (p.1, σ p.2) = 1)
      ↔ (p.1 = 1/2 ∧ D.Z.count p = 1)
  rw [relabel_count D hσ]

/-- **The ledger does not know the ordinates' names.**  Every counted quantity
is invariant under an injective relabelling of ordinates.

So the residue `(μ_T, offAt)` of `ledger_determined` is strictly more than
needed: what matters is the *profile*, the multiset of `(mass, off-line mass)`
pairs, with the heights themselves discarded.  The swap pair of
`offAt_not_minimal` is one instance of this theorem — the relabelling that
exchanges two heights. -/
theorem ledger_relabel_invariant (D : ZeroData) {σ : ℝ → ℝ}
    (hσ : Function.Injective σ) :
    (relabel D σ).N = D.N ∧ (relabel D σ).Nstar = D.Nstar ∧
      (relabel D σ).Nsc = D.Nsc ∧ (relabel D σ).NscStd = D.NscStd ∧
      (relabel D σ).Noff = D.Noff :=
  ⟨relabel_N D σ, relabel_Nstar D hσ, relabel_Nsc D hσ, relabel_NscStd D hσ,
    relabel_Noff D σ⟩


/-! #### The profile

The *profile* is the multiset of `(mass, off-line mass)` pairs, one per distinct
ordinate, with the heights themselves discarded.  `ledger_relabel_invariant`
says the residue cannot depend on the heights; the profile is the natural
candidate for what is left.

**Kill condition, stated before the section was written:** *if the construction
needs a finiteness or decidable-support fact not available for an arbitrary
`ZeroData`, the question is not answerable at this generality and that is the
finding.*  **It did not fire** — `Z` is a `Multiset`, hence finite, so
`ordinates.toFinset` exists classically with no extra hypothesis. -/

/-- The ordinates of the **off-line** zeros, with multiplicity. -/
noncomputable def offOrd (D : ZeroData) : Multiset ℝ :=
  (D.Z.filter fun p => p.1 ≠ 1/2).map Prod.snd

lemma count_offOrd (D : ZeroData) (γ : ℝ) : (offOrd D).count γ = offAt D γ := by
  classical
  rw [offOrd, Multiset.count_map, offAt, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- The profile: one `(H γ, offAt γ)` pair per distinct ordinate. -/
noncomputable def profile (D : ZeroData) : Multiset (ℕ × ℕ) :=
  D.ordinates.toFinset.val.map fun γ => (D.H γ, offAt D γ)

/-- **`N` is read off the profile** as the total mass. -/
theorem N_from_profile (D : ZeroData) :
    D.N = ((profile D).map Prod.fst).sum := by
  classical
  have h1 : ((profile D).map Prod.fst).sum
      = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
    rw [profile, Multiset.map_map]
    rfl
  rw [h1]
  have h2 : ∀ γ ∈ D.ordinates.toFinset, D.H γ = D.ordinates.count γ :=
    fun γ _ => D.H_eq_count γ
  rw [Finset.sum_congr rfl h2, Multiset.toFinset_sum_count_eq,
    (ZeroData.N_Nstar_ordinate_functional D).1]

/-- **`N_off` is read off the profile** as the total off-line mass. -/
theorem Noff_from_profile (D : ZeroData) :
    D.Noff = ((profile D).map Prod.snd).sum := by
  classical
  have hsub : (offOrd D).toFinset ⊆ D.ordinates.toFinset := by
    intro γ hγ
    rw [Multiset.mem_toFinset] at hγ ⊢
    rw [offOrd, Multiset.mem_map] at hγ
    obtain ⟨p, hp, rfl⟩ := hγ
    exact Multiset.mem_map_of_mem _ (Multiset.mem_of_mem_filter hp)
  have hzero : ∀ γ ∈ D.ordinates.toFinset, γ ∉ (offOrd D).toFinset →
      offAt D γ = 0 := by
    intro γ _ hγ
    rw [← count_offOrd]
    simpa using hγ
  have h1 : ((profile D).map Prod.snd).sum
      = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [profile, Multiset.map_map]
    rfl
  rw [h1, ← Finset.sum_subset hsub hzero]
  have h2 : ∀ γ ∈ (offOrd D).toFinset, offAt D γ = (offOrd D).count γ :=
    fun γ _ => (count_offOrd D γ).symm
  rw [Finset.sum_congr rfl h2, Multiset.toFinset_sum_count_eq, offOrd,
    Multiset.card_map, ZeroData.Noff]


/-- **`N⊛` is read off the profile** as the sum of squared masses.

The regrouping is `Finset.sum_multiset_map_count`, which needs only
`DecidableEq` — no hypothesis beyond `ZeroData`'s own finiteness, so the kill
condition stated for this section did not fire. -/
theorem Nstar_from_profile (D : ZeroData) :
    D.Nstar = ((profile D).map fun q => q.1 * q.1).sum := by
  classical
  have h1 : ((profile D).map fun q => q.1 * q.1).sum
      = ∑ γ ∈ D.ordinates.toFinset, D.H γ * D.H γ := by
    rw [profile, Multiset.map_map]
    rfl
  have h2 : D.Nstar = (D.ordinates.map fun γ => D.H γ).sum := by
    rw [ZeroData.Nstar, ZeroData.ordinates, Multiset.map_map]
    rfl
  rw [h1, h2, Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← D.H_eq_count γ, smul_eq_mul]

/-- **`Nsc` is read off the profile** as the number of mass-one atoms. -/
theorem Nsc_from_profile (D : ZeroData) :
    (D.Nsc : ℤ) = ((profile D).map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum := by
  classical
  have h1 : ((profile D).map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum
      = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then (1 : ℤ) else 0) := by
    rw [profile, Multiset.map_map]
    rfl
  rw [ZeroData.Nsc_eq_ordinate_functional, h1, card_filter_eq_sum,
    Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [← D.H_eq_count γ]
  by_cases h : D.H γ = 1
  · rw [if_pos h, h, one_smul]
  · rw [if_neg h, smul_zero]

/-- **`NscStd` is read off the profile** as the number of atoms whose on-line
part is exactly one — and `onAt = H − offAt` is a function of the profile
entry, which is the point.

With `N_from_profile`, `Noff_from_profile` and `Nstar_from_profile`, **all five
ledger quantities are functionals of the profile**: the heights are discarded
entirely and only the `(mass, off-line mass)` pairs survive. -/
theorem NscStd_from_profile (D : ZeroData) :
    (D.NscStd : ℤ)
      = ((profile D).map fun q => if q.1 - q.2 = 1 then (1 : ℤ) else 0).sum := by
  classical
  have h1 : ((profile D).map fun q => if q.1 - q.2 = 1 then (1 : ℤ) else 0).sum
      = ∑ γ ∈ D.ordinates.toFinset,
          (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
    rw [profile, Multiset.map_map]
    rfl
  have honAt : ∀ γ, D.H γ - offAt D γ = onAt D γ := by
    intro γ; rw [H_eq_onAt_add_offAt]; omega
  have h2 : (D.NscStd : ℤ)
      = ∑ γ ∈ (onOrd D).toFinset, (if onAt D γ = 1 then (1 : ℤ) else 0) := by
    rw [NscStd_eq_onOrd_functional, card_filter_eq_sum,
      Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [count_onOrd]
    by_cases h : onAt D γ = 1
    · rw [if_pos h, h, one_smul]
    · rw [if_neg h, smul_zero]
  have hsub : (onOrd D).toFinset ⊆ D.ordinates.toFinset := by
    intro γ hγ
    rw [Multiset.mem_toFinset] at hγ ⊢
    rw [onOrd, Multiset.mem_map] at hγ
    obtain ⟨p, hp, rfl⟩ := hγ
    exact Multiset.mem_map_of_mem _ (Multiset.mem_of_mem_filter hp)
  have hzero : ∀ γ ∈ D.ordinates.toFinset, γ ∉ (onOrd D).toFinset →
      (if onAt D γ = 1 then (1 : ℤ) else 0) = 0 := by
    intro γ _ hγ
    have : onAt D γ = 0 := by rw [← count_onOrd]; simpa using hγ
    rw [if_neg (by omega)]
  rw [h1, h2, Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [honAt]


/-! #### The third moment is `μ_T`-visible — two axes, not one

`Optimal.prop1_LP_optimal` says improving Proposition 1 requires leaving the
two-moment world, and `ISSUES` #20 names the missing object as `Σ m³`.  W35
identifies that as the coincidence-diagonal of the 3-level correlation.

**Kill condition, stated before this section was written:** *if `Σ m³` turns out
not to be `μ_T`-visible, it sits on the blindness side and the registers'
framing stands.*  **It did not fire.**  `H γ` is `ordinates.count γ`, so any
moment of the mass distribution is a functional of `μ_T` alone.

That separates two things the registers have been carrying close together:

* **more moments of `μ_T`** — `Σ m³` and beyond.  Inside the certificate class's
  reach in principle; what is missing is a *theorem supplying them*, not an
  ability to see them.
* **the fiber coordinate** — `offAt`, and the profile's second component.  Not a
  functional of `μ_T` at any order (`Blindness.NscStd_not_ordinate_functional`),
  so no amount of higher-moment information reaches it.

Improving `prop1` therefore does **not** require breaking the blindness.  The
two open directions are independent, and only one of them is an impossibility. -/

/-- The third moment of the mass distribution: `Σ_γ H(γ)³`. -/
noncomputable def thirdMoment (D : ZeroData) : ℕ :=
  ∑ γ ∈ D.ordinates.toFinset, D.H γ * D.H γ * D.H γ

/-- **The third moment is a functional of `μ_T`.**  Contrast
`Blindness.NscStd_not_ordinate_functional`: higher moments are inside the
certificate class's reach, the fiber coordinate is not. -/
theorem thirdMoment_determined {D D' : ZeroData}
    (hord : D.ordinates = D'.ordinates) : thirdMoment D = thirdMoment D' := by
  classical
  rw [thirdMoment, thirdMoment, hord]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [D.H_eq_count, D'.H_eq_count, hord]

/-- …and so is every moment, by the same one-line argument. -/
theorem moment_determined {D D' : ZeroData} (k : ℕ)
    (hord : D.ordinates = D'.ordinates) :
    ∑ γ ∈ D.ordinates.toFinset, D.H γ ^ k
      = ∑ γ ∈ D'.ordinates.toFinset, D'.H γ ^ k := by
  classical
  rw [hord]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [D.H_eq_count, D'.H_eq_count, hord]


/-! #### Minimality, and why the question was ill-posed

**Kill condition, stated before this section was written:** *if the minimality
question is trivially answered — the ledger being a sufficient statistic for
itself — then it is ill-posed as asked and the finding is the reframing, not a
minimal object.*  **It fired.**

The ledger is five numbers.  Any five-number summary that happens to equal it is
trivially sufficient for it, so the "minimal sufficient statistic" is the ledger,
and asking for it teaches nothing.

The question with content is *what shape* the ledger has as a functional of the
atom distribution.  Reading off the five `_from_profile` theorems, every ledger
quantity is a sum over atoms of one of five basis functions of `(m, j)`, where
`m` is the mass and `2j` the off-line mass:

| ledger | basis function | `μ_T`-visible? |
|---|---|---|
| `N` | `m` | **yes** |
| `N⊛` | `m²` | **yes** |
| `Nsc` | `[m = 1]` | **yes** |
| `NscStd` | `[m − 2j = 1]` | **no** |
| `N_off` | `2j` | **no** |

So the certificate class's target is a **five-dimensional linear image** of the
atom distribution, and the split is `3 : 2`.  Three of the five basis
functionals depend on `m` alone and are therefore inside `μ_T`; two require `j`
and are provably outside it.

Every entry of that table is already proved.  The theorem below only assembles
them, because the assembled statement is the clearest thing this development
has to say and it was scattered across three files. -/

/-- **The visibility split, assembled.**  Three of the ledger's five components
are functionals of `μ_T`; two are not, and the two are exactly those whose basis
function reads the off-line mass. -/
theorem ledger_visibility_split :
    -- the visible three: equal ordinates suffice
    (∀ D D' : ZeroData, D.ordinates = D'.ordinates →
        D.N = D'.N ∧ D.Nstar = D'.Nstar ∧ D.Nsc = D'.Nsc) ∧
      -- the invisible two: no ordinate functional computes them
      (¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, D.NscStd = f D.ordinates) ∧
      (¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, D.Noff = f D.ordinates) := by
  refine ⟨fun D D' hord => ⟨?_, ?_, ?_⟩, NscStd_not_ordinate_functional, ?_⟩
  · rw [(ZeroData.N_Nstar_ordinate_functional D).1,
      (ZeroData.N_Nstar_ordinate_functional D').1, hord]
  · rw [(ZeroData.N_Nstar_ordinate_functional D).2,
      (ZeroData.N_Nstar_ordinate_functional D').2, hord]
  · rw [ZeroData.Nsc_eq_ordinate_functional, ZeroData.Nsc_eq_ordinate_functional,
      hord]
  · rintro ⟨f, hf⟩
    exact no_muInvariant_bundle_computes_Noff (fun _ => True) (fun _ _ _ => Iff.rfl)
      (a := 1/4) (by norm_num) (Or.inl trivial) ⟨f, fun D _ => hf D⟩


/-! #### The third moment cannot help — an exact obstruction

W35 proposed supplying `Σ m³` to beat `prop1`.  claude.ai's LP analysis showed
the certified value would be `(2 − C) + s·(3C − 2 − C₃)` for a free parameter
`s ≥ 0`, so the third moment helps **iff** `C₃ < 3C − 2`.

That condition is never satisfiable, and the reason is an identity:

    3·N⊛ − 2·N − Σm³  =  − Σ_atoms m(m−1)(m−2)

and `m(m−1)(m−2) ≥ 0` for every natural `m`, with equality exactly when
`m ≤ 2`.  So `Σm³ ≥ 3N⊛ − 2N` for **every** configuration, the improvement
term `3C − 2 − C₃` is `≤ 0` always, and the optimum sits at `s = 0` — which is
`prop1` unchanged.

**The third moment buys nothing for this route.**  Not "not yet"; the
obstruction is an inequality true of all configurations, so no supplier — RS,
Fujii, Tsang — can change it.

Note what the obstruction is made of.  `m(m−1)(m−2)` vanishes at `m ≤ 2` and is
**6** at `m = 3`: the same `6` as `six_mul_NscStd_le`.  The third moment carries
information about atoms of mass `≥ 3` and nothing else, and it carries it in the
direction that costs. -/

/-- `3h² ≤ h³ + 2h` for every natural `h` — the pointwise form of
`m(m−1)(m−2) ≥ 0`. -/
private lemma three_sq_le_cube_add_two (h : ℕ) : 3 * h * h ≤ h * h * h + 2 * h := by
  rcases Nat.lt_or_ge h 3 with hlt | hge
  · interval_cases h <;> norm_num
  · nlinarith [hge]

lemma N_eq_sum_H (D : ZeroData) :
    D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
  classical
  have h2 : ∀ γ ∈ D.ordinates.toFinset, D.H γ = D.ordinates.count γ :=
    fun γ _ => D.H_eq_count γ
  rw [Finset.sum_congr rfl h2, Multiset.toFinset_sum_count_eq,
    (ZeroData.N_Nstar_ordinate_functional D).1]

lemma Nstar_eq_sum_H_sq (D : ZeroData) :
    D.Nstar = ∑ γ ∈ D.ordinates.toFinset, D.H γ * D.H γ := by
  classical
  have h2 : D.Nstar = (D.ordinates.map fun γ => D.H γ).sum := by
    rw [ZeroData.Nstar, ZeroData.ordinates, Multiset.map_map]
    rfl
  rw [h2, Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← D.H_eq_count γ, smul_eq_mul]

/-- `2^(j+1) ≤ 3^j + 1`.  `SESSION 211`.  The step that makes the general
moment minorant work: it says the coefficient `2^(k−1) − 1` never outruns
`3^(k−2)`, which is the smallest `m^(k−2)` available once `m ≥ 3`. -/
private lemma two_pow_le_three_pow_add_one (j : ℕ) : 2 ^ (j + 1) ≤ 3 ^ j + 1 := by
  induction j with
  | zero => norm_num
  | succ n ih =>
      have h3 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
      have h4 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      omega

/-- **The moment minorant at every order.**  `SESSION 211`.

For `A + 1 = 2^(k−1)` and `k ≥ 2`,

    A·m² + m  ≤  m^k + A·m      for every natural `m`.

`A` is chosen so the inequality is an **equality at `m = 1` and `m = 2`** — at
`m = 2` because `2A + 2 = 2^k` exactly — and those are the two masses whose
constraints settle the two-moment program (`206`).  `k = 2` gives `A = 1` and an
identity; `k = 3` gives `A = 3`, which is `three_sq_le_cube_add_two`; `k = 4`
gives `A = 7`, which is `seven_sq_le_fourth_add_six`.

For `m ≥ 3` the work is `A ≤ 3^(k−2) ≤ m^(k−2)`. -/
theorem moment_minorant {k A : ℕ} (hk : 2 ≤ k) (hA : A + 1 = 2 ^ (k - 1))
    (m : ℕ) : A * (m * m) + m ≤ m ^ k + A * m := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hA' : A + 1 = 2 ^ (j + 1) := by simpa using hA
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · interval_cases m
    · simp
    · simp [pow_succ]
    · have h2 : (2 : ℕ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      omega
  · have hAle : A ≤ 3 ^ j := by
      have := two_pow_le_three_pow_add_one j
      omega
    have hpow : (3 : ℕ) ^ j ≤ m ^ j := Nat.pow_le_pow_left hge j
    have hsplit : m ^ (j + 2) = m ^ j * (m * m) := by ring
    have hkey : A * (m * m) ≤ m ^ (j + 2) := by
      rw [hsplit]
      exact Nat.mul_le_mul_right _ (le_trans hAle hpow)
    have hm : 1 ≤ A := by
      have h2 : (2:ℕ) ^ 1 ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [pow_one] at h2
      omega
    nlinarith [hkey, hm, hge]

/-- `7h² ≤ h⁴ + 6h` for every natural `h` — the pointwise form of
`h(h−1)(h−2)(h+3) ≥ 0`.  `SESSION 210`.  The companion of
`three_sq_le_cube_add_two`, and chosen the same way: the linear-in-`(h², h)`
minorant of `h⁴` that is **tight at `h = 1` and `h = 2`**. -/
private lemma seven_sq_le_fourth_add_six (h : ℕ) :
    7 * (h * h) ≤ h * h * h * h + 6 * h := by
  rcases Nat.lt_or_ge h 3 with hlt | hge
  · interval_cases h <;> norm_num
  · have h1 : 3 * (h * h) ≤ h * h * h := by nlinarith [hge]
    have h2 : 3 * (h * h * h) ≤ h * h * h * h := by nlinarith [hge]
    have h3 : 9 * (h * h) ≤ h * h * h * h := by
      calc 9 * (h * h) = 3 * (3 * (h * h)) := by ring
        _ ≤ 3 * (h * h * h) := by omega
        _ ≤ h * h * h * h := h2
    omega

/-- `Σm⁴`, the fourth moment of the multiplicity distribution.  `SESSION 210`. -/
noncomputable def fourthMoment (D : ZeroData) : ℕ :=
  ∑ γ ∈ D.ordinates.toFinset, D.H γ * D.H γ * D.H γ * D.H γ

/-- **`Σm⁴ ≥ 7N⊛ − 6N`, for every configuration.**  `SESSION 210`.  The
order-`4` analogue of `three_Nstar_le_thirdMoment_add_two_N`. -/
theorem seven_Nstar_le_fourthMoment_add_six_N (D : ZeroData) :
    7 * D.Nstar ≤ fourthMoment D + 6 * D.N := by
  classical
  rw [N_eq_sum_H, Nstar_eq_sum_H_sq, fourthMoment, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun γ _ => seven_sq_le_fourth_add_six (D.H γ)

/-- `Σm^k`, the `k`-th moment of the multiplicity distribution.  `SESSION 211`.
`thirdMoment` and `fourthMoment` are the `k = 3` and `k = 4` cases in content. -/
noncomputable def momentK (D : ZeroData) (k : ℕ) : ℕ :=
  ∑ γ ∈ D.ordinates.toFinset, D.H γ ^ k

/-- **The moment obstruction at every order.**  `SESSION 211`.

With `A + 1 = 2^(k−1)` and `k ≥ 2`,

    A·N⊛ + N  ≤  Σm^k + A·N

so `C_k ≥ A·C − (A−1)` for every configuration.  `k = 3` (`A = 3`) is
`three_Nstar_le_thirdMoment_add_two_N`; `k = 4` (`A = 7`) is
`seven_Nstar_le_fourthMoment_add_six_N`. -/
theorem moment_obstruction (D : ZeroData) {k A : ℕ} (hk : 2 ≤ k)
    (hA : A + 1 = 2 ^ (k - 1)) :
    A * D.Nstar + D.N ≤ momentK D k + A * D.N := by
  classical
  rw [N_eq_sum_H, Nstar_eq_sum_H_sq, momentK, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun γ _ => moment_minorant hk hA (D.H γ)

/-- **`Σm^k` on a pure on-line atom of mass `m`.**  `SESSION 211`. -/
lemma config_momentK_pure (m : ℕ) {k : ℕ} (hk : 1 ≤ k) (a : ℝ) :
    momentK (config m 0 a) k = m ^ k := by
  classical
  have hH : (config m 0 a).H (0:ℝ) = m := by
    rw [config_eq_configAt, configAt_H]; simp
  have hord : (config m 0 a).ordinates = Multiset.replicate m ((0:ℝ)) := by
    show ((config m 0 a).Z.map Prod.snd) = _
    have hZ : (config m 0 a).Z = Multiset.replicate m ((1/2 : ℝ), (0:ℝ)) := by
      show Multiset.replicate m ((1/2 : ℝ), (0:ℝ))
          + (Multiset.replicate 0 (a, (0:ℝ))
            + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))) = _
      simp
    rw [hZ, Multiset.map_replicate]
  rw [momentK, hord]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [Nat.zero_pow (show 0 < k by omega)]
  · rw [Multiset.toFinset_replicate, if_neg (by omega)]
    simp [hH]

/-- **`Σm⁴` on a pure on-line atom of mass `m`.**  `SESSION 210`. -/
lemma config_fourthMoment_pure (m : ℕ) (a : ℝ) :
    fourthMoment (config m 0 a) = m * m * m * m := by
  classical
  have hH : (config m 0 a).H (0:ℝ) = m := by
    rw [config_eq_configAt, configAt_H]; simp
  have hord : (config m 0 a).ordinates = Multiset.replicate m ((0:ℝ)) := by
    show ((config m 0 a).Z.map Prod.snd) = _
    have hZ : (config m 0 a).Z = Multiset.replicate m ((1/2 : ℝ), (0:ℝ)) := by
      show Multiset.replicate m ((1/2 : ℝ), (0:ℝ))
          + (Multiset.replicate 0 (a, (0:ℝ))
            + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))) = _
      simp
    rw [hZ, Multiset.map_replicate]
  rw [fourthMoment, hord]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [Multiset.toFinset_replicate, if_neg (by omega)]
    simp [hH]

/-- **`Σm³` on a pure on-line atom of mass `m`.**  `SESSION 208`.  One atom, so
one term. -/
lemma config_thirdMoment_pure (m : ℕ) (a : ℝ) :
    thirdMoment (config m 0 a) = m * m * m := by
  classical
  have hH : (config m 0 a).H (0:ℝ) = m := by
    rw [config_eq_configAt, configAt_H]; simp
  have hord : (config m 0 a).ordinates = Multiset.replicate m ((0:ℝ)) := by
    show ((config m 0 a).Z.map Prod.snd) = _
    have hZ : (config m 0 a).Z = Multiset.replicate m ((1/2 : ℝ), (0:ℝ)) := by
      show Multiset.replicate m ((1/2 : ℝ), (0:ℝ))
          + (Multiset.replicate 0 (a, (0:ℝ))
            + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))) = _
      simp
    rw [hZ, Multiset.map_replicate]
  rw [thirdMoment, hord]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [Multiset.toFinset_replicate, if_neg (by omega)]
    simp [hH]

/-- **`N_sc` as a sum over atoms**, in the same shape as `N_eq_sum_H` and
`Nstar_eq_sum_H_sq`.  `SESSION 205`.  `N_sc` counts the mass-one atoms — `a₁` in
`ISSUES` `#20`'s notation — and this is that reading, machine-checked.

Built on `Basic.card_filter_eq_sum`, which was already in the repo; `205`'s
first attempt rebuilt it privately and shadowed it, breaking two proofs
downstream. -/
lemma Nsc_eq_sum_mass_one (D : ZeroData) :
    (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then (1:ℤ) else 0) := by
  classical
  rw [ZeroData.Nsc_eq_ordinate_functional, card_filter_eq_sum,
    Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← D.H_eq_count γ]
  by_cases h : D.H γ = 1 <;> simp [h]

/-- **The exact obstruction: `Σm³ ≥ 3N⊛ − 2N`, for every configuration.**

Hence `C₃ ≥ 3C − 2` always, the three-moment LP's improvement term is never
positive, and the optimum stays at `prop1`'s `2 − C`.  No level-3 supplier can
move this route.

**`SESSION 209`: that last sentence is now a theorem.**
`Optimal.linearBound3_LP_value` is `IsGreatest` at `2 − C` for the three-moment
program evaluated at the extreme `C₃ = 3C − 2` this inequality permits; the
ceiling is `Optimal.linearBound3_no_gain` and `prop1` attains it with `c = 0`.
The substitution `A = a − 2c`, `B = b + 3c` sends the mass-`1` and mass-`2`
constraints onto the two-moment feasible set exactly, which is why the value is
unchanged. -/
theorem three_Nstar_le_thirdMoment_add_two_N (D : ZeroData) :
    3 * D.Nstar ≤ thirdMoment D + 2 * D.N := by
  classical
  rw [N_eq_sum_H, Nstar_eq_sum_H_sq, thirdMoment, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ _ => ?_
  have := three_sq_le_cube_add_two (D.H γ)
  linarith [this]


/-! #### The moment route is walled at every order

`three_Nstar_le_thirdMoment_add_two_N` killed the third moment.  claude.ai
observed the generalisation, and it is the stronger statement:

> the configuration that makes `prop1` tight has **every** descending factorial
> moment of order `≥ 3` equal to zero.

`prop1`'s two extremal witnesses are `single` (one atom of mass `1`) and
`Gauge.pairOnly` (one atom of mass `2`).  For `m ≤ 2` and `k ≥ 3` the descending
factorial `m(m−1)⋯(m−k+1)` vanishes — it has more factors than `m` has room
for.  So every factorial moment functional of order `≥ 3`, hence every
polynomial moment functional of order `≥ 3`, is **zero** on the extremal family.

**A moment inequality cannot exclude a configuration on which it is tight.**  So
no moment constraint of any order — third, fourth, or the whole infinite
sequence — removes the witnesses that force `prop1`'s optimum.  The moment route
to improving `prop1` is walled **at every order**, not merely at three.

What survives is *equality*-grade, not inequality-grade: recovering the mass
distribution itself would need asymptotic **identities** for the moments
(Fujii-with-main-terms), which is a different supply chain.  `F.md`'s F2 should
be read at that grade and no higher. -/

/-- The `k`-th descending factorial moment of the mass distribution. -/
noncomputable def factMoment (D : ZeroData) (k : ℕ) : ℕ :=
  ∑ γ ∈ D.ordinates.toFinset, Nat.descFactorial (D.H γ) k

/-- **Every factorial moment of order `≥ 3` vanishes when all atoms have mass
`≤ 2`** — i.e. on exactly the family that makes `prop1` tight. -/
theorem factMoment_eq_zero_of_masses_le_two (D : ZeroData) {k : ℕ} (hk : 3 ≤ k)
    (hm : ∀ γ, D.H γ ≤ 2) : factMoment D k = 0 := by
  classical
  refine Finset.sum_eq_zero fun γ _ => ?_
  exact Nat.descFactorial_eq_zero_iff_lt.2 (lt_of_le_of_lt (hm γ) (by omega))


/-! #### Anti-rigidity, certified without literature (E24)

E24 reads *"the zeros could not be otherwise"* as **rigidity** — that the axiom
set pins its satisfiers — and promotes Davenport–Heilbronn to the programme's
**anti-rigidity control**: functional equation plus counting admits an object
with off-line zeros, so those axioms do not pin anything.

**Kill condition, stated before this section was written:** *if anti-rigidity
genuinely requires D–H, the claim rests on `[RECALL]` literature and must be
graded accordingly rather than certified.*  **It did not fire.**  The content
that matters — *the axiom set leaves room* — needs only a witness, and
`Gauge.pairOnly` is one: a lawful `ZeroData`, reflection-symmetric, whose zeros
are entirely off the critical line.

**What D–H adds, and it is a different strength.**  `pairOnly` shows the
*combinatorial* axioms have room.  D–H shows that room is occupied by a genuine
analytic object with a Dirichlet series and a functional equation.  The first is
certified here; the second is `[RECALL]` and is the one that makes the control
interesting.  They should not be quoted as the same fact. -/

/-- **The `ZeroData` axioms are not rigid.**  They admit a configuration all of
whose zeros lie off the critical line — so functional-equation symmetry plus
counting cannot force anything about position.

This is the certified half of E24's anti-rigidity control.  Davenport–Heilbronn
is the *arithmetic* witness for the same fact and remains `[RECALL]`; this one
needs no literature. -/
theorem zeroData_not_rigid :
    ∃ D : ZeroData, 0 < D.N ∧ D.Noff = D.N ∧ D.Nsc = 0 :=
  ⟨Gauge.pairOnly, by rw [Gauge.pairOnly_N]; norm_num,
    by rw [Gauge.pairOnly_Noff, Gauge.pairOnly_N], Gauge.pairOnly_Nsc⟩

/-- And the same axioms admit a configuration with **no** off-line zeros, so
they do not force the opposite either: the axiom set is silent on position in
both directions, which is what "leaves room" means. -/
theorem zeroData_admits_both :
    (∃ D : ZeroData, 0 < D.N ∧ D.Noff = D.N) ∧
      (∃ D : ZeroData, 0 < D.N ∧ D.Noff = 0) := by
  refine ⟨⟨Gauge.pairOnly, by rw [Gauge.pairOnly_N]; norm_num, ?_⟩,
    ⟨config 1 0 (1/4), ?_, ?_⟩⟩
  · rw [Gauge.pairOnly_Noff, Gauge.pairOnly_N]
  · rw [config_N]; norm_num
  · rw [config_Noff (by norm_num : (1/4 : ℝ) ≠ 1/2)]


/-! #### How much is missing, exactly: the gauge orbit has `⌊m/2⌋ + 1` elements

`config_ordinates_eq` says the whole fiber over an atom of mass `m` shares one
`μ_T`.  The registers have described the missing datum as *"one bounded natural
number per crowded atom"* without ever saying **how** bounded.  It is exactly
this: the fiber states are `(k, j)` with `k + 2j = m`, so `j` ranges over
`0 … ⌊m/2⌋` and the orbit has `⌊m/2⌋ + 1` members.

**Kill condition, stated before the section was written:** *if two distinct
fiber states shared the same `N_off`, the orbit would be smaller than claimed
and the ambiguity count wrong.*  It did not fire — `N_off = 2j` separates them.

So the certificate class, at each atom of mass `m`, cannot distinguish
`⌊m/2⌋ + 1` configurations: **one alternative at `m = 2` and `m = 3`, two at
`m = 4` and `m = 5**, and so on.  That is the size of the shadow, per atom. -/

/-- The fiber states over mass `m`, indexed by `j`: all share one `μ_T`. -/
theorem fiber_states_share_ordinates (m j₁ j₂ : ℕ) (h₁ : 2 * j₁ ≤ m)
    (h₂ : 2 * j₂ ≤ m) (a : ℝ) :
    (config (m - 2 * j₁) j₁ a).ordinates = (config (m - 2 * j₂) j₂ a).ordinates :=
  config_ordinates_eq (by omega) a a

/-- …and `N_off` tells them apart, so the indexing by `j` is faithful.  The
orbit over mass `m` therefore has exactly `⌊m/2⌋ + 1` distinct members. -/
theorem fiber_states_distinguished {a : ℝ} (ha : a ≠ 1/2) (m j₁ j₂ : ℕ)
    (h₁ : 2 * j₁ ≤ m) (h₂ : 2 * j₂ ≤ m) (hne : j₁ ≠ j₂) :
    (config (m - 2 * j₁) j₁ a).Noff ≠ (config (m - 2 * j₂) j₂ a).Noff := by
  rw [config_Noff ha, config_Noff ha]
  omega

/-- **The size of the shadow.**  At an atom of mass `m` the class sees one
`μ_T` and cannot tell `⌊m/2⌋ + 1` configurations apart — the states are
faithfully indexed by `j ∈ {0, …, ⌊m/2⌋}`, all sharing ordinates, all separated
by `N_off`.

This is the quantitative form of *"one bounded natural number per crowded
atom"*: the bound is `⌊m/2⌋`. -/
theorem gauge_orbit_size {a : ℝ} (ha : a ≠ 1/2) (m : ℕ) :
    ∀ j₁ ∈ Finset.range (m / 2 + 1), ∀ j₂ ∈ Finset.range (m / 2 + 1),
      (config (m - 2 * j₁) j₁ a).ordinates = (config (m - 2 * j₂) j₂ a).ordinates
        ∧ (j₁ ≠ j₂ →
            (config (m - 2 * j₁) j₁ a).Noff ≠ (config (m - 2 * j₂) j₂ a).Noff) := by
  intro j₁ h₁ j₂ h₂
  rw [Finset.mem_range] at h₁ h₂
  have hb₁ : 2 * j₁ ≤ m := by omega
  have hb₂ : 2 * j₂ ≤ m := by omega
  exact ⟨fiber_states_share_ordinates m j₁ j₂ hb₁ hb₂ a,
    fun hne => fiber_states_distinguished ha m j₁ j₂ hb₁ hb₂ hne⟩



/-! ### Is the profile minimal?  No — and the question was ill-posed

The profile determines the ledger (`N_from_profile` … `NscStd_from_profile`).
Queue item: *is it minimal — is there a coarser sufficient statistic?*

**Kill condition, filed before construction:** *if the ledger separates every
pair of distinct profiles that can be realised, minimality stands unrefuted and
the question is reported open, not answered.*  **It fired.**

Two two-atom configurations of the same total mass exchange their off-line
mass between the atoms:

* `A` — mass `4` with `2` off-line at height `0`, mass `2` all on-line at `γ`
* `B` — mass `4` all on-line at `0`, mass `2` with `2` off-line at `γ`

Their profiles `{(4,2),(2,0)}` and `{(4,0),(2,2)}` are **distinct**, and all
five ledger quantities agree.  So `profile → ledger` is not injective, the
ledger is itself a strictly coarser sufficient statistic, and the profile is
**not** minimal.

The finding is really about the question.  *Any* target quantity is its own
minimal sufficient statistic, so "is `X` minimal for the ledger" is degenerate
unless the competing statistics are restricted — to `μ_T`-augmentations, or to
statistics that are local in the ordinate.  Re-posed at that grade below. -/

/-- Two atoms: mass `k₁ + 2j₁` at height `0`, mass `k₂ + 2j₂` at height `γ`. -/
noncomputable def twoAtom (γ a : ℝ) (k₁ j₁ k₂ j₂ : ℕ) : ZeroData :=
  superpose (configAt 0 k₁ j₁ a) (configAt γ k₂ j₂ a)

lemma twoAtom_ordinates (γ a : ℝ) (k₁ j₁ k₂ j₂ : ℕ) :
    (twoAtom γ a k₁ j₁ k₂ j₂).ordinates
      = Multiset.replicate (k₁ + 2 * j₁) (0:ℝ)
        + Multiset.replicate (k₂ + 2 * j₂) γ := by
  rw [twoAtom, add_ordinates, configAt_ordinates, configAt_ordinates]

lemma twoAtom_profile {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) {k₁ j₁ k₂ j₂ : ℕ}
    (h1 : k₁ + 2 * j₁ ≠ 0) (h2 : k₂ + 2 * j₂ ≠ 0) :
    profile (twoAtom γ a k₁ j₁ k₂ j₂)
      = {(k₁ + 2 * j₁, 2 * j₁), (k₂ + 2 * j₂, 2 * j₂)} := by
  classical
  have hord := twoAtom_ordinates γ a k₁ j₁ k₂ j₂
  have hfin : (twoAtom γ a k₁ j₁ k₂ j₂).ordinates.toFinset = {0, γ} := by
    have e1 : ¬(k₁ = 0 ∧ j₁ = 0) := fun h => h1 (by omega)
    have e2 : ¬(k₂ = 0 ∧ j₂ = 0) := fun h => h2 (by omega)
    rw [hord]
    simp [Multiset.toFinset_add, Multiset.toFinset_replicate, e1, e2]
  have hH0 : (twoAtom γ a k₁ j₁ k₂ j₂).H 0 = k₁ + 2 * j₁ := by
    rw [ZeroData.H_eq_count, hord]
    simp [Multiset.count_replicate, hγ, Ne.symm hγ]
  have hHg : (twoAtom γ a k₁ j₁ k₂ j₂).H γ = k₂ + 2 * j₂ := by
    rw [ZeroData.H_eq_count, hord]
    simp [Multiset.count_replicate, hγ, Ne.symm hγ]
  have hO0 : offAt (twoAtom γ a k₁ j₁ k₂ j₂) 0 = 2 * j₁ := by
    rw [twoAtom, offAt_superpose, offAt_configAt_self ha,
      offAt_configAt_other (a := a) (Ne.symm hγ) k₂ j₂]
    omega
  have hOg : offAt (twoAtom γ a k₁ j₁ k₂ j₂) γ = 2 * j₂ := by
    rw [twoAtom, offAt_superpose, offAt_configAt_self ha,
      offAt_configAt_other (a := a) hγ k₁ j₁]
    omega
  rw [profile, hfin]
  rw [show ({0, γ} : Finset ℝ).val = (0 : ℝ) ::ₘ {γ} from
    Finset.insert_val_of_notMem (by simpa using Ne.symm hγ)]
  simp [hH0, hHg, hO0, hOg]

/-- **The profile is not minimal.**  Two realisable configurations with
*distinct* profiles and *identical* ledgers: exchange the off-line mass between
a mass-`4` atom and a mass-`2` atom.  So `profile → ledger` is not injective,
and the ledger is itself a strictly coarser sufficient statistic.

The kill condition — *the ledger separates every realisable pair of distinct
profiles* — fired here. -/
theorem profile_not_minimal {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    profile (twoAtom γ a 2 1 2 0) ≠ profile (twoAtom γ a 4 0 0 1)
      ∧ (twoAtom γ a 2 1 2 0).N = (twoAtom γ a 4 0 0 1).N
      ∧ (twoAtom γ a 2 1 2 0).Nstar = (twoAtom γ a 4 0 0 1).Nstar
      ∧ (twoAtom γ a 2 1 2 0).Nsc = (twoAtom γ a 4 0 0 1).Nsc
      ∧ (twoAtom γ a 2 1 2 0).NscStd = (twoAtom γ a 4 0 0 1).NscStd
      ∧ (twoAtom γ a 2 1 2 0).Noff = (twoAtom γ a 4 0 0 1).Noff := by
  have pA := twoAtom_profile hγ ha (k₁ := 2) (j₁ := 1) (k₂ := 2) (j₂ := 0)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 4) (j₁ := 0) (k₂ := 0) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨by rw [pA, pB]; decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((twoAtom γ a 2 1 2 0).Nsc : ℤ) = ((twoAtom γ a 4 0 0 1).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((twoAtom γ a 2 1 2 0).NscStd : ℤ) = ((twoAtom γ a 4 0 0 1).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide

/-! ### Is the ledger itself irredundant? — `SESSION 216`

`075` showed the profile is not the minimal sufficient statistic: the ledger is
coarser and still determines itself.  `NIGHT.md` has carried "minimal residue
still unidentified" since night-`17`.  The sharp question one level down is
whether the ledger's own five entries are independent — whether any of them is
recoverable from the other four.

Two are not, by the same construction `profile_not_minimal` uses: read every
entry off the profile and `decide`. -/

/-- **`N_off` is not determined by the other four ledger entries.**
`SESSION 216`.

Two atoms of masses `4` and `2`, once entirely on the line and once entirely off
it.  `N = 6`, `N⊛ = 20`, `N_sc = 0`, `NscStd = 0` on both — no atom has mass one,
and no atom has on-line part one — while `N_off` is `0` against `6`. -/
theorem Noff_not_determined_by_ledger {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 4 0 2 0).N = (twoAtom γ a 0 2 0 1).N
      ∧ (twoAtom γ a 4 0 2 0).Nstar = (twoAtom γ a 0 2 0 1).Nstar
      ∧ (twoAtom γ a 4 0 2 0).Nsc = (twoAtom γ a 0 2 0 1).Nsc
      ∧ (twoAtom γ a 4 0 2 0).NscStd = (twoAtom γ a 0 2 0 1).NscStd
      ∧ (twoAtom γ a 4 0 2 0).Noff ≠ (twoAtom γ a 0 2 0 1).Noff := by
  have pA := twoAtom_profile hγ ha (k₁ := 4) (j₁ := 0) (k₂ := 2) (j₂ := 0)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 0) (j₁ := 2) (k₂ := 0) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((twoAtom γ a 4 0 2 0).Nsc : ℤ) = ((twoAtom γ a 0 2 0 1).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((twoAtom γ a 4 0 2 0).NscStd : ℤ)
        = ((twoAtom γ a 0 2 0 1).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide

/-- **`NscStd` is not determined by the other four ledger entries.**
`SESSION 216`.

Masses `5` and `3` with two off-line zeros, placed on the mass-`5` atom or on
the mass-`3` one.  `N = 8`, `N⊛ = 34`, `N_off = 2`, `N_sc = 0` on both; but the
on-line part is `3` and `3` in the first case and `5` and `1` in the second, so
`NscStd` is `0` against `1`. -/
theorem NscStd_not_determined_by_ledger {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 3 1 3 0).N = (twoAtom γ a 5 0 1 1).N
      ∧ (twoAtom γ a 3 1 3 0).Nstar = (twoAtom γ a 5 0 1 1).Nstar
      ∧ (twoAtom γ a 3 1 3 0).Nsc = (twoAtom γ a 5 0 1 1).Nsc
      ∧ (twoAtom γ a 3 1 3 0).Noff = (twoAtom γ a 5 0 1 1).Noff
      ∧ (twoAtom γ a 3 1 3 0).NscStd ≠ (twoAtom γ a 5 0 1 1).NscStd := by
  have pA := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 1) (k₂ := 3) (j₂ := 0)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 5) (j₁ := 0) (k₂ := 1) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((twoAtom γ a 3 1 3 0).Nsc : ℤ) = ((twoAtom γ a 5 0 1 1).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide
  · have : ((twoAtom γ a 3 1 3 0).NscStd : ℤ)
        ≠ ((twoAtom γ a 5 0 1 1).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this

/-- Three atoms, at ordinates `0`, `γ` and `δ`.  `SESSION 217`.  `216` recorded
that `N_sc` independence needs three: with two atoms `Σm` and `Σm²` already pin
the mass multiset, so a pair matching in `N` and `N⊛` matches in `N_sc` too. -/
noncomputable def threeAtom (γ δ a : ℝ) (k₁ j₁ k₂ j₂ k₃ j₃ : ℕ) : ZeroData :=
  superpose (twoAtom γ a k₁ j₁ k₂ j₂) (configAt δ k₃ j₃ a)

lemma threeAtom_ordinates (γ δ a : ℝ) (k₁ j₁ k₂ j₂ k₃ j₃ : ℕ) :
    (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃).ordinates
      = Multiset.replicate (k₁ + 2 * j₁) (0:ℝ)
        + Multiset.replicate (k₂ + 2 * j₂) γ
        + Multiset.replicate (k₃ + 2 * j₃) δ := by
  rw [threeAtom, add_ordinates, twoAtom_ordinates, configAt_ordinates]

lemma threeAtom_profile {γ δ a : ℝ} (hγ : γ ≠ 0) (hδ : δ ≠ 0) (hγδ : γ ≠ δ)
    (ha : a ≠ 1/2) {k₁ j₁ k₂ j₂ k₃ j₃ : ℕ}
    (h1 : k₁ + 2 * j₁ ≠ 0) (h2 : k₂ + 2 * j₂ ≠ 0) (h3 : k₃ + 2 * j₃ ≠ 0) :
    profile (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃)
      = {(k₁ + 2 * j₁, 2 * j₁), (k₂ + 2 * j₂, 2 * j₂), (k₃ + 2 * j₃, 2 * j₃)} := by
  classical
  have hord := threeAtom_ordinates γ δ a k₁ j₁ k₂ j₂ k₃ j₃
  have e1 : ¬(k₁ = 0 ∧ j₁ = 0) := fun h => h1 (by omega)
  have e2 : ¬(k₂ = 0 ∧ j₂ = 0) := fun h => h2 (by omega)
  have e3 : ¬(k₃ = 0 ∧ j₃ = 0) := fun h => h3 (by omega)
  have hfin : (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃).ordinates.toFinset = {0, γ, δ} := by
    rw [hord]
    simp [Multiset.toFinset_add, Multiset.toFinset_replicate, e1, e2, e3]
  have hH0 : (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃).H 0 = k₁ + 2 * j₁ := by
    rw [ZeroData.H_eq_count, hord]
    simp [Multiset.count_replicate, hγ, hδ, Ne.symm hγ, Ne.symm hδ]
  have hHg : (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃).H γ = k₂ + 2 * j₂ := by
    rw [ZeroData.H_eq_count, hord]
    simp [Multiset.count_replicate, hγ, hγδ, Ne.symm hγ, Ne.symm hγδ]
  have hHd : (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃).H δ = k₃ + 2 * j₃ := by
    rw [ZeroData.H_eq_count, hord]
    simp [Multiset.count_replicate, hδ, hγδ, Ne.symm hδ, Ne.symm hγδ]
  have hO0 : offAt (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃) 0 = 2 * j₁ := by
    rw [threeAtom, offAt_superpose,
      offAt_configAt_other (a := a) (Ne.symm hδ) k₃ j₃, twoAtom,
      offAt_superpose, offAt_configAt_self ha,
      offAt_configAt_other (a := a) (Ne.symm hγ) k₂ j₂]
    omega
  have hOg : offAt (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃) γ = 2 * j₂ := by
    rw [threeAtom, offAt_superpose,
      offAt_configAt_other (a := a) hγδ k₃ j₃, twoAtom,
      offAt_superpose, offAt_configAt_self ha,
      offAt_configAt_other (a := a) hγ k₁ j₁]
    omega
  have hOd : offAt (threeAtom γ δ a k₁ j₁ k₂ j₂ k₃ j₃) δ = 2 * j₃ := by
    rw [threeAtom, offAt_superpose, offAt_configAt_self ha, twoAtom,
      offAt_superpose, offAt_configAt_other (a := a) hδ k₁ j₁,
      offAt_configAt_other (a := a) (Ne.symm hγδ) k₂ j₂]
    omega
  rw [profile, hfin]
  rw [show ({0, γ, δ} : Finset ℝ).val = (0 : ℝ) ::ₘ γ ::ₘ {δ} by
    rw [Finset.insert_val_of_notMem (by simp [Ne.symm hγ, Ne.symm hδ]),
      Finset.insert_val_of_notMem (by simpa using hγδ)]
    rfl]
  simp [hH0, hHg, hHd, hO0, hOg, hOd]

/-- **`N_sc` is not determined by the other four ledger entries.**  `SESSION 217`.

Three atoms of masses `1, 1, 4` with the off-line mass all on the `4`, against
two atoms of mass `3` each carrying one off-line pair.  `N = 6`, `N⊛ = 18`,
`N_off = 4`, `NscStd = 2` on both — the on-line parts are `1, 1, 0` and `1, 1` —
while `N_sc` is `2` against `0`, because only the first has atoms of mass one. -/
theorem Nsc_not_determined_by_ledger {γ δ a : ℝ} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hγδ : γ ≠ δ) (ha : a ≠ 1/2) :
    (threeAtom γ δ a 1 0 1 0 0 2).N = (twoAtom γ a 1 1 1 1).N
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).Nstar = (twoAtom γ a 1 1 1 1).Nstar
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).NscStd = (twoAtom γ a 1 1 1 1).NscStd
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).Noff = (twoAtom γ a 1 1 1 1).Noff
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).Nsc ≠ (twoAtom γ a 1 1 1 1).Nsc := by
  have pA := threeAtom_profile hγ hδ hγδ ha (k₁ := 1) (j₁ := 0) (k₂ := 1)
    (j₂ := 0) (k₃ := 0) (j₃ := 2) (by norm_num) (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 1) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((threeAtom γ δ a 1 0 1 0 0 2).NscStd : ℤ)
        = ((twoAtom γ a 1 1 1 1).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide
  · have : ((threeAtom γ δ a 1 0 1 0 0 2).Nsc : ℤ)
        ≠ ((twoAtom γ a 1 1 1 1).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this

/-- **`N⊛` is not determined by the other four ledger entries.**  `SESSION 217`.

Masses `2, 4` against `3, 3`, all on the line.  `N = 6`, `N_sc = 0`,
`NscStd = 0`, `N_off = 0` both; `N⊛` is `20` against `18`. -/
theorem Nstar_not_determined_by_ledger {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 2 0 4 0).N = (twoAtom γ a 3 0 3 0).N
      ∧ (twoAtom γ a 2 0 4 0).Nsc = (twoAtom γ a 3 0 3 0).Nsc
      ∧ (twoAtom γ a 2 0 4 0).NscStd = (twoAtom γ a 3 0 3 0).NscStd
      ∧ (twoAtom γ a 2 0 4 0).Noff = (twoAtom γ a 3 0 3 0).Noff
      ∧ (twoAtom γ a 2 0 4 0).Nstar ≠ (twoAtom γ a 3 0 3 0).Nstar := by
  have pA := twoAtom_profile hγ ha (k₁ := 2) (j₁ := 0) (k₂ := 4) (j₂ := 0)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 3) (j₂ := 0)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · have : ((twoAtom γ a 2 0 4 0).Nsc : ℤ) = ((twoAtom γ a 3 0 3 0).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((twoAtom γ a 2 0 4 0).NscStd : ℤ)
        = ((twoAtom γ a 3 0 3 0).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide

/-- The profile of a single atom. -/
lemma configAt_profile {γ a : ℝ} (ha : a ≠ 1/2) {k j : ℕ} (h : k + 2 * j ≠ 0) :
    profile (configAt γ k j a) = {(k + 2 * j, 2 * j)} := by
  classical
  have hord := configAt_ordinates γ k j a
  have hfin : (configAt γ k j a).ordinates.toFinset = {γ} := by
    rw [hord, Multiset.toFinset_replicate, if_neg h]
  have hH : (configAt γ k j a).H γ = k + 2 * j := by
    rw [ZeroData.H_eq_count, hord]
    simp
  rw [profile, hfin]
  simp [hH, offAt_configAt_self ha]


/-- **`N` is not determined by the other four ledger entries.**  `SESSION 217`.

One atom of mass `5` against two atoms of masses `3` and `4`, all on the line.
`N⊛ = 25` both, `N_sc = 0`, `NscStd = 0`, `N_off = 0` both; `N` is `5` against
`7`. -/
theorem N_not_determined_by_ledger {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (configAt 0 5 0 a).Nstar = (twoAtom γ a 3 0 4 0).Nstar
      ∧ (configAt 0 5 0 a).Nsc = (twoAtom γ a 3 0 4 0).Nsc
      ∧ (configAt 0 5 0 a).NscStd = (twoAtom γ a 3 0 4 0).NscStd
      ∧ (configAt 0 5 0 a).Noff = (twoAtom γ a 3 0 4 0).Noff
      ∧ (configAt 0 5 0 a).N ≠ (twoAtom γ a 3 0 4 0).N := by
  have pA := configAt_profile (γ := (0:ℝ)) ha (k := 5) (j := 0) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 4) (j₂ := 0)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((configAt 0 5 0 a).Nsc : ℤ) = ((twoAtom γ a 3 0 4 0).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((configAt 0 5 0 a).NscStd : ℤ)
        = ((twoAtom γ a 3 0 4 0).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide
  · rw [N_from_profile, N_from_profile, pA, pB]; decide

/-- **The profile *is* minimal among ordinate-local statistics.**

`profile_not_minimal` shows the profile is not minimal outright — but that is
degenerate, since the ledger is trivially its own minimal sufficient statistic.
The non-degenerate question is whether the per-atom entry `(mass, off-line mass)`
can be *coarsened*: is there a non-injective `g` such that the multiset of
`g`-values still determines the ledger?

**No.**  Any such `g` must be injective on realisable atoms, because `N` and
`N_off` are the atom-wise sums of the two components: two atoms with the same
`g`-value but different mass are separated by `N`, and with the same mass but
different off-line mass by `N_off`.  Single-atom configurations suffice as
witnesses, so the argument needs nothing about crowded configurations at all.

The kill condition — *some non-injective coarsening still determines the ledger*
— did not fire. -/
theorem profile_minimal_among_local {S : Type*} {a : ℝ} (ha : a ≠ 1/2)
    (g : ℕ × ℕ → S)
    (hg : ∀ D D' : ZeroData, (profile D).map g = (profile D').map g →
            D.N = D'.N ∧ D.Noff = D'.Noff)
    {k₁ j₁ k₂ j₂ : ℕ} (h₁ : k₁ + 2 * j₁ ≠ 0) (h₂ : k₂ + 2 * j₂ ≠ 0)
    (hgeq : g (k₁ + 2 * j₁, 2 * j₁) = g (k₂ + 2 * j₂, 2 * j₂)) :
    (k₁ + 2 * j₁, 2 * j₁) = (k₂ + 2 * j₂, 2 * j₂) := by
  have hmap : (profile (configAt 0 k₁ j₁ a)).map g
      = (profile (configAt 0 k₂ j₂ a)).map g := by
    rw [configAt_profile ha h₁, configAt_profile ha h₂]
    simpa using hgeq
  obtain ⟨hN, hOff⟩ := hg _ _ hmap
  rw [configAt_N, configAt_N] at hN
  rw [configAt_Noff ha, configAt_Noff ha] at hOff
  rw [hN, hOff]

/-! #### …and *both* additive rows are load-bearing

`profile_minimal_among_local` forces injectivity from `N` and `N_off` together.
Neither alone will do, and the witnesses are single atoms of mass `2`.

**Kill condition, filed first:** *if either single row already forces
injectivity, the "two rows" reading is wrong and the hypothesis of
`profile_minimal_among_local` can be weakened.*  It did not fire. -/

/-- **Mass alone is not enough.**  The coarsening `(m, off) ↦ m` has a
value-multiset that determines `N` (and `N⊛`, and `Nsc`) yet misses `N_off`:
two atoms of mass `2`, one wholly on-line and one wholly off-line. -/
theorem mass_only_not_sufficient {a : ℝ} (ha : a ≠ 1/2) :
    (profile (configAt 0 2 0 a)).map Prod.fst
        = (profile (configAt 0 0 1 a)).map Prod.fst
      ∧ (configAt 0 2 0 a).Noff ≠ (configAt 0 0 1 a).Noff := by
  refine ⟨?_, ?_⟩
  · rw [configAt_profile ha (by norm_num), configAt_profile ha (by norm_num)]
    decide
  · rw [configAt_Noff ha, configAt_Noff ha]
    norm_num

/-- **Off-line mass alone is not enough either.**  The coarsening
`(m, off) ↦ off` misses `N`: two wholly on-line atoms of masses `2` and `4`. -/
theorem off_only_not_sufficient {a : ℝ} (ha : a ≠ 1/2) :
    (profile (configAt 0 2 0 a)).map Prod.snd
        = (profile (configAt 0 4 0 a)).map Prod.snd
      ∧ (configAt 0 2 0 a).N ≠ (configAt 0 4 0 a).N := by
  refine ⟨?_, ?_⟩
  · rw [configAt_profile ha (by norm_num), configAt_profile ha (by norm_num)]
    decide
  · rw [configAt_N, configAt_N]
    norm_num

/-! ### What the class *can* compute: the interval

`no_muInvariant_theory_computes_NscStd` says the certificate class cannot
compute `NscStd`.  That is a statement about a point.  Since even atoms
contribute `0` (`even_mass_NscStd_zero`) and odd atoms contribute at most `1`,
the class should be able to compute an **interval** containing it — and both
endpoints should be `μ_T` functionals.

**Kill condition, filed before the section was written:** *if `NscStd` can
exceed the odd-atom count, the interval reading is wrong and the section dies.*
It did not fire.

Together with `Basic.Nsc_le_NscStd` this brackets the invisible row:

> `Nsc ≤ NscStd ≤ #{odd atoms}`,  both endpoints visible to `μ_T`. -/

/-- **Off-line mass at an ordinate is even** — the functional equation pairs
`β` with `1 - β`, and `β ≠ 1/2` makes the pairing fixed-point-free. -/
lemma even_offAt (D : ZeroData) (γ : ℝ) : Even (offAt D γ) := by
  classical
  obtain ⟨j, hj⟩ := D.H_eq_online_add_two_mul γ
  have honline : Multiset.card ((D.Z.filter fun q => q.2 = γ).filter
      fun q => q.1 = 1 / 2) = onAt D γ := by
    rw [Multiset.filter_filter, onAt]
    congr 1
    exact Multiset.filter_congr fun p _ => and_comm
  rw [honline] at hj
  have hsplit := H_eq_onAt_add_offAt D γ
  exact ⟨j, by omega⟩

/-- The number of odd-mass atoms — a `μ_T` functional, since `H` is. -/
noncomputable def oddAtoms (D : ZeroData) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => ¬ Even (D.H γ)).card

/-- **`NscStd ≤ #{odd atoms}`, and the right-hand side is `μ_T`-visible.**
An atom contributes to `NscStd` only if its on-line part is `1`; with the
off-line part even, its mass is then odd.  So the invisible row is bracketed
above by a quantity the certificate class can read. -/
theorem NscStd_le_oddAtoms (D : ZeroData) : D.NscStd ≤ oddAtoms D := by
  classical
  have key : (D.NscStd : ℤ) ≤ (oddAtoms D : ℤ) := by
    rw [NscStd_from_profile]
    have h1 : ((profile D).map fun q => if q.1 - q.2 = 1 then (1 : ℤ) else 0).sum
        = ∑ γ ∈ D.ordinates.toFinset,
            (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [profile, Multiset.map_map]
      rfl
    have h2 : (oddAtoms D : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset,
            (if ¬ Even (D.H γ) then (1 : ℤ) else 0) := by
      rw [oddAtoms, Finset.card_filter]
      push_cast
      rfl
    rw [h1, h2]
    refine Finset.sum_le_sum fun γ _ => ?_
    by_cases h : D.H γ - offAt D γ = 1
    · rw [if_pos h, if_pos]
      intro hev
      obtain ⟨r, hr⟩ := even_offAt D γ
      obtain ⟨t, ht⟩ := hev
      have := H_eq_onAt_add_offAt D γ
      omega
    · rw [if_neg h]
      split <;> norm_num
  exact_mod_cast key

/-- **Both endpoints of the bracket are `μ_T` functionals.**  `Nsc` by
`Nsc_eq_ordinate_functional`; `oddAtoms` because `H` is the ordinate count.
This is what makes the bracket *computable by the class* rather than merely
true. -/
theorem bracket_muInvariant {D D' : ZeroData} (h : D.ordinates = D'.ordinates) :
    D.Nsc = D'.Nsc ∧ oddAtoms D = oddAtoms D' := by
  classical
  refine ⟨?_, ?_⟩
  · rw [ZeroData.Nsc_eq_ordinate_functional, ZeroData.Nsc_eq_ordinate_functional, h]
  · unfold oddAtoms
    simp only [ZeroData.H_eq_count, h]

/-- `oddAtoms` read off the profile, so it can be computed on explicit
configurations the same way the ledger rows are. -/
lemma oddAtoms_from_profile (D : ZeroData) :
    oddAtoms D = Multiset.card ((profile D).filter fun q => ¬ Even q.1) := by
  classical
  rw [oddAtoms, profile, Multiset.filter_map, Multiset.card_map, Finset.card,
    Finset.filter_val]
  rfl

/-- **The certificate class computes an interval, not a point.**  Both endpoints
are functionals of `μ_T` alone, and `no_muInvariant_theory_computes_NscStd` says
nothing inside the interval is determined. -/
theorem NscStd_bracketed (D : ZeroData) : D.Nsc ≤ D.NscStd ∧ D.NscStd ≤ oddAtoms D :=
  ⟨ZeroData.Nsc_le_NscStd D, NscStd_le_oddAtoms D⟩

/-! ### The arbitrary-arity builder

`bracket_tight_two_atoms` is tightness on one family.  The general statement
needs a configuration built from an arbitrary list of atoms, and a lemma reading
its profile.  Both are below.

**Kill condition, filed before construction:** *if the profile of the fold needs
a hypothesis beyond distinctness of the heights, the general statement is not
reachable this way and I say so rather than adding hypotheses until it works.* -/

lemma H_superpose (D D' : ZeroData) (γ : ℝ) :
    (superpose D D').H γ = D.H γ + D'.H γ := by
  classical
  rw [ZeroData.H_eq_count, ZeroData.H_eq_count, ZeroData.H_eq_count,
    add_ordinates, Multiset.count_add]

lemma H_eq_zero_of_not_mem {D : ZeroData} {γ : ℝ} (h : γ ∉ D.ordinates) :
    D.H γ = 0 := by
  classical
  rw [ZeroData.H_eq_count, Multiset.count_eq_zero]
  exact h

lemma offAt_eq_zero_of_not_mem {D : ZeroData} {γ : ℝ} (h : γ ∉ D.ordinates) :
    offAt D γ = 0 := by
  have h1 := H_eq_onAt_add_offAt D γ
  have h2 := H_eq_zero_of_not_mem h
  omega

/-- **Profiles add over superpositions with disjoint ordinate supports.**  The
disjointness hypothesis is the *only* one needed — the kill condition asked
whether anything further was required, and nothing is. -/
lemma profile_superpose_disjoint {D D' : ZeroData}
    (hdis : ∀ γ, γ ∈ D.ordinates → γ ∉ D'.ordinates) :
    profile (superpose D D') = profile D + profile D' := by
  classical
  have hfin : (superpose D D').ordinates.toFinset
      = D.ordinates.toFinset ∪ D'.ordinates.toFinset := by
    rw [add_ordinates, Multiset.toFinset_add]
  have hdisj : Disjoint D.ordinates.toFinset D'.ordinates.toFinset := by
    rw [Finset.disjoint_left]
    intro γ h1 h2
    rw [Multiset.mem_toFinset] at h1 h2
    exact hdis γ h1 h2
  rw [profile, hfin, ← Finset.disjUnion_eq_union _ _ hdisj, Finset.disjUnion_val,
    Multiset.map_add]
  congr 1
  · refine Multiset.map_congr rfl fun γ hγ => ?_
    have hmem : γ ∈ D.ordinates := by simpa using hγ
    have hout : γ ∉ D'.ordinates := hdis γ hmem
    rw [H_superpose, offAt_superpose, H_eq_zero_of_not_mem hout,
      offAt_eq_zero_of_not_mem hout]
    simp
  · refine Multiset.map_congr rfl fun γ hγ => ?_
    have hin : γ ∈ D'.ordinates := by simpa using hγ
    have hout : γ ∉ D.ordinates := fun hD => hdis γ hD hin
    rw [H_superpose, offAt_superpose, H_eq_zero_of_not_mem hout,
      offAt_eq_zero_of_not_mem hout]
    simp

/-- **The builder.**  A configuration from an arbitrary list of fiber states,
atom `i` placed at height equal to the length of the remaining tail — which
makes the heights `n-1, n-2, …, 0`, hence automatically distinct. -/
noncomputable def chain (a : ℝ) : List (ℕ × ℕ) → ZeroData
  | [] => ⟨0, by simp⟩
  | (p :: ps) => superpose (configAt (ps.length : ℝ) p.1 p.2 a) (chain a ps)

lemma chain_ordinates_lt (a : ℝ) (l : List (ℕ × ℕ)) :
    ∀ γ ∈ (chain a l).ordinates, γ < (l.length : ℝ) := by
  induction l with
  | nil => intro γ h; simp [chain, ZeroData.ordinates] at h
  | cons p ps ih =>
      intro γ h
      rw [chain, add_ordinates, Multiset.mem_add] at h
      rcases h with h | h
      · rw [configAt_ordinates] at h
        rw [Multiset.eq_of_mem_replicate h]
        simp only [List.length_cons]
        push_cast
        linarith
      · have := ih γ h
        simp only [List.length_cons]
        push_cast
        linarith

/-- **The builder's profile is exactly the list of its atoms.**  Every atom must
be nonempty; that is the only hypothesis, as the kill condition asked. -/
lemma chain_profile {a : ℝ} (ha : a ≠ 1/2) :
    ∀ l : List (ℕ × ℕ), (∀ p ∈ l, p.1 + 2 * p.2 ≠ 0) →
      profile (chain a l) = ((l.map fun p => (p.1 + 2 * p.2, 2 * p.2) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  intro l
  induction l with
  | nil => intro _; simp [chain, profile, ZeroData.ordinates]
  | cons p ps ih =>
      intro hne
      have hdis : ∀ γ, γ ∈ (configAt (ps.length : ℝ) p.1 p.2 a).ordinates →
          γ ∉ (chain a ps).ordinates := by
        intro γ hγ hmem
        rw [configAt_ordinates] at hγ
        have := chain_ordinates_lt a ps γ hmem
        rw [Multiset.eq_of_mem_replicate hγ] at this
        exact lt_irrefl _ this
      rw [chain, profile_superpose_disjoint hdis,
        configAt_profile ha (hne p (by simp)),
        ih fun q hq => hne q (by simp [hq])]
      simp

lemma chain_ordinates_congr {a : ℝ} : ∀ l₁ l₂ : List (ℕ × ℕ),
    (l₁.map fun p => p.1 + 2 * p.2) = (l₂.map fun p => p.1 + 2 * p.2) →
      (chain a l₁).ordinates = (chain a l₂).ordinates := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      rw [List.map_eq_nil_iff.1 h.symm]
  | cons p ps ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons q qs =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hlen : ps.length = qs.length := by
            have := congrArg List.length h.2
            simpa using this
          rw [chain, chain, add_ordinates, add_ordinates, configAt_ordinates,
            configAt_ordinates, h.1, hlen, ih qs h.2]

/-- **Tightness in general, on `n` atoms of mass 3.**  For every `t ≤ n` the
builder realises `NscStd = t` while `Nsc = 0` and `#{odd atoms} = n`, and the
`μ_T` does not depend on `t`.  So the whole interval `[Nsc, #{odd atoms}]` is
attained, at every width. -/
theorem bracket_tight_chain {a : ℝ} (ha : a ≠ 1/2) (n t : ℕ) (h : t ≤ n) :
    (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).ordinates
        = (chain a (List.replicate n ((3 : ℕ), (0 : ℕ)))).ordinates
      ∧ (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).NscStd = t
      ∧ (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).Nsc = 0
      ∧ oddAtoms (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))) = n := by
  classical
  set L := List.replicate t ((1 : ℕ), (1 : ℕ)) ++ List.replicate (n - t) ((3 : ℕ), (0 : ℕ)) with hL
  have hne : ∀ p ∈ L, p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [hL, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.eq_of_mem_replicate hp]; norm_num
    · rw [List.eq_of_mem_replicate hp]; norm_num
  have hp : profile (chain a L) = ((List.replicate t ((3 : ℕ), (2 : ℕ))
      ++ List.replicate (n - t) ((3 : ℕ), (0 : ℕ)) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
    rw [chain_profile ha L hne, hL]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine chain_ordinates_congr _ _ ?_
    rw [hL]
    simp [List.map_append, Nat.add_sub_cancel' h]
  · have : ((chain a L).NscStd : ℤ) = (t : ℤ) := by
      rw [NscStd_from_profile, hp]
      simp
    exact_mod_cast this
  · have : ((chain a L).Nsc : ℤ) = 0 := by
      rw [Nsc_from_profile, hp]
      simp
    exact_mod_cast this
  · rw [oddAtoms_from_profile, hp]
    have h3 : Odd 3 := by decide
    simp [List.filter_replicate, h3, Nat.add_sub_cancel' h]

/-! ### The bracket is tight — every value in it is attained

`NscStd_bracketed` gives `Nsc ≤ NscStd ≤ #{odd atoms}`.  A bracket is only a
resolution limit if the class really cannot do better, i.e. if **every** value
in it is realised at the same `μ_T`.

**Kill condition, filed before construction:** *if some value in the interval is
unattainable at fixed `μ_T`, the bracket is not tight and the resolution reading
overstates what the class is missing.*  It did not fire.

**Scope, stated rather than implied:** what follows is tightness on the
**two-atom family of mass 3**, where `Nsc = 0` and `#{odd atoms} = 2`, so the
interval is the whole of `[0, 2]` and all three values — both endpoints *and*
the interior point — are attained by configurations sharing one `μ_T`.
Tightness for an arbitrary `μ_T` is **not** proved; see the note after the
theorem for what the general statement would need. -/

/-- **All three values of the interval `[0, 2]` are attained at one `μ_T`.**
Two atoms of mass `3`, each independently either wholly on-line (`k = 3`,
contributing nothing) or carrying an off-line pair (`k = 1`, contributing one).
The `μ_T` is `{0, 0, 0, γ, γ, γ}` in every case. -/
theorem bracket_tight_two_atoms {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 3 0 3 0).ordinates = (twoAtom γ a 1 1 3 0).ordinates
      ∧ (twoAtom γ a 1 1 3 0).ordinates = (twoAtom γ a 1 1 1 1).ordinates
      ∧ (twoAtom γ a 3 0 3 0).Nsc = 0
      ∧ oddAtoms (twoAtom γ a 3 0 3 0) = 2
      ∧ (twoAtom γ a 3 0 3 0).NscStd = 0
      ∧ (twoAtom γ a 1 1 3 0).NscStd = 1
      ∧ (twoAtom γ a 1 1 1 1).NscStd = 2 := by
  have p0 := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 3) (j₂ := 0)
    (by norm_num) (by norm_num)
  have p1 := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 3) (j₂ := 0)
    (by norm_num) (by norm_num)
  have p2 := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 1) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at p0 p1 p2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twoAtom_ordinates, twoAtom_ordinates]
  · rw [twoAtom_ordinates, twoAtom_ordinates]
  · have : ((twoAtom γ a 3 0 3 0).Nsc : ℤ) = 0 := by
      rw [Nsc_from_profile, p0]; decide
    exact_mod_cast this
  · rw [oddAtoms_from_profile, p0]; decide
  · have : ((twoAtom γ a 3 0 3 0).NscStd : ℤ) = 0 := by
      rw [NscStd_from_profile, p0]; decide
    exact_mod_cast this
  · have : ((twoAtom γ a 1 1 3 0).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, p1]; decide
    exact_mod_cast this
  · have : ((twoAtom γ a 1 1 1 1).NscStd : ℤ) = 2 := by
      rw [NscStd_from_profile, p2]; decide
    exact_mod_cast this

/-! ### The *other* invisible row, bracketed the same way

`ledger_visibility_split` names two rows the class cannot read: `NscStd` and
`N_off`.  The first is now bracketed exactly.  This section does the second, and
the bound has the same shape — an inequality between `μ_T` functionals, tight at
every value the parity allows.

**Kill condition, filed before the section was written:** *if `N_off` can exceed
`N − #{odd atoms}`, the analogous bound is wrong and the symmetry between the
two invisible rows fails.*  It did not fire: an odd atom must keep at least one
zero on the line, and that one zero per odd atom is the entire gap. -/

/-- `N_off` is even — it is a sum of off-line masses, each even by
`even_offAt`. -/
theorem Noff_even (D : ZeroData) : Even D.Noff := by
  classical
  have hoff : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [Noff_from_profile, profile, Multiset.map_map]; rfl
  have hdvd : 2 ∣ D.Noff := by
    rw [hoff]
    refine Finset.dvd_sum fun γ _ => ?_
    obtain ⟨r, hr⟩ := even_offAt D γ
    exact ⟨r, by omega⟩
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by omega⟩

/-- **`N_off + #{odd atoms} ≤ N`.**  Every odd atom keeps at least one zero on
the critical line, so the off-line mass is short of the total by at least the
number of odd atoms — and both `N` and `#{odd atoms}` are `μ_T` functionals, so
this is a bound the certificate class can compute. -/
theorem Noff_add_oddAtoms_le_N (D : ZeroData) : D.Noff + oddAtoms D ≤ D.N := by
  classical
  have hoff : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [Noff_from_profile, profile, Multiset.map_map]; rfl
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
    rw [N_from_profile, profile, Multiset.map_map]; rfl
  have hodd : oddAtoms D
      = ∑ γ ∈ D.ordinates.toFinset, (if ¬ Even (D.H γ) then 1 else 0) := by
    rw [oddAtoms, Finset.card_filter]
  rw [hoff, hN, hodd, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ _ => ?_
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  by_cases h : Even (D.H γ)
  · rw [if_neg (by simpa using h)]
    omega
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 h
    omega

/-- **The `N_off` bound is attained, and every parity-admissible value with
it.**  On `n` atoms of mass `3`, the same family that made the `NscStd` bracket
tight gives `N_off = 2t` for every `t ≤ n` at a `t`-independent `μ_T` — so
`N_off` ranges over *all* even values from `0` to `2n`, and at `t = n` the
inequality `N_off + #{odd atoms} ≤ N` holds with equality (`2n + n = 3n`). -/
theorem Noff_tight_chain {a : ℝ} (ha : a ≠ 1/2) (n t : ℕ) (h : t ≤ n) :
    (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).Noff = 2 * t
      ∧ (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).N = 3 * n := by
  classical
  set L := List.replicate t ((1 : ℕ), (1 : ℕ)) ++ List.replicate (n - t) ((3 : ℕ), (0 : ℕ))
    with hL
  have hne : ∀ p ∈ L, p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [hL, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.eq_of_mem_replicate hp]; norm_num
    · rw [List.eq_of_mem_replicate hp]; norm_num
  have hp : profile (chain a L) = ((List.replicate t ((3 : ℕ), (2 : ℕ))
      ++ List.replicate (n - t) ((3 : ℕ), (0 : ℕ)) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
    rw [chain_profile ha L hne, hL]
    simp
  refine ⟨?_, ?_⟩
  · rw [Noff_from_profile, hp]
    simp [Nat.mul_comm]
  · rw [N_from_profile, hp]
    simp [Nat.add_sub_cancel' h, Nat.mul_comm]

/-! ### The two invisible rows are *coupled*

`NscStd` and `N_off` each have an exact bracket now.  A reader could take that
to mean the class's ignorance is two independent unknowns.  It is not: an atom
contributes to `NscStd` only when its on-line part is `1`, i.e. only at
*maximal* off-line mass, so pushing `NscStd` up drags `N_off` up with it.

The coupling is exactly the haunted count.  `NscStd − Nsc` counts atoms that are
standard-simple without being simple — mass `≥ 3`, on-line part `1` — and each
of those carries at least two off-line zeros.

**Kill condition, filed before the section was written:** *if a haunted atom can
exist with fewer than two off-line zeros, the coupling is looser than `2 : 1`
and the bound is wrong.*  It did not fire: on-line part `1` with mass `≠ 1`
forces off-line mass `≥ 1`, and `even_offAt` upgrades that to `≥ 2`. -/

/-- **Every haunted zero costs at least two off-line zeros:**
`2·(NscStd − Nsc) ≤ N_off`, stated additively to keep truncated subtraction out
of the content.  The two rows the certificate class cannot read are therefore
not independent unknowns — the class cannot be maximally wrong about both at
once. -/
theorem two_mul_NscStd_le_Noff_add_two_mul_Nsc (D : ZeroData) :
    2 * D.NscStd ≤ D.Noff + 2 * D.Nsc := by
  classical
  have key : (2 * D.NscStd : ℤ) ≤ (D.Noff : ℤ) + 2 * (D.Nsc : ℤ) := by
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hC0 : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
      rw [Noff_from_profile, profile, Multiset.map_map]; rfl
    have hC : (D.Noff : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (offAt D γ : ℤ) := by
      rw [hC0, Nat.cast_sum]
    rw [hA, hB, hC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    split_ifs <;> omega
  exact_mod_cast key

/-- **The `2 : 1` coupling is sharp**, and on the very family that made both
brackets tight: `n` atoms of mass `3` with `t` of them haunted give
`NscStd = t`, `Nsc = 0`, `N_off = 2t`, so the inequality is an equality at every
`t ≤ n`.  A mass-`3` haunted atom carries exactly two off-line zeros and cannot
carry fewer. -/
theorem coupling_tight {a : ℝ} (ha : a ≠ 1/2) (n t : ℕ) (h : t ≤ n) :
    2 * (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).NscStd
      = (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).Noff
        + 2 * (chain a (List.replicate t (1, 1) ++ List.replicate (n - t) (3, 0))).Nsc := by
  obtain ⟨-, hNscStd, hNsc, -⟩ := bracket_tight_chain ha n t h
  obtain ⟨hoff, -⟩ := Noff_tight_chain ha n t h
  rw [hNscStd, hNsc, hoff]
  omega

/-- **The coupling read as a supply route for the `Nsc` row.**  Any upper bound
`B` on the off-line count transfers directly to a lower bound on `Nsc` in terms
of the already-certified `NscStd`:

> `2·Nsc + B ≥ 2·NscStd`,  i.e.  `Nsc ≥ NscStd − B/2`.

Nothing beyond `two_mul_NscStd_le_Noff_add_two_mul_Nsc` is used — the kill
condition for this route asked whether any further hypothesis was needed, and
none is.  What the route *costs* is priced in `PRICES.md`; the theorem here is
only the conversion. -/
theorem Nsc_ge_of_Noff_le {D : ZeroData} {B : ℕ} (hB : D.Noff ≤ B) :
    2 * D.NscStd ≤ 2 * D.Nsc + B := by
  have := two_mul_NscStd_le_Noff_add_two_mul_Nsc D
  omega

/-- `N_off ≤ N` — trivially, the off-line zeros are a sub-multiset. -/
theorem Noff_le_N (D : ZeroData) : D.Noff ≤ D.N := by
  classical
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- **The unconditional form:** `2·NscStd ≤ 2·Nsc + N`, i.e.
`Nsc ≥ NscStd − N/2`, with no hypothesis at all.  Axiom-free. -/
theorem two_mul_NscStd_le_two_mul_Nsc_add_N (D : ZeroData) :
    2 * D.NscStd ≤ 2 * D.Nsc + D.N :=
  Nsc_ge_of_Noff_le (Noff_le_N D)

/-- **`3·NscStd ≤ N + 2·Nsc` — unconditional, axiom-free, no star bound.**

Sharper than the `2 :` form above, and by the same mechanism pushed one step: a
*haunted* atom (on-line part `1`, mass `≠ 1`) has off-line part even and
nonzero, hence **mass at least 3**.  So each haunted atom consumes three zeros
of `N` while contributing one to `NscStd`, and each simple atom consumes one
while contributing one to both counts.

This subsumes `two_mul_NscStd_le_two_mul_Nsc_add_N`. -/
theorem three_mul_NscStd_le_N_add_two_mul_Nsc (D : ZeroData) :
    3 * D.NscStd ≤ D.N + 2 * D.Nsc := by
  classical
  have key : (3 * D.NscStd : ℤ) ≤ (D.N : ℤ) + 2 * (D.Nsc : ℤ) := by
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    rw [hA, hB, hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    split_ifs <;> omega
  exact_mod_cast key

/-! ### The bridge's constants are optimal

`three_mul_NscStd_le_N_add_two_mul_Nsc` is `3·NscStd ≤ N + 2·Nsc`.  A future
cycle will want to improve it, so here is why it cannot be improved — two
single-atom witnesses settle both constants at once.

**Kill condition, filed before the section was written:** *if some configuration
permits `c > 3`, or `c = 3` with `d < 2`, the pair is not optimal and the claim
must be weakened.*  It did not fire. -/

/-- The one-atom witnesses: a haunted atom of mass `3`, and a simple atom. -/
lemma haunted_atom_counts {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 1 a).NscStd = 1 ∧ (configAt 0 1 1 a).Nsc = 0
      ∧ (configAt 0 1 1 a).N = 3 := by
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by norm_num)
  norm_num at hp
  refine ⟨?_, ?_, by simpa using configAt_N (0:ℝ) 1 1 a⟩
  · have : ((configAt 0 1 1 a).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, hp]; decide
    exact_mod_cast this
  · have : ((configAt 0 1 1 a).Nsc : ℤ) = 0 := by
      rw [Nsc_from_profile, hp]; decide
    exact_mod_cast this

lemma simple_atom_counts {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 0 a).NscStd = 1 ∧ (configAt 0 1 0 a).Nsc = 1
      ∧ (configAt 0 1 0 a).N = 1 := by
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 0) (by norm_num)
  norm_num at hp
  refine ⟨?_, ?_, by simpa using configAt_N (0:ℝ) 1 0 a⟩
  · have : ((configAt 0 1 0 a).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, hp]; decide
    exact_mod_cast this
  · have : ((configAt 0 1 0 a).Nsc : ℤ) = 1 := by
      rw [Nsc_from_profile, hp]; decide
    exact_mod_cast this

/-- **`(3, 2)` is the optimal constant pair.**  Any unconditional bridge
`c·NscStd ≤ N + d·Nsc` valid on all `ZeroData` has `c ≤ 3`, and if `c = 3` then
`d ≥ 2`.  The haunted atom forces the first, the simple atom the second — so the
`Nsc` row's `(3κ − 1)/2` cannot be improved by any inequality of this shape. -/
theorem bridge_optimal {c d : ℝ}
    (h : ∀ D : ZeroData, c * (D.NscStd : ℝ) ≤ (D.N : ℝ) + d * (D.Nsc : ℝ)) :
    c ≤ 3 ∧ (c = 3 → 2 ≤ d) := by
  obtain ⟨h1, h2, h3⟩ := haunted_atom_counts (a := (0:ℝ)) (by norm_num)
  obtain ⟨g1, g2, g3⟩ := simple_atom_counts (a := (0:ℝ)) (by norm_num)
  have hH := h (configAt 0 1 1 (0:ℝ))
  have hS := h (configAt 0 1 0 (0:ℝ))
  rw [h1, h2, h3] at hH
  rw [g1, g2, g3] at hS
  norm_num at hH hS
  exact ⟨hH, fun hc => by rw [hc] at hS; linarith⟩

/-! ### The four-quantity bridge, and why it does not move the row

`bridge_optimal` closes the shape `c·NscStd ≤ N + d·Nsc`.  Its scope is the
triple, and the proof of `(3,2)` throws away that a non-contributing **even**
atom has mass `≥ 2`.  Using that, plus the atom count `A` (visible: it is the
number of distinct ordinates) and `oddAtoms`, gives a strictly finer bound.

**Kill condition, filed first:** *if the four-quantity bound reduces to `(3,2)`
with no gain, it does not improve the row and I say so.*  **It fired.** -/

/-- The number of atoms — the count of distinct ordinates.  A `μ_T` functional. -/
noncomputable def atomCount (D : ZeroData) : ℕ := D.ordinates.toFinset.card

/-- **`distinctZeros`: the literature's `N_d`** — distinct zeros as *points* of
the plane, not distinct ordinates.  `SESSION 167`.

Wu, *Distinct zeros of the Riemann zeta-function* (arXiv:1206.3737), Theorem 1
proves `N_d(T) ≥ 0.66036·N(T)` unconditionally, with `N_d` defined there as
`|{ρ = β + iγ : 0 < γ ≤ T, ζ(ρ) = 0}|`.  That is this quantity, and it is **not**
`atomCount`. -/
noncomputable def distinctZeros (D : ZeroData) : ℕ := D.Z.toFinset.card

/-- **The dictionary, and it runs the wrong way for us: `atomCount ≤
distinctZeros`.**

Two zeros sharing an ordinate but sitting at different `β` are one *ordinate* and
two *distinct zeros*, so collapsing to ordinates can only lose count.  Hence a
**lower** bound on `N_d` — which is what the literature proves — does not
lower-bound `atomCount`, the quantity `hauntedDensity_of_distinctZeros` consumes.

Under RH the two coincide, every zero being on the line; unconditionally the gap
between them is exactly the off-line structure this project exists to measure.
So `166`'s want-ad is not filled by Wu's theorem even setting its constant aside,
and its constant `0.66036` is in any case below the `0.6725` the baseline already
supplies through `certified_atomCount`. -/
theorem atomCount_le_distinctZeros (D : ZeroData) :
    atomCount D ≤ distinctZeros D := by
  classical
  rw [atomCount, distinctZeros, ZeroData.ordinates, Multiset.toFinset_map]
  exact Finset.card_image_le

/-- **The reverse dictionary: `distinctZeros ≤ atomCount + Noff`** — `SESSION
168`.

`167` gave `atomCount ≤ distinctZeros` and stopped, which showed only that a
*lower* bound on the literature's `N_d` does not transfer downward.  `161`'s
lesson is that the other direction is where the arithmetic actually gets decided,
so here it is.

Split the distinct zeros by whether they sit on the line.  A distinct point with
`β = 1/2` is `(1/2, γ)` for a distinct ordinate `γ`, so those are counted by
`atomCount`; the rest are off-line and counted by `Noff`. -/
theorem distinctZeros_le_atomCount_add_Noff (D : ZeroData) :
    distinctZeros D ≤ atomCount D + D.Noff := by
  classical
  have hsub : D.Z.toFinset ⊆ (D.Z.toFinset.filter fun p => p.1 = 1/2)
      ∪ (D.Z.toFinset.filter fun p => ¬ (p.1 = 1/2)) := by
    intro p hp
    by_cases h : p.1 = 1/2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h⟩)
  have hsplit : distinctZeros D
      ≤ (D.Z.toFinset.filter fun p => p.1 = 1/2).card
        + (D.Z.toFinset.filter fun p => ¬ (p.1 = 1/2)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h1 : (D.Z.toFinset.filter fun p => p.1 = 1/2).card ≤ atomCount D := by
    rw [atomCount, ZeroData.ordinates, Multiset.toFinset_map]
    refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) ?_
    · exact Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter _ hp)
    · intro p hp q hq h
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      exact Prod.ext (hp'.trans hq'.symm) h
  have h2 : (D.Z.toFinset.filter fun p => ¬ (p.1 = 1/2)).card ≤ D.Noff := by
    have he : (D.Z.toFinset.filter fun p => ¬ (p.1 = 1/2))
        = (D.Z.filter fun p => ¬ (p.1 = 1/2)).toFinset :=
      (Multiset.toFinset_filter _ _).symm
    rw [he, ZeroData.Noff]
    exact Multiset.toFinset_card_le _
  omega

/-- **The four-quantity bridge:** `2·A + #{odd atoms} ≤ N + 2·Nsc`.  Per atom
this is `2 + [odd] ≤ mass + 2·[mass = 1]`, tight at masses `1`, `2` and `3`. -/
theorem two_mul_atomCount_add_oddAtoms_le (D : ZeroData) :
    2 * atomCount D + oddAtoms D ≤ D.N + 2 * D.Nsc := by
  classical
  have key : (2 * atomCount D + oddAtoms D : ℤ) ≤ (D.N : ℤ) + 2 * (D.Nsc : ℤ) := by
    have hO : (oddAtoms D : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if ¬ Even (D.H γ) then (1 : ℤ) else 0) := by
      rw [oddAtoms, Finset.card_filter]; push_cast; rfl
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    have e1 : (2 * atomCount D + oddAtoms D : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset,
            ((2 : ℤ) + if ¬ Even (D.H γ) then 1 else 0) := by
      rw [Finset.sum_add_distrib, ← hO, Finset.sum_const, atomCount]
      push_cast
      ring
    have e2 : ((D.N : ℤ) + 2 * (D.Nsc : ℤ))
        = ∑ γ ∈ D.ordinates.toFinset,
            ((D.H γ : ℤ) + 2 * if D.H γ = 1 then 1 else 0) := by
      rw [Finset.sum_add_distrib, ← hN, ← Finset.mul_sum, ← hB]
    rw [e1, e2]
    refine Finset.sum_le_sum fun γ hγ => ?_
    have hpos : 0 < D.H γ := by
      rw [ZeroData.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 hγ
    by_cases hev : Even (D.H γ)
    · obtain ⟨r, hr⟩ := hev
      rw [if_neg (by simpa using ⟨r, hr⟩)]
      split_ifs <;> omega
    · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 hev
      rw [if_pos hev]
      split_ifs <;> omega
  exact_mod_cast key

/-- **…and it collapses back to `(3, 2)`.**  Every atom is an ordinate and
every atom counted by `NscStd` is odd, so `A ≥ NscStd` and
`#{odd atoms} ≥ NscStd`; substituting recovers
`3·NscStd ≤ N + 2·Nsc` exactly.  The finer bound therefore buys nothing on the
literature's input, which supplies a proportion for `NscStd` and nothing for `A`
or `#{odd atoms}` — the kill condition fired. -/
theorem three_mul_NscStd_le_of_four (D : ZeroData) :
    3 * D.NscStd ≤ D.N + 2 * D.Nsc := by
  have h4 := two_mul_atomCount_add_oddAtoms_le D
  have hodd := NscStd_le_oddAtoms D
  have hA : D.NscStd ≤ atomCount D := le_trans hodd (by
    rw [atomCount, oddAtoms]
    exact Finset.card_filter_le _ _)
  omega

/-- `Nsc + N_off ≤ N` — the simple on-line zeros and the off-line zeros are
disjoint sub-multisets.  Axiom-free. -/
theorem Nsc_add_Noff_le_N (D : ZeroData) : D.Nsc + D.Noff ≤ D.N := by
  classical
  have h1 : D.Nsc ≤ Multiset.card (D.Z.filter fun p => p.1 = 1/2) := by
    refine Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)
    intro p hp
    exact hp.1
  have h2 : Multiset.card (D.Z.filter fun p => p.1 = 1/2)
      + Multiset.card (D.Z.filter fun p => ¬ (p.1 = 1/2)) = D.N := by
    rw [← Multiset.card_add, Multiset.filter_add_not]; rfl
  have h3 : D.Noff = Multiset.card (D.Z.filter fun p => ¬ (p.1 = 1/2)) := rfl
  omega

/-- **`N_off + NscStd ≤ N`** — the standard-simple zeros lie *on* the critical
line and the off-line zeros do not, so the two are disjoint sub-multisets.
Sharper than `Nsc_add_Noff_le_N`, since `Nsc ≤ NscStd`. -/
theorem Noff_add_NscStd_le_N (D : ZeroData) : D.Noff + D.NscStd ≤ D.N := by
  classical
  have h1 : D.NscStd ≤ Multiset.card (D.Z.filter fun p => p.1 = 1/2) := by
    refine Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)
    intro p hp
    exact hp.1
  have h2 : Multiset.card (D.Z.filter fun p => p.1 = 1/2)
      + Multiset.card (D.Z.filter fun p => ¬ (p.1 = 1/2)) = D.N := by
    rw [← Multiset.card_add, Multiset.filter_add_not]; rfl
  have h3 : D.Noff = Multiset.card (D.Z.filter fun p => ¬ (p.1 = 1/2)) := rfl
  omega

/-- **`NscStd ≤ atomCount`** — distinct standard-simple zeros sit at distinct
ordinates, since a standard-simple zero *is* `(1/2, γ)` and has multiplicity
one.  So the literature's row is also a lower bound on the number of **distinct
ordinates**, hence an upper bound on the mean vertical multiplicity. -/
theorem NscStd_le_atomCount (D : ZeroData) : D.NscStd ≤ atomCount D :=
  le_trans (NscStd_le_oddAtoms D) (by
    rw [atomCount, oddAtoms]
    exact Finset.card_filter_le _ _)

/-! ### The wall generalises: *no* low-multiplicity proportion bounds `N⊛`

`no_starBound_from_proportionStd` kills the case `k = 1` — a proportion of
*simple* zeros. The natural repair is to ask for a proportion of zeros at
ordinates of multiplicity `≤ k`, for some larger `k`. It fails for every `k`,
and the same witness family does it.

**Kill condition, filed first:** *if some `k` makes the low-multiplicity
proportion sufficient to bound `N⊛`, then the `k = 1` negative was special and
the wall is not general.* **It fired: no `k` works.** -/

/-- Zeros sitting at ordinates of multiplicity at most `k`. -/
noncomputable def lowMult (D : ZeroData) (k : ℕ) : ℕ :=
  Multiset.card (D.Z.filter fun p => D.H p.2 ≤ k)

/-- **The whole family of low-multiplicity proportions is insufficient.**  For
every threshold `k ≥ 1` and every `B`, a configuration with three quarters of its
zeros at simple ordinates — so `lowMult k` is `3/4` of `N` for *every* `k` — and
`N⊛ > B·N`.

The obstruction is not the choice of threshold.  It is that a proportion counts
zeros in the *good* part and says nothing about how the remainder is arranged,
while `N⊛` is dominated by exactly that remainder. -/
theorem no_starBound_from_lowMult {a : ℝ} (ha : a ≠ 1/2) (k B : ℕ) (hk : 1 ≤ k) :
    ∃ D : ZeroData, 4 * lowMult D k = 3 * D.N ∧ B * D.N < D.Nstar := by
  classical
  set m := 4 * B + k + 4 with hm
  set L : List (ℕ × ℕ) := List.replicate (3 * m) (1, 0) ++ [(m, 0)] with hL
  have hne : ∀ p ∈ L, p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [hL, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.eq_of_mem_replicate hp]; norm_num
    · simp only [List.mem_singleton] at hp
      rw [hp]; omega
  have hp := chain_profile ha L hne
  rw [hL] at hp
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil] at hp
  have hN : (chain a L).N = 4 * m := by
    rw [N_from_profile, hp]; simp; try ring
  have hS : (chain a L).Nstar = 3 * m + m * m := by
    rw [Nstar_from_profile, hp]; simp; try ring
  have hLow : ((lowMult (chain a L) k : ℕ) : ℤ) = ((3 * m : ℕ) : ℤ) := by
    have e : Multiset.card ((chain a L).ordinates.filter fun γ => (chain a L).H γ ≤ k)
        = lowMult (chain a L) k := by
      rw [ZeroData.ordinates, Multiset.filter_map, Multiset.card_map, lowMult]
      rfl
    rw [← e, card_filter_eq_sum, Finset.sum_multiset_map_count]
    have hmk : ¬ (m ≤ k) := by omega
    have hstep : ∀ γ ∈ (chain a L).ordinates.toFinset,
        (chain a L).ordinates.count γ •
            (if (chain a L).H γ ≤ k then (1 : ℤ) else 0)
          = (if (chain a L).H γ ≤ k then ((chain a L).H γ : ℤ) else 0) := by
      intro γ _
      rw [← ZeroData.H_eq_count]
      by_cases h : (chain a L).H γ ≤ k
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]; simp
    rw [Finset.sum_congr rfl hstep]
    have hprof : ∑ γ ∈ (chain a L).ordinates.toFinset,
        (if (chain a L).H γ ≤ k then ((chain a L).H γ : ℤ) else 0)
          = ((profile (chain a L)).map
              fun q => if q.1 ≤ k then (q.1 : ℤ) else 0).sum := by
      rw [profile, Multiset.map_map]
      rfl
    rw [hprof, hp]
    simp [hmk]
    omega
  have hLow' : lowMult (chain a L) k = 3 * m := by exact_mod_cast hLow
  refine ⟨chain a L, by rw [hLow', hN]; ring, ?_⟩
  rw [hN, hS]
  nlinarith [Nat.zero_le B, hm]

/-! ### The class impossibility, proved rather than asserted

`093` closed the low-multiplicity thresholds and then *asserted* the general
form: no statistic of the shape "at least `α` of the zeros are nice" can reach
`(★)`, whatever "nice" means, provided simple zeros qualify.  Asserting a
generalisation from a witness is exactly what `S30` cost, so it is proved here.

**Kill condition, filed first:** *if the general statement needs a hypothesis
beyond "simple atoms count as good", the generalisation is wrong and gets
downgraded at its location.*  It did not fire — that one hypothesis is all it
takes. -/

/-- The number of zeros sitting at atoms the predicate `good` accepts.  `good`
is an arbitrary property of the atom's profile entry `(mass, off-line mass)` —
the finest local data there is, by `profile_minimal_among_local`. -/
noncomputable def goodCount (D : ZeroData) (good : ℕ × ℕ → Prop)
    [DecidablePred good] : ℕ :=
  ((profile D).map fun q => if good q then q.1 else 0).sum

/-- **No goodness proportion of any kind bounds `N⊛`.**

Let `good` be *any* predicate on atoms whatsoever, subject to the single
requirement that a simple on-line atom counts as good.  Then for every `B` there
is a configuration in which at least three quarters of the zeros sit at good
atoms and `N⊛ > B·N`.

This subsumes `no_starBound_from_proportionStd` (`good q ↔ q.1 - q.2 = 1`) and
`no_starBound_from_lowMult` (`good q ↔ q.1 ≤ k`), and it explains both: a
proportion bounds the *good* part from below and leaves the remainder
unconstrained, while `N⊛` is decided by the remainder. -/
theorem no_starBound_from_goodness {a : ℝ} (ha : a ≠ 1/2)
    (good : ℕ × ℕ → Prop) [DecidablePred good] (hgood : good (1, 0)) (B : ℕ) :
    ∃ D : ZeroData, 3 * D.N ≤ 4 * goodCount D good ∧ B * D.N < D.Nstar := by
  classical
  set m := 4 * B + 4 with hm
  set L : List (ℕ × ℕ) := List.replicate (3 * m) (1, 0) ++ [(m, 0)] with hL
  have hne : ∀ p ∈ L, p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [hL, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.eq_of_mem_replicate hp]; norm_num
    · simp only [List.mem_singleton] at hp
      rw [hp]; omega
  have hp := chain_profile ha L hne
  rw [hL] at hp
  norm_num [List.map_append, List.map_replicate] at hp
  have hN : (chain a L).N = 4 * m := by
    rw [N_from_profile, hp]; simp; try ring
  have hS : (chain a L).Nstar = 3 * m + m * m := by
    rw [Nstar_from_profile, hp]; simp; try ring
  have hG : 3 * m ≤ goodCount (chain a L) good := by
    rw [goodCount, hp]
    simp [hgood]
  refine ⟨chain a L, by omega, ?_⟩
  rw [hN, hS]
  nlinarith [Nat.zero_le B, hm]

/-- **`lowMult` is a `goodCount`**, so `no_starBound_from_lowMult` is a genuine
instance of `no_starBound_from_goodness` and not merely an analogue. -/
lemma lowMult_eq_goodCount (D : ZeroData) (k : ℕ) :
    lowMult D k = goodCount D (fun q => q.1 ≤ k) := by
  classical
  have key : ((lowMult D k : ℕ) : ℤ) = ((goodCount D (fun q => q.1 ≤ k) : ℕ) : ℤ) := by
    have e : Multiset.card (D.ordinates.filter fun γ => D.H γ ≤ k) = lowMult D k := by
      rw [ZeroData.ordinates, Multiset.filter_map, Multiset.card_map, lowMult]
      rfl
    rw [← e, card_filter_eq_sum, Finset.sum_multiset_map_count]
    have hstep : ∀ γ ∈ D.ordinates.toFinset,
        D.ordinates.count γ • (if D.H γ ≤ k then (1 : ℤ) else 0)
          = (if D.H γ ≤ k then (D.H γ : ℤ) else 0) := by
      intro γ _
      rw [← D.H_eq_count]
      by_cases h : D.H γ ≤ k
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]; simp
    rw [Finset.sum_congr rfl hstep]
    have hprof : ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ ≤ k then (D.H γ : ℤ) else 0)
          = ((profile D).map fun q => if q.1 ≤ k then (q.1 : ℤ) else 0).sum := by
      rw [profile, Multiset.map_map]
      rfl
    rw [hprof, goodCount]
    push_cast
    rw [Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
    by_cases h : q.1 ≤ k <;> simp [h]
  exact_mod_cast key

/-- **…and at *every* proportion below `1`, not just `3/4`.**

`no_starBound_from_goodness` fixes the good proportion at `3/4`, which does not
exclude a hypothesis of the form "at least `99%` of the zeros are good".  This
does: for any rational level `p/q < 1` and any `B`, a configuration with at least
that proportion of its zeros at good atoms and `N⊛ > B·N`.

The family is `c·m` simple atoms beside one atom of mass `m`, with `c` chosen
from the level and `m` from `B`: the good proportion is `c/(c+1)`, pushed as
close to `1` as required, while `N⊛/N = (c+m)/(c+1)` still runs away in `m`.

**Kill condition, filed first:** *if the witness cannot be pushed past some
`α < 1`, proportions above that level are not excluded and `094`'s might-mean
must be downgraded.*  It did not fire. -/
theorem no_starBound_from_goodness_at_any_level {a : ℝ} (ha : a ≠ 1/2)
    (good : ℕ × ℕ → Prop) [DecidablePred good] (hgood : good (1, 0))
    (p q B : ℕ) (hpq : p < q) :
    ∃ D : ZeroData, p * D.N ≤ q * goodCount D good ∧ B * D.N < D.Nstar := by
  classical
  set c := max p 1 with hc
  set m := (c + 1) * (B + 1) + 1 with hm
  set L : List (ℕ × ℕ) := List.replicate (c * m) (1, 0) ++ [(m, 0)] with hL
  have hc1 : 1 ≤ c := le_max_right _ _
  have hcp : p ≤ c := le_max_left _ _
  have hne : ∀ x ∈ L, x.1 + 2 * x.2 ≠ 0 := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]; norm_num
    · simp only [List.mem_singleton] at hx
      rw [hx]; omega
  have hp := chain_profile ha L hne
  rw [hL] at hp
  norm_num [List.map_append, List.map_replicate] at hp
  have hN : (chain a L).N = c * m + m := by
    rw [N_from_profile, hp]; simp; try ring
  have hS : (chain a L).Nstar = c * m + m * m := by
    rw [Nstar_from_profile, hp]; simp; try ring
  have hG : c * m ≤ goodCount (chain a L) good := by
    rw [goodCount, hp]
    simp [hgood]
  refine ⟨chain a L, ?_, ?_⟩
  · rw [hN]
    have hcq : p * (c + 1) ≤ q * c := by nlinarith [hcp, hc1, hpq]
    calc p * (c * m + m) = (p * (c + 1)) * m := by ring
      _ ≤ (q * c) * m := Nat.mul_le_mul hcq (le_refl m)
      _ = q * (c * m) := by ring
      _ ≤ q * goodCount (chain a L) good := Nat.mul_le_mul (le_refl q) hG
  · rw [hN, hS, hm]
    nlinarith [hc1, Nat.zero_le B]

/-! ### The bare supremum is useless; the supremum *plus the row* is not

`092` showed a multiplicity supremum `M` gives `StarBound M`, useless for `prop1`
unless `M ≤ 1`.  That is correct about the **bare** supremum.  Combined with a
lower bound on `Nsc` — which the ledger now certifies — it does much better,
because the simple atoms cost `1` each rather than `M`.

**Kill condition, filed first:** *if the joint criterion cannot give `C < 2` at
any `M ≥ 2`, multiplicity control never substitutes for simplicity and `092`'s
wall is total.*  **It did not fire — `M = 2` suffices.** -/

/-- **`N⊛ + M·Nsc ≤ (1 + M)·N`** for any multiplicity supremum `M`.

⚠️ **Superseded (SESSION 098) by `Nstar_add_pred_mul_Nsc_le`**, which is this
bound improved by exactly `N − Nsc`: the sharp per-atom estimate is
`H² + (M−1)·[H = 1] ≤ M·H`, tight at `H = 1` *and* at `H = M`.  Kept because the
`096` narrative refers to it.

Per atom: `H² + M·[H = 1] ≤ H + M·H`, with equality at `H = 1` and slack
`H(M − H)` above.  Dividing by `N`: `C ≤ 1 + M·(1 − Nsc/N)` — the simple atoms
are charged `1`, not `M`, and a certified `Nsc` row therefore buys down the star
constant. -/
theorem Nstar_add_mul_Nsc_le (D : ZeroData) (M : ℕ) (h : ∀ γ, D.H γ ≤ M) :
    D.Nstar + M * D.Nsc ≤ (1 + M) * D.N := by
  classical
  have key : (D.Nstar : ℤ) + M * D.Nsc ≤ (1 + M) * D.N := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    have hS0 : D.Nstar = ∑ γ ∈ D.ordinates.toFinset, D.H γ * D.H γ :=
      Nstar_eq_sum_H_sq D
    have hS : (D.Nstar : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℤ) * (D.H γ : ℤ)) := by
      rw [hS0, Nat.cast_sum]; push_cast; rfl
    rw [hS, hB, hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have hHM : (D.H γ : ℤ) ≤ (M : ℤ) := by exact_mod_cast h γ
    have hH0 : (0 : ℤ) ≤ (D.H γ : ℤ) := Int.natCast_nonneg _
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, hone]
      push_cast
      ring_nf
      nlinarith [hHM, hH0]
    · rw [if_neg hone]
      nlinarith [hHM, hH0]
  exact_mod_cast key

/-! ### At `M = 2` the constant is exact, and much better

`096` charged a crowded atom `M·H`.  At `M = 2` there is nothing to estimate:
every atom has `H ∈ {1, 2}` and `H² + [H = 1] = 2H` **exactly**.

**Kill condition, filed first:** *if the sharpened `M = 2` analysis does not beat
`096`'s constant, the loose bound was already tight and there is nothing here.*
**It did not fire — the constant drops from `1.9825` to `2 − κ`.** -/

/-- **Under multiplicity `≤ 2`, standard-simple *is* simple.**  A standard-simple
atom has `onAt = 1` and even off-line part; with `H ≤ 2` that forces `off = 0`,
so `H = 1`.  The two notions the project keeps carefully apart coincide exactly
where this hypothesis holds — and the literature's row is stated on the *standard*
notion. -/
theorem Nsc_eq_NscStd_of_mult_le_two (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    D.Nsc = D.NscStd := by
  classical
  have key : (D.Nsc : ℤ) = (D.NscStd : ℤ) := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    rw [hB, hA]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    have h2 := h γ
    by_cases hone : D.H γ = 1
    · rw [if_pos hone]
      rw [if_pos (by omega)]
    · rw [if_neg hone]
      rw [if_neg (by omega)]
  exact_mod_cast key

/-- **Under multiplicity `≤ 2` the star constant is exact:** `N⊛ + Nsc = 2·N`.
Per atom, `H² + [H = 1] = 2H` with `H ∈ {1, 2}` — an identity, not an estimate.
So `C = 2 − Nsc/N`, and `prop1`'s output `2 − C` is exactly `Nsc/N`. -/
theorem Nstar_add_Nsc_eq_two_mul_N (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    D.Nstar + D.Nsc = 2 * D.N := by
  classical
  have key : (D.Nstar : ℤ) + D.Nsc = 2 * D.N := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    have hS : (D.Nstar : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℤ) * (D.H γ : ℤ)) := by
      rw [Nstar_eq_sum_H_sq D, Nat.cast_sum]; push_cast; rfl
    rw [hS, hB, hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hpos : 0 < D.H γ := by
      rw [ZeroData.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 hγ
    have h2 := h γ
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, hone]; norm_num
    · have he : D.H γ = 2 := by omega
      rw [if_neg hone, he]; norm_num
  exact_mod_cast key

/-- **The sharp form at every `M`: `N⊛ + (M−1)·Nsc ≤ M·N`.**

`096` proved `N⊛ + M·Nsc ≤ (1 + M)·N`, which is loose by `N − Nsc`: it charges a
simple atom `1` and *also* keeps a spare `H`.  The tight linear-in-`H` estimate is

> per atom, `H² + (M − 1)·[H = 1] ≤ M·H`,

with **equality at `H = 1` and at `H = M`** — so the bound cannot be improved
within this shape.  Dividing by `N`: `C ≤ M − (M − 1)·κ`, which is `< 2` exactly
when `κ > 1 − 1/(M − 1)`.

At the unconditional `κ = 0.50875` that threshold is met for `M ≤ 3`, so the
sufficient hypothesis weakens from `097`'s "multiplicity `≤ 2`" to
**"multiplicity `≤ 3`"**. -/
theorem Nstar_add_pred_mul_Nsc_le (D : ZeroData) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ γ, D.H γ ≤ M) : D.Nstar + (M - 1) * D.Nsc ≤ M * D.N := by
  classical
  have key : (D.Nstar : ℤ) + ((M : ℤ) - 1) * D.Nsc ≤ (M : ℤ) * D.N := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    have hS : (D.Nstar : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℤ) * (D.H γ : ℤ)) := by
      rw [Nstar_eq_sum_H_sq D, Nat.cast_sum]; push_cast; rfl
    rw [hS, hB, hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have hHM : (D.H γ : ℤ) ≤ (M : ℤ) := by exact_mod_cast h γ
    have hH0 : (0 : ℤ) ≤ (D.H γ : ℤ) := Int.natCast_nonneg _
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, hone]; push_cast; ring_nf; nlinarith [hHM, hH0]
    · rw [if_neg hone]; nlinarith [hHM, hH0]
  have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    have : (1 : ℕ) ≤ M := hM
    omega
  have : ((D.Nstar + (M - 1) * D.Nsc : ℕ) : ℤ) ≤ ((M * D.N : ℕ) : ℤ) := by
    push_cast [hcast]
    exact key
  exact_mod_cast this

/-- **The criterion tolerates exceptions, and the tolerance is `√N`.**

`Nstar_add_pred_mul_Nsc_le` needs a supremum on *every* ordinate.  Allow a set of
exceptional ordinates carrying `E` zeros in total, with `H ≤ M` outside it:

> `N⊛ + (M−1)·Nsc ≤ M·N + E²`.

The exceptional term is `E²` because the worst arrangement puts all `E` zeros at
one ordinate, and `Σ H² ≤ (Σ H)²`.  So `(★)` survives exactly while
`E² = o(N)` — an exceptional set of size `o(√N)`.

**Kill condition, filed first:** *if the exceptional set can be as large as
`o(N)`, the square-root threshold is not the real boundary.*  It did not fire:
`E = c√N` contributes `c²N`, which shifts `C` by `c²` and is not `o(1)`. -/
theorem Nstar_add_pred_mul_Nsc_le_except (D : ZeroData) (M : ℕ) (hM : 1 ≤ M)
    (exc : ℝ → Prop) [DecidablePred exc]
    (h : ∀ γ, ¬ exc γ → D.H γ ≤ M) :
    D.Nstar + (M - 1) * D.Nsc
      ≤ M * D.N + (∑ γ ∈ D.ordinates.toFinset.filter exc, D.H γ) ^ 2 := by
  classical
  set S := D.ordinates.toFinset with hSdef
  set E := ∑ γ ∈ S.filter exc, D.H γ with hE
  have hN0 : D.N = ∑ γ ∈ S, D.H γ := by
    rw [N_from_profile, profile, Multiset.map_map]; rfl
  have hS0 : D.Nstar = ∑ γ ∈ S, D.H γ * D.H γ := Nstar_eq_sum_H_sq D
  have hB0 : D.Nsc = ∑ γ ∈ S, (if D.H γ = 1 then 1 else 0) := by
    have : (D.Nsc : ℤ) = ∑ γ ∈ S, (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    exact_mod_cast this
  -- split every sum along `exc`
  have hsplit : ∀ f : ℝ → ℕ, ∑ γ ∈ S, f γ
      = (∑ γ ∈ S.filter exc, f γ) + ∑ γ ∈ S.filter (fun γ => ¬ exc γ), f γ :=
    fun f => (Finset.sum_filter_add_sum_filter_not S exc f).symm
  -- exceptional part: `Σ H² ≤ E²`
  have hexc : ∑ γ ∈ S.filter exc, (D.H γ * D.H γ + (M - 1) * (if D.H γ = 1 then 1 else 0))
      ≤ E * E + (M - 1) * E := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    refine Nat.add_le_add ?_ ?_
    · calc ∑ γ ∈ S.filter exc, D.H γ * D.H γ
          ≤ ∑ γ ∈ S.filter exc, D.H γ * E :=
            Finset.sum_le_sum fun γ hγ => Nat.mul_le_mul_left _
              (Finset.single_le_sum (f := D.H) (fun _ _ => Nat.zero_le _) hγ)
        _ = E * E := by rw [← Finset.sum_mul]
    · refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun γ hγ => ?_)
      by_cases hh : D.H γ = 1
      · rw [if_pos hh, hh]
      · rw [if_neg hh]; exact Nat.zero_le _
  -- ordinary part: the sharp per-atom estimate
  have hord : ∑ γ ∈ S.filter (fun γ => ¬ exc γ),
      (D.H γ * D.H γ + (M - 1) * (if D.H γ = 1 then 1 else 0))
        ≤ M * ∑ γ ∈ S.filter (fun γ => ¬ exc γ), D.H γ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun γ hγ => ?_
    have hnot : ¬ exc γ := (Finset.mem_filter.1 hγ).2
    have hHM : D.H γ ≤ M := h γ hnot
    by_cases hh : D.H γ = 1
    · rw [if_pos hh, hh]; omega
    · rw [if_neg hh]
      have : D.H γ * D.H γ ≤ M * D.H γ := Nat.mul_le_mul_right _ hHM
      omega
  have hEle : E ≤ D.N := by
    rw [hN0]
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (le_refl _)
  have hNsplit := hsplit D.H
  have hcomb : D.Nstar + (M - 1) * D.Nsc
      = ∑ γ ∈ S, (D.H γ * D.H γ + (M - 1) * (if D.H γ = 1 then 1 else 0)) := by
    rw [hS0, hB0, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hcomb, hsplit (fun γ => D.H γ * D.H γ + (M - 1) * (if D.H γ = 1 then 1 else 0))]
  have : M * D.N = M * E + M * ∑ γ ∈ S.filter (fun γ => ¬ exc γ), D.H γ := by
    rw [hN0, hNsplit, Nat.mul_add, hE]
  rw [this]
  have hM1 : M - 1 ≤ M := Nat.sub_le _ _
  nlinarith [hexc, hord, hEle, hM1]

/-- **The hierarchy, machine-checked.**  `Nstar_add_pred_mul_Nsc_le` is the
`E = 0` case of `Nstar_add_pred_mul_Nsc_le_except`, so the multiplicity family is
one theorem with three specialisations rather than four separate results.

Stated as a theorem rather than a comment because `S36` was a retraction filed
somewhere other than the text it corrected, and a thread of four superseding
results is the same hazard at larger scale. -/
theorem Nstar_add_pred_mul_Nsc_le_of_except (D : ZeroData) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ γ, D.H γ ≤ M) : D.Nstar + (M - 1) * D.Nsc ≤ M * D.N := by
  classical
  have := Nstar_add_pred_mul_Nsc_le_except D M hM (fun _ => False)
    (fun γ _ => h γ)
  simpa using this

/-- **`(★)` does not imply bounded multiplicity — the criterion is one-way.**

`096`–`100` give multiplicity hypotheses *sufficient* for `(★)`.  They are far
from necessary: for every `m` there is a configuration with `N⊛ < 2·N` — so
`(★)` holds with a constant strictly below `prop1`'s threshold — containing an
atom of mass `m`.

The family is `m²` simple atoms beside one atom of mass `m`:
`N = m² + m`, `N⊛ = 2m²`, and `2m² < 2m² + 2m`.

**Kill condition, filed first:** *if `(★)` with `C < 2` forces bounded
multiplicity, the criterion is an equivalence and the route table should say so.*
**It fired: `(★)` tolerates any fixed multiplicity**, so nobody should try to
extract multiplicity bounds from a star bound. -/
theorem starBound_allows_any_multiplicity {a : ℝ} (ha : a ≠ 1/2) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ D : ZeroData, D.Nstar < 2 * D.N ∧ ((m, 0) : ℕ × ℕ) ∈ profile D := by
  classical
  set L : List (ℕ × ℕ) := List.replicate (m * m) (1, 0) ++ [(m, 0)] with hL
  have hne : ∀ x ∈ L, x.1 + 2 * x.2 ≠ 0 := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]; norm_num
    · simp only [List.mem_singleton] at hx
      rw [hx]; omega
  have hp := chain_profile ha L hne
  rw [hL] at hp
  norm_num [List.map_append, List.map_replicate] at hp
  have hN : (chain a L).N = m * m + m := by
    rw [N_from_profile, hp]; simp; try ring
  have hS : (chain a L).Nstar = m * m + m * m := by
    rw [Nstar_from_profile, hp]; simp; try ring
  refine ⟨chain a L, ?_, ?_⟩
  · rw [hN, hS]; omega
  · rw [hp]; simp

/-- **`NscStd` cannot substitute for `Nsc` in the criterion once `M ≥ 3`.**

The per-atom estimate is `H² + (M−1)·[H = 1] ≤ M·H`.  The obvious improvement
would replace `[H = 1]` by `[onAt = 1]`, since `NscStd ≥ 0.6725` is both larger
and better certified than `Nsc ≥ 0.50875` — and would reach `M = 4`.

It is not available.  A **haunted** atom of mass `3` has `onAt = 1` and
`H² = 9 = M·H` at `M = 3`, leaving no room for any positive coefficient.  Below,
that atom witnesses it: `Nstar = 9`, `N = 3`, `NscStd = 1`, so
`Nstar + b·NscStd ≤ 3·N` forces `b ≤ 0`.

**Kill condition, filed first:** *if a positive coefficient on `[onAt = 1]` is
admissible at `M ≥ 3`, the criterion should use the stronger row and I have been
feeding it the weaker one.*  **It fired: no positive coefficient exists.** -/
theorem no_NscStd_coefficient_at_three {a : ℝ} (ha : a ≠ 1/2) {b : ℕ} (hb : 1 ≤ b) :
    ¬ (∀ D : ZeroData, (∀ γ, D.H γ ≤ 3) →
        D.Nstar + b * D.NscStd ≤ 3 * D.N) := by
  intro hcon
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by norm_num)
  norm_num at hp
  have hH : ∀ γ, (configAt 0 1 1 a).H γ ≤ 3 := by
    intro γ
    rw [ZeroData.H_eq_count, configAt_ordinates]
    have := Multiset.count_le_card γ (Multiset.replicate (1 + 2 * 1) (0:ℝ))
    simpa using this
  have hN : (configAt 0 1 1 a).N = 3 := by simpa using configAt_N (0:ℝ) 1 1 a
  have hS : (configAt 0 1 1 a).Nstar = 9 := by
    rw [Nstar_from_profile, hp]; decide
  have hSc : ((configAt 0 1 1 a).NscStd : ℤ) = 1 := by
    rw [NscStd_from_profile, hp]; decide
  have hSc' : (configAt 0 1 1 a).NscStd = 1 := by exact_mod_cast hSc
  have := hcon (configAt 0 1 1 a) hH
  rw [hN, hS, hSc'] at this
  omega

/-! ### The haunted atom saturates everything

`102`'s might-mean said the project's arithmetic *is* the arithmetic of one
picture — a simple on-line zero with an off-line pair at the same height.  That
was rhetoric past any theorem, which is what `S37` is about.  It is checkable, so
here it is checked.

**Kill condition, filed first:** *if the haunted mass-`3` atom fails to attain
equality in any one of the project's inequalities, the "one picture" reading is
wrong and the might-mean gets downgraded at its location.*  It did not fire. -/

/-- **The haunted atom of mass `3` attains equality in seven certified
inequalities at once.**  `configAt 0 1 1 a` has `N = 3`, `N⊛ = 9`, `Nsc = 0`,
`NscStd = 1`, `N_off = 2`, one odd atom and one atom.

Every bound the project has proved about the relationship between its counts is
tight *here*, and at a single three-element configuration. -/
theorem haunted_atom_saturates {a : ℝ} (ha : a ≠ 1/2) :
    let D := configAt 0 1 1 a
    3 * D.NscStd = D.N + 2 * D.Nsc
      ∧ 2 * D.NscStd = D.Noff + 2 * D.Nsc
      ∧ D.Nstar + (3 - 1) * D.Nsc = 3 * D.N
      ∧ D.Noff + D.NscStd = D.N
      ∧ D.Noff + oddAtoms D = D.N
      ∧ D.NscStd = oddAtoms D
      ∧ 2 * atomCount D + oddAtoms D = D.N + 2 * D.Nsc := by
  intro D
  obtain ⟨hSc0, hsc0, hN0⟩ := haunted_atom_counts ha
  have hSc : D.NscStd = 1 := hSc0
  have hsc : D.Nsc = 0 := hsc0
  have hN : D.N = 3 := hN0
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by norm_num)
  norm_num at hp
  have hOff : D.Noff = 2 := by
    show (configAt 0 1 1 a).Noff = 2
    rw [configAt_Noff ha]
  have hS : D.Nstar = 9 := by
    show (configAt 0 1 1 a).Nstar = 9
    rw [Nstar_from_profile, hp]; decide
  have hOdd : oddAtoms D = 1 := by
    show oddAtoms (configAt 0 1 1 a) = 1
    rw [oddAtoms_from_profile, hp]; decide
  have hA : atomCount D = 1 := by
    show atomCount (configAt 0 1 1 a) = 1
    rw [atomCount, configAt_ordinates, Multiset.toFinset_replicate, if_neg (by norm_num)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hSc, hsc, hN, hOff, hS, hOdd, hA] <;> norm_num

/-! ### The extremal family, characterised

`103` showed the haunted mass-`3` atom saturates seven bounds and declined to
claim uniqueness.  It is not unique — the **simple** atom saturates all seven
too — so the right question is which configurations are extremal, and for the
project's central bound `3·NscStd ≤ N + 2·Nsc` (`084`, the `Nsc` row) the answer
is exact.

**Kill condition, filed first:** *if some atom shape outside "simple, or haunted
of mass 3" also gives per-atom equality, the characterisation is wrong.*  It did
not fire: `H = 2` gives `0 < 2`, `H = 3` with `onAt = 3` gives `0 < 3`, and a
haunted atom of mass `5` gives `3 < 5`. -/

/-- **Equality in the `Nsc` row's bound holds exactly on mixtures of simple and
haunted-mass-`3` atoms.**

`3·NscStd = N + 2·Nsc` iff every ordinate carries either one zero, or three with
exactly one on the line.  Those are the two configurations of
`haunted_atom_saturates`, and nothing else. -/
theorem three_mul_NscStd_eq_iff (D : ZeroData) :
    3 * D.NscStd = D.N + 2 * D.Nsc ↔
      ∀ γ ∈ D.ordinates.toFinset, D.H γ = 1 ∨ (D.H γ = 3 ∧ onAt D γ = 1) := by
  classical
  have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
      (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
    rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
  have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
      (if D.H γ = 1 then (1 : ℤ) else 0) := by
    rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
  have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
    rw [N_from_profile, profile, Multiset.map_map]; rfl
  have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
    rw [hN0, Nat.cast_sum]
  have hle : ∀ γ ∈ D.ordinates.toFinset,
      3 * (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0)
        ≤ (D.H γ : ℤ) + 2 * (if D.H γ = 1 then (1 : ℤ) else 0) := by
    intro γ _
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    split_ifs <;> omega
  have hsplit : (3 * D.NscStd = D.N + 2 * D.Nsc) ↔
      (∑ γ ∈ D.ordinates.toFinset,
          3 * (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0))
        = ∑ γ ∈ D.ordinates.toFinset,
          ((D.H γ : ℤ) + 2 * (if D.H γ = 1 then (1 : ℤ) else 0)) := by
    rw [← Finset.mul_sum, ← hA, Finset.sum_add_distrib, ← Finset.mul_sum, ← hB, ← hN]
    constructor
    · intro h; exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h
    · intro h; exact_mod_cast h
  rw [hsplit, Finset.sum_congr rfl (fun _ _ => rfl),
    (Finset.sum_eq_sum_iff_of_le hle)]
  refine forall_congr' fun γ => forall_congr' fun hγ => ?_
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  constructor
  · intro heq
    by_cases hone : D.H γ = 1
    · exact Or.inl hone
    · right
      rw [if_neg hone] at heq
      by_cases hsc : D.H γ - offAt D γ = 1
      · rw [if_pos hsc] at heq
        constructor <;> omega
      · rw [if_neg hsc] at heq
        have hpos : 0 < D.H γ := by
          rw [ZeroData.H_eq_count, Multiset.count_pos]
          exact Multiset.mem_toFinset.1 hγ
        omega
  · intro hcase
    rcases hcase with h | ⟨h3, hon⟩
    · rw [if_pos (by omega : D.H γ - offAt D γ = 1), if_pos h]
      simp [h]
    · rw [if_pos (by omega : D.H γ - offAt D γ = 1),
        if_neg (by omega : ¬ D.H γ = 1)]
      simp [h3]

/-! ### Excluding the smallest shadow: a ladder to the full baseline

`104` characterised the equality set of `3·NscStd ≤ N + 2·Nsc` as mixtures of
simple and **haunted mass-`3`** atoms.  So the constant `3` is forced by that one
shape.  Forbid it — allow haunted atoms only from mass `m` upward — and the
constant rises to `m`.

**Kill condition, filed first:** *if excluding low-mass haunted atoms does not
improve the constant, the shadow is not where the loss lives and `104`'s
might-mean is wrong.*  **It did not fire.** -/

/-- **The ladder: `m·NscStd ≤ N + (m−1)·Nsc` when every haunted atom has mass at
least `m`.**

The hypothesis is exactly "no standard-simple ordinate carries between `2` and
`m−1` zeros".  At `m = 3` it is vacuous and this is `084`'s bound; each odd step
upward buys a better constant, and the row it yields,
`(m·κ − 1)/(m − 1)`, increases to `κ` — the *whole* literature baseline. -/
theorem mul_NscStd_le_N_add_pred_mul_Nsc (D : ZeroData) (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ m ≤ D.H γ) :
    m * D.NscStd ≤ D.N + (m - 1) * D.Nsc := by
  classical
  have key : (m : ℤ) * D.NscStd ≤ (D.N : ℤ) + ((m : ℤ) - 1) * D.Nsc := by
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    rw [hA, hB, hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have hcase := h γ
    have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    by_cases hsc : D.H γ - offAt D γ = 1
    · rw [if_pos hsc]
      by_cases hone : D.H γ = 1
      · rw [if_pos hone, hone]; push_cast; linarith
      · rw [if_neg hone]
        rcases hcase hsc with h1 | hbig
        · exact absurd h1 hone
        · have hbZ : (m : ℤ) ≤ (D.H γ : ℤ) := by exact_mod_cast hbig
          omega
    · rw [if_neg hsc]
      have hH0 : (0 : ℤ) ≤ (D.H γ : ℤ) := Int.natCast_nonneg _
      split_ifs <;> omega
  have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have : ((m * D.NscStd : ℕ) : ℤ) ≤ ((D.N + (m - 1) * D.Nsc : ℕ) : ℤ) := by
    push_cast [hcast]
    exact key
  exact_mod_cast this

/-! ### The ladder is sharp — but only at *odd* rungs

`105` gives `m·NscStd ≤ N + (m−1)·Nsc` under `NoSmallHaunted m`.  Two questions
a future cycle would ask: is `m` the best constant, and does every `m` give a
distinct rung?

**Kill condition, filed first:** *if a constant larger than `m` is admissible
under `NoSmallHaunted m`, the ladder is not sharp and its rungs understate what
the hypothesis buys.*  **It fired — at even `m`.** -/

/-- **A standard-simple ordinate carries an odd number of zeros.**  `H = onAt +
offAt` with `offAt` even, and `onAt = 1`. -/
theorem haunted_odd (D : ZeroData) {γ : ℝ} (h : D.H γ - offAt D γ = 1)
    (hpos : 0 < D.H γ) : ¬ Even (D.H γ) := by
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  rw [Nat.not_even_iff_odd]
  exact ⟨(D.H γ - 1) / 2, by omega⟩

/-- **At even `m` the ladder understates: the hypothesis at `m` is already the
hypothesis at `m + 1`.**  Haunted ordinates carry odd mass, so "mass `≥ m`" and
"mass `≥ m + 1`" are the same requirement when `m` is even.  The sharp ladder is
therefore indexed by the **odd** numbers, and an even rung should be read up. -/
theorem noSmallHaunted_succ_of_even (D : ZeroData) (m : ℕ) (hm : Even m)
    (h : ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ m ≤ D.H γ) :
    ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ m + 1 ≤ D.H γ := by
  intro γ hsc
  rcases h γ hsc with hone | hbig
  · exact Or.inl hone
  · right
    by_cases hz : 0 < D.H γ
    · have hodd := haunted_odd D hsc hz
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 hodd
      obtain ⟨j, hj⟩ := hm
      omega
    · omega

/-- **…and at odd `m` the constant `m` cannot be improved.**  The haunted atom of
mass `m` is admitted by `NoSmallHaunted m` and has `NscStd = 1`, `Nsc = 0`,
`N = m`, so any valid `c·NscStd ≤ N + b·Nsc` has `c ≤ m`. -/
theorem ladder_sharp_at_odd {a : ℝ} (ha : a ≠ 1/2) {j : ℕ} (hj : 1 ≤ j) {c b : ℝ}
    (h : ∀ D : ZeroData,
      (∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ 1 + 2 * j ≤ D.H γ) →
        c * D.NscStd ≤ D.N + b * D.Nsc) :
    c ≤ 1 + 2 * j := by
  classical
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := j) (by omega)
  have hN : (configAt 0 1 j a).N = 1 + 2 * j := by simpa using configAt_N (0:ℝ) 1 j a
  have hSc : ((configAt 0 1 j a).NscStd : ℤ) = 1 := by
    rw [NscStd_from_profile, hp]; simp
  have hsc : ((configAt 0 1 j a).Nsc : ℤ) = 0 := by
    rw [Nsc_from_profile, hp]; simp; omega
  have hSc' : (configAt 0 1 j a).NscStd = 1 := by exact_mod_cast hSc
  have hsc' : (configAt 0 1 j a).Nsc = 0 := by exact_mod_cast hsc
  have hhyp : ∀ γ, (configAt 0 1 j a).H γ - offAt (configAt 0 1 j a) γ = 1 →
      (configAt 0 1 j a).H γ = 1 ∨ 1 + 2 * j ≤ (configAt 0 1 j a).H γ := by
    intro γ _
    right
    rw [ZeroData.H_eq_count, configAt_ordinates]
    by_cases hγ : γ = 0
    · rw [hγ]; simp
    · exfalso
      have : (configAt 0 1 j a).H γ = 0 := by
        rw [ZeroData.H_eq_count, configAt_ordinates, Multiset.count_replicate,
          if_neg (by simpa using Ne.symm hγ)]
      have h1 := H_eq_onAt_add_offAt (configAt 0 1 j a) γ
      omega
  have := h (configAt 0 1 j a) hhyp
  rw [hSc', hsc', hN] at this
  push_cast at this
  linarith

/-! ### Where the two conditional families meet

The registers now carry two unrelated ladders of hypotheses: multiplicity
(`H ≤ M`, `096`–`100`) and hauntedness (`NoSmallHaunted m`, `105`–`106`).  They
meet at the top.

**Kill condition, filed first:** *if "no haunted ordinates at all" fails to
deliver the full `κ` row, the ladder's limit is not attained and the two families
do not meet.*  It did not fire. -/

/-- **No haunted ordinates ⟹ the two simplicity notions coincide.**  This is the
`m → ∞` end of the ladder, and it gives the literature's row **whole**. -/
theorem Nsc_eq_NscStd_of_noHaunted (D : ZeroData)
    (h : ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1) : D.Nsc = D.NscStd := by
  classical
  have key : (D.Nsc : ℤ) = (D.NscStd : ℤ) := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    rw [hB, hA]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    by_cases hsc : D.H γ - offAt D γ = 1
    · rw [if_pos hsc, if_pos (h γ hsc)]
    · rw [if_neg hsc, if_neg (by intro hone; exact hsc (by omega))]
  exact_mod_cast key

/-- **`H ≤ 2` is strictly stronger than "no haunted ordinates".**  A haunted
ordinate carries odd mass `≥ 3` (`haunted_odd`), so a multiplicity bound of `2`
forbids them — but not conversely: an ordinate of mass `4` with every zero on the
line is unhaunted and violates `H ≤ 2`.

So `097`'s `Proportion 0.6725` needed less than it assumed.  What `H ≤ 2` buys
*beyond* the row is the star bound `C ≤ 1.3275`, which hauntedness alone does not
give. -/
theorem noHaunted_of_mult_le_two (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 := by
  intro γ hsc
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  have := h γ
  omega

/-- The converse fails: `configAt 0 4 0 a` has no haunted ordinate and mass `4`. -/
theorem noHaunted_not_mult_le_two {a : ℝ} (ha : a ≠ 1/2) :
    (∀ γ, (configAt 0 4 0 a).H γ - offAt (configAt 0 4 0 a) γ = 1 →
        (configAt 0 4 0 a).H γ = 1)
      ∧ ¬ (∀ γ, (configAt 0 4 0 a).H γ ≤ 2) := by
  classical
  have hH : (configAt 0 4 0 a).H 0 = 4 := by
    rw [ZeroData.H_eq_count, configAt_ordinates]; simp
  refine ⟨?_, ?_⟩
  · intro γ hsc
    have hoff : offAt (configAt 0 4 0 a) γ = 0 := by
      by_cases hγ : γ = 0
      · rw [hγ, offAt_configAt_self ha]
      · rw [offAt_configAt_other (a := a) hγ 4 0]
    omega
  · intro hcon
    have := hcon 0
    omega

/-- **`NoHaunted` is exactly "the two simplicity notions agree".**

`Nsc ≤ NscStd` always, pointwise: a mass-one ordinate has no off-line zeros to
carry.  The two counts are *equal* precisely when no ordinate is haunted.

So the hypothesis of `proportion_of_noHaunted` is not an ad-hoc condition
invented for that theorem — it is the exact content of `ISSUES #13`, the
distinction the project has carried since session 003, stated as an equation.

**Kill condition, filed first:** *if `Nsc = NscStd` can hold with a haunted
ordinate present, the equivalence fails and `NoHaunted` is strictly stronger than
agreement of the two notions.*  It did not fire.

*Candour: with this in hand `proportion_of_noHaunted` is a substitution, and its
content is this characterisation rather than the transfer.* -/
theorem Nsc_eq_NscStd_iff_noHaunted (D : ZeroData) :
    D.Nsc = D.NscStd ↔ ∀ γ ∈ D.ordinates.toFinset,
      D.H γ - offAt D γ = 1 → D.H γ = 1 := by
  classical
  have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
      (if D.H γ = 1 then (1 : ℤ) else 0) := by
    rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
  have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
      (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
    rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
  have hle : ∀ γ ∈ D.ordinates.toFinset,
      (if D.H γ = 1 then (1 : ℤ) else 0)
        ≤ (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
    intro γ _
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    split_ifs <;> omega
  have hcast : (D.Nsc = D.NscStd) ↔ ((D.Nsc : ℤ) = (D.NscStd : ℤ)) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hcast, hB, hA, Finset.sum_eq_sum_iff_of_le hle]
  refine forall_congr' fun γ => forall_congr' fun hγ => ?_
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  constructor
  · intro heq hsc
    by_contra hone
    rw [if_neg hone, if_pos hsc] at heq
    exact absurd heq (by norm_num)
  · intro himp
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, if_pos (by omega)]
    · rw [if_neg hone, if_neg (fun hsc => hone (himp hsc))]

/-! ### The master identity: `NscStd = Nsc + haunted`

`108` found that the whole conditional apparatus answers one question.  It also
*reduces* to one fact, and stating it makes `084`, the ladder and `NoHaunted`
corollaries rather than separate results.

**Kill condition, filed first:** *if `NscStd = Nsc + hauntedCount` fails — if
some ordinate is counted by `NscStd` without being simple or haunted — the
identity is wrong and the reduction does not exist.*  It did not fire. -/

/-- The number of **haunted** ordinates: a lone critical zero shadowed by
off-line pairs. -/
noncomputable def hauntedCount (D : ZeroData) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1).card

/-- **`hauntedCount` is read off the profile too** — `SESSION 181`.

The file carries five `_from_profile` theorems (`N`, `Noff`, `N⊛`, `Nsc`,
`NscStd`) and states that the profile determines the ledger.  `hauntedCount` —
the quantity this project coined, and the one every conditional route runs
through — had no such reading, for the same reason `180` found `atomCount`
lacked one: the connection is definitional and nobody wrote it down.

It is immediate, and it has to be: a profile entry is `(H γ, offAt γ)`, and
hauntedness is the predicate `H − offAt = 1 ∧ H ≠ 1` on exactly that pair.  So
`hauntedCount` was always a profile functional; now it says so.

**Why this is worth a line.**  `Blindness` argues that the profile is the
residue — everything the ledger can see. `HauntedDensity`, the ladder, and the
off-line exchange all consume `hauntedCount`, so had it *not* been a profile
functional, the blindness analysis would have had a hole exactly where the
project's own quantity lives. -/
theorem hauntedCount_from_profile (D : ZeroData) :
    hauntedCount D
      = Multiset.card ((profile D).filter fun q => q.1 - q.2 = 1 ∧ q.1 ≠ 1) := by
  classical
  rw [hauntedCount, profile, Multiset.filter_map, Multiset.card_map]
  rfl

/-- **`distinctZeros` is NOT a profile functional** — `SESSION 184`, settling the
obligation `181` opened and `182`/`183` narrowed.

`181` completed the profile↔ledger dictionary: every ledger quantity has a
profile reading.  `ZeroData`'s `distinctZeros` — the literature's `N_d`,
introduced at `167` for the Wu dictionary — has none, and cannot.

Both configurations put **four off-line zeros at one ordinate**, so both have
`H = 4`, `offAt = 4` and therefore the **same profile** `{(4, 4)}`.  They differ
in how that off-line *mass* splits into *points*:

* `configAt 0 0 2 a` — one pair at doubled multiplicity;
* `superpose (configAt 0 0 1 a) (configAt 0 0 1 b)` — two distinct pairs.

**This is why `167`/`168`'s dictionary had to be an inequality.**
`atomCount ≤ distinctZeros` cannot be strengthened to an identity, and no
profile-level argument can bound `N_d`, because the profile records off-line mass
and `N_d` counts points.

*Method note.*  `182` and `183` failed computing `distinctZeros` of the
four-point configuration directly (`Finset` cardinalities over multiset literals;
`simp` stalling, then `maximum recursion depth`).  The strict-subset route needs
no such computation: `A`'s support is contained in `B`'s, and `(b, 0)` is in `B`
and not in `A`, so `Finset.card_lt_card` gives the strict inequality without ever
counting `B`. -/
theorem distinctZeros_not_profile_functional {a b : ℝ}
    (ha : a ≠ 1/2) (hb : b ≠ 1/2) (hab : a ≠ b) (hab' : a ≠ 1 - b) :
    profile (configAt 0 0 2 a)
        = profile (superpose (configAt 0 0 1 a) (configAt 0 0 1 b))
      ∧ distinctZeros (configAt 0 0 2 a)
        < distinctZeros (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)) := by
  classical
  have hane : a ≠ 1 - a := fun h => ha (by linarith [h])
  have hba : b ≠ 1 - a := fun h => hab' (by linarith [h])
  constructor
  · have hA : (configAt 0 0 2 a).ordinates = Multiset.replicate 4 (0:ℝ) := by
      rw [configAt_ordinates]
    have hB : (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)).ordinates
        = Multiset.replicate 4 (0:ℝ) := by
      rw [add_ordinates, configAt_ordinates, configAt_ordinates,
        ← Multiset.replicate_add]
    have h1 : (configAt 0 0 2 a).H 0 = 4 := by rw [configAt_H]; norm_num
    have h2 : (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)).H 0 = 4 := by
      rw [H_superpose, configAt_H, configAt_H]; norm_num
    have h3 : offAt (configAt 0 0 2 a) 0 = 4 := by rw [configAt_offAt ha]
    have h4 : offAt (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)) 0 = 4 := by
      rw [offAt_superpose, configAt_offAt ha, configAt_offAt hb]
    rw [profile, profile, hA, hB, Multiset.toFinset_replicate,
      if_neg (by norm_num : ¬(4 = 0))]
    simp only [Finset.singleton_val, Multiset.map_singleton]
    rw [h1, h2, h3, h4]
  · rw [distinctZeros, distinctZeros]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro p hp
      rw [Multiset.mem_toFinset] at hp ⊢
      show p ∈ (configAt 0 0 1 a).Z + (configAt 0 0 1 b).Z
      rw [Multiset.mem_add]
      left
      revert hp
      show p ∈ (Multiset.replicate 0 ((1/2:ℝ),(0:ℝ))
        + (Multiset.replicate 2 (a,(0:ℝ)) + Multiset.replicate 2 ((1-a:ℝ),(0:ℝ)))) → _
      intro hp
      show p ∈ (Multiset.replicate 0 ((1/2:ℝ),(0:ℝ))
        + (Multiset.replicate 1 (a,(0:ℝ)) + Multiset.replicate 1 ((1-a:ℝ),(0:ℝ))))
      simp only [Multiset.replicate_zero, zero_add, Multiset.mem_add,
        Multiset.mem_replicate] at hp ⊢
      tauto
    · intro hsub
      have hmem : ((b,(0:ℝ)) : ℝ × ℝ)
          ∈ (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)).Z.toFinset := by
        rw [Multiset.mem_toFinset]
        show (b,(0:ℝ)) ∈ (configAt 0 0 1 a).Z + (configAt 0 0 1 b).Z
        rw [Multiset.mem_add]; right
        show (b,(0:ℝ)) ∈ (Multiset.replicate 0 ((1/2:ℝ),(0:ℝ))
          + (Multiset.replicate 1 (b,(0:ℝ)) + Multiset.replicate 1 ((1-b:ℝ),(0:ℝ))))
        simp
      have hcon := hsub hmem
      rw [Multiset.mem_toFinset] at hcon
      revert hcon
      show (b,(0:ℝ)) ∈ (Multiset.replicate 0 ((1/2:ℝ),(0:ℝ))
        + (Multiset.replicate 2 (a,(0:ℝ)) + Multiset.replicate 2 ((1-a:ℝ),(0:ℝ)))) → False
      simp only [Multiset.replicate_zero, zero_add, Multiset.mem_add,
        Multiset.mem_replicate]
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> rw [Prod.ext_iff] at h
      · exact hab.symm h.1
      · exact hba h.1

/-- **Both dictionary bounds are attained** — `SESSION 188`.

`167` and `168` sandwich the literature's `N_d` between two profile-side
quantities:

    atomCount ≤ distinctZeros ≤ atomCount + Noff

and `184` showed `distinctZeros` is not itself a profile functional, so the
sandwich is the most the profile can say.  The project checked tightness for
every other bound it owns (`169`, `175`, `178`–`180`); these two were never
asked.

**Both are equalities, and the upper one at the mass-`3` haunted atom** — the
same configuration that attains all six route bounds (`178`).  Its three zeros
are three *distinct* points, one on the line and two off it, so
`distinctZeros = 3 = atomCount + Noff = 1 + 2`.

The lower bound is attained by a single simple zero, where the ordinate carries
exactly one point.  So the sandwich is sharp on both sides and there is no slack
to recover: the profile determines `N_d` to within exactly `Noff`, and no
better. -/
theorem dictionary_bounds_attained {a : ℝ} (ha : a ≠ 1/2) :
    atomCount (configAt 0 1 0 a) = distinctZeros (configAt 0 1 0 a)
      ∧ distinctZeros (configAt 0 1 1 a)
          = atomCount (configAt 0 1 1 a) + (configAt 0 1 1 a).Noff := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  have hane : a ≠ 1 - a := fun h => ha (by linarith [h])
  constructor
  · -- one simple zero: one ordinate, one point
    have h1 : atomCount (configAt 0 1 0 a) = 1 := by
      rw [atomCount, configAt_ordinates]
      rw [show Multiset.replicate (1 + 2 * 0) (0:ℝ) = Multiset.replicate 1 (0:ℝ)
        by norm_num, Multiset.toFinset_replicate, if_neg (by norm_num : ¬(1 = 0))]
      simp
    have h2 : distinctZeros (configAt 0 1 0 a) = 1 := by
      show (Multiset.toFinset (Multiset.replicate 1 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 0 (a, (0:ℝ))
          + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))))).card = 1
      simp
    rw [h1, h2]
  · -- the mass-3 haunted atom: three distinct points, one ordinate, two off-line
    have hA : atomCount (configAt 0 1 1 a) = 1 := by
      rw [atomCount, configAt_ordinates]
      rw [show Multiset.replicate (1 + 2 * 1) (0:ℝ) = Multiset.replicate 3 (0:ℝ)
        by norm_num, Multiset.toFinset_replicate, if_neg (by norm_num : ¬(3 = 0))]
      simp
    have hO : (configAt 0 1 1 a).Noff = 2 := by rw [configAt_Noff ha]
    have hD : distinctZeros (configAt 0 1 1 a) = 3 := by
      show (Multiset.toFinset (Multiset.replicate 1 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 1 (a, (0:ℝ))
          + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))))).card = 3
      rw [Multiset.toFinset_add, Multiset.toFinset_add, Multiset.toFinset_replicate,
        Multiset.toFinset_replicate, Multiset.toFinset_replicate]
      norm_num
      have hh : a ≠ (2:ℝ)⁻¹ := by intro h; apply ha; rw [h]; norm_num
      have hh2 : ((2:ℝ)⁻¹) ≠ 1 - a := by intro h; apply ha'; rw [← h]; norm_num
      rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hh, hane]),
        Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hh2])]
      simp
    rw [hA, hO, hD]

/-- **`NscStd = Nsc + hauntedCount`** — an identity, not a bound.

Every standard-simple ordinate is either simple or haunted, and the two cases are
disjoint by definition.  So the gap between the literature's count and the
project's is *exactly* the number of haunted ordinates. -/
theorem NscStd_eq_Nsc_add_haunted (D : ZeroData) :
    D.NscStd = D.Nsc + hauntedCount D := by
  classical
  have key : (D.NscStd : ℤ) = (D.Nsc : ℤ) + (hauntedCount D : ℤ) := by
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hC : (hauntedCount D : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1 then (1 : ℤ) else 0) := by
      rw [hauntedCount, Finset.card_filter]; push_cast; rfl
    rw [hA, hB, hC, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, if_pos (by omega : D.H γ - offAt D γ = 1),
        if_neg (by simp [hone])]
      norm_num
    · rw [if_neg hone]
      by_cases hsc : D.H γ - offAt D γ = 1
      · rw [if_pos hsc, if_pos ⟨hsc, hone⟩]; norm_num
      · rw [if_neg hsc, if_neg (by tauto)]; norm_num
  exact_mod_cast key

/-- **`β = 1 − κ` is not a limitation of the producers — it is optimal.**
`SESSION 169`.

`162` found every `OffLineImport` in the development carrying `β = 1 − κ`, and
`161`/`168` found three routes dying because of it.  That left a question those
cycles did not ask: is `1 − κ` merely what our two producers happen to emit, or
the best any derivation from `ProportionStd κ` could give?

**The best.**  `Noff_add_NscStd_le_N` gives `Noff ≤ N − NscStd ≤ (1 − κ)·N`
directly, so no rearrangement of the same information does better — and the
bound is *attained*, so there is no slack to recover.

The witness is one ordinate carrying a single critical zero and one off-line
pair: `N = 3`, `Noff = 2`, `NscStd = 1`, and `2 + 1 = 3`.  Via
`NscStd_eq_Nsc_add_haunted` its `NscStd` is `0 + 1`, the atom being haunted
rather than simple.

**So `168`'s want-ad is for new arithmetic information, not for a cleverer
derivation.**  Any `β < 1 − κ` must consume something the proportion does not
contain. -/
theorem offLine_bound_attained {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 1 a).Noff + (configAt 0 1 1 a).NscStd = (configAt 0 1 1 a).N
      ∧ 0 < (configAt 0 1 1 a).N := by
  classical
  have hN : (configAt 0 1 1 a).N = 3 := by rw [configAt_N]
  have hOff : (configAt 0 1 1 a).Noff = 2 := by rw [configAt_Noff ha]
  have hNsc : (configAt 0 1 1 a).Nsc = 0 := by
    rw [ZeroData.Nsc, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro p hp hcon
    have hH : (configAt 0 1 1 a).H p.2 = 3 := by
      have : p.2 = 0 := by
        have := congrArg (fun m => Multiset.count p.2 m)
          (configAt_ordinates (0:ℝ) 1 1 a)
        by_contra hne
        have hmem : p.2 ∈ (configAt 0 1 1 a).ordinates :=
          Multiset.mem_map_of_mem _ hp
        rw [configAt_ordinates] at hmem
        exact hne (Multiset.eq_of_mem_replicate hmem)
      rw [this, configAt_H]; simp
    omega
  have hHnt : hauntedCount (configAt 0 1 1 a) = 1 := by
    rw [hauntedCount, configAt_ordinates]
    rw [show Multiset.replicate (1 + 2 * 1) (0:ℝ) = Multiset.replicate 3 (0:ℝ) by norm_num]
    rw [Multiset.toFinset_replicate]
    rw [if_neg (by norm_num : ¬(3 = 0))]
    rw [Finset.filter_singleton]
    rw [if_pos]
    · simp
    · constructor
      · rw [configAt_H, configAt_offAt ha]; simp
      · rw [configAt_H]; simp
  have := NscStd_eq_Nsc_add_haunted (configAt 0 1 1 a)
  omega

/-- **Proximity to the line places no bound on the off-line count** — `SESSION
170`.

`168` reduced the off-line, simple-zero and distinct-zero shelves to one missing
number: a bound `Noff ≤ β·N` with `β < 1 − κ`.  `169` showed it cannot come from
`ProportionStd κ`.  The natural next hope is the narrow box — `Gaps.NarrowBox`,
the hypothesis Route III consumes, asserting every zero lies within `b/log T` of
the critical line.

**It supplies nothing here.**  `NarrowBox` constrains how *far* a zero sits from
the line; `Noff` counts how *many* sit off it, and a zero at
`β = 1/2 + 10⁻⁶/log T` is off-line exactly as much as one at `β = 0.9`.  For
every `ε > 0` there is a configuration whose zeros all lie within `ε` of the line
and whose off-line count is **all of them**.

So Route III's hypothesis and `168`'s want-ad are different asks, and Route III
does not pay through the off-line exchange at all — it reaches the row through
`StarBound`, which is why its axiom cone is `1` and why the `β = 1 − κ` wall does
not touch it. -/
theorem offLine_count_not_bounded_by_proximity {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ZeroData, 0 < D.N ∧ D.Noff = D.N
      ∧ ∀ p ∈ D.Z, |p.1 - 1/2| ≤ ε := by
  classical
  set a : ℝ := 1/2 + min ε 1 / 2 with ha_def
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have ha : a ≠ 1/2 := by
    rw [ha_def]; intro h; nlinarith [hmin]
  have hdist : |a - 1/2| ≤ ε := by
    rw [ha_def, abs_of_nonneg (by nlinarith [hmin] : (0:ℝ) ≤ 1/2 + min ε 1 / 2 - 1/2)]
    nlinarith [min_le_left ε 1, min_le_right ε 1, hmin]
  have hdist' : |(1 - a) - 1/2| ≤ ε := by
    have : (1 - a) - 1/2 = -(a - 1/2) := by ring
    rw [this, abs_neg]; exact hdist
  refine ⟨configAt 0 0 1 a, ?_, ?_, ?_⟩
  · rw [configAt_N]; norm_num
  · rw [configAt_N, configAt_Noff ha]
  · intro p hp
    have : p ∈ Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 1 (a, (0:ℝ))
          + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))) := hp
    simp only [Multiset.replicate_zero, zero_add, Multiset.mem_add,
      Multiset.mem_replicate] at this
    rcases this with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> assumption

/-- **One configuration attains every route constant at once** — `SESSION 178`.

`176` counted **99** inequality-concluding theorems against about **21**
tightness witnesses and withdrew the claim that all were tight.  The question it
did not ask: are the ones on a **route to the ledger** among the 21?

They are, and they are tight *together*.  The single ordinate carrying one
critical zero and one off-line pair — `configAt 0 1 1 a`, the haunted atom of
mass `3` — has

    N = 3,  N⊛ = 9,  Nsc = 0,  NscStd = 1,  Noff = 2,  haunted = 1,  atomCount = 1

and every route constant is an **equality** there:

| bound | at this configuration |
|---|---|
| `Noff + NscStd ≤ N` (`169`, the off-line optimum) | `2 + 1 = 3` |
| `2·haunted + NscStd ≤ N` (`110`'s canonical bound) | `2 + 1 = 3` |
| `2·haunted + atomCount ≤ N` (the distinct-zeros route) | `2 + 1 = 3` |
| `6·haunted + N ≤ N⊛` (the `StarBound` route's `/6`) | `6 + 3 = 9` |
| `3·NscStd ≤ N + 2·Nsc` (`084`) | `3 = 3` |
| `Nsc + 3·haunted ≤ N` (mass accounting) | `0 + 3 = 3` |

So the `21/99` of `176` is a count dominated by plumbing: **every constant on a
route is tight, and they are tight at one object.** The remaining tightness
questions are about lemmas no route consumes. -/
theorem mass_three_atom_attains_all {a : ℝ} (ha : a ≠ 1/2) :
    let D := configAt 0 1 1 a
    D.N = 3 ∧ D.Nstar = 9 ∧ D.Nsc = 0 ∧ D.NscStd = 1 ∧ D.Noff = 2
      ∧ hauntedCount D = 1 ∧ atomCount D = 1 := by
  classical
  obtain ⟨hEq, -⟩ := offLine_bound_attained ha
  have hN : (configAt 0 1 1 a).N = 3 := by rw [configAt_N]
  have hOff : (configAt 0 1 1 a).Noff = 2 := by rw [configAt_Noff ha]
  have hNscStd : (configAt 0 1 1 a).NscStd = 1 := by omega
  have hA : atomCount (configAt 0 1 1 a) = 1 := by
    rw [atomCount, configAt_ordinates]
    rw [show Multiset.replicate (1 + 2 * 1) (0:ℝ) = Multiset.replicate 3 (0:ℝ)
      by norm_num, Multiset.toFinset_replicate, if_neg (by norm_num : ¬(3 = 0))]
    simp
  have hS : (configAt 0 1 1 a).Nstar = 9 := by
    have hsum : (configAt 0 1 1 a).Nstar
        = ((configAt 0 1 1 a).Z.map fun _ : ℝ × ℝ => 3).sum := by
      show ((configAt 0 1 1 a).Z.map fun p => (configAt 0 1 1 a).H p.2).sum = _
      congr 1
      refine Multiset.map_congr rfl fun p hp => ?_
      have hp2 : p.2 = 0 := by
        have hmem : p.2 ∈ (configAt 0 1 1 a).ordinates :=
          Multiset.mem_map_of_mem _ hp
        rw [configAt_ordinates] at hmem
        exact Multiset.eq_of_mem_replicate hmem
      rw [hp2, configAt_H]; simp
    rw [hsum, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
    rw [show Multiset.card (configAt 0 1 1 a).Z = (configAt 0 1 1 a).N from rfl, hN]
  have hNsc : (configAt 0 1 1 a).Nsc = 0 := by
    rw [ZeroData.Nsc, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro p hp hcon
    have hp2 : p.2 = 0 := by
      have hmem : p.2 ∈ (configAt 0 1 1 a).ordinates :=
        Multiset.mem_map_of_mem _ hp
      rw [configAt_ordinates] at hmem
      exact Multiset.eq_of_mem_replicate hmem
    have : (configAt 0 1 1 a).H p.2 = 3 := by rw [hp2, configAt_H]; simp
    omega
  have hH : hauntedCount (configAt 0 1 1 a) = 1 := by
    have := NscStd_eq_Nsc_add_haunted (configAt 0 1 1 a)
    omega
  exact ⟨hN, hS, hNsc, hNscStd, hOff, hH, hA⟩

/-- **And the extremal point is not isolated — it scales** — `SESSION 179`.

`178` showed the haunted mass-`3` atom attains every route bound at once, but
that is a single `ZeroData` with `N = 3`.  `Proportion` is **asymptotic over
families** (`111`'s lesson: a small witness does not refute a `Family`-level
claim), so the question is whether the equalities survive at arbitrary size.

They do.  The chain of `n` haunted mass-`3` atoms has `N = 3n`, `NscStd = n`,
`Nsc = 0`, `Noff = 2n` and `hauntedCount = n`, and four of `178`'s six bounds are
equalities at **every** `n`.  So no route bound improves asymptotically: the
tightness is a property of the configuration *type*, not of one small instance.

*Scope, stated:* the two bounds involving `N⊛` and `atomCount`
(`6·haunted + N ≤ N⊛`, `2·haunted + atomCount ≤ N`) are **not lifted here** —
they need chain-level `Nstar` and `atomCount` lemmas the file does not have, and
`178` establishes them only at `n = 1`.  Four of six, said plainly rather than
rounded up. -/
theorem haunted_chain_attains {a : ℝ} (ha : a ≠ 1/2) (n : ℕ) :
    let C := chain a (List.replicate n ((1 : ℕ), (1 : ℕ))
      ++ List.replicate (n - n) ((3 : ℕ), (0 : ℕ)))
    C.Noff + C.NscStd = C.N
      ∧ 2 * hauntedCount C + C.NscStd = C.N
      ∧ 3 * C.NscStd = C.N + 2 * C.Nsc
      ∧ C.Nsc + 3 * hauntedCount C = C.N := by
  classical
  obtain ⟨-, hStd, hSc, -⟩ := bracket_tight_chain ha n n (le_refl n)
  obtain ⟨hOff, hN⟩ := Noff_tight_chain ha n n (le_refl n)
  have hid := NscStd_eq_Nsc_add_haunted
    (chain a (List.replicate n ((1 : ℕ), (1 : ℕ))
      ++ List.replicate (n - n) ((3 : ℕ), (0 : ℕ))))
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- `atomCount` is the profile's length: one pair per distinct ordinate. -/
lemma atomCount_eq_card_profile (D : ZeroData) :
    atomCount D = Multiset.card (profile D) := by
  classical
  rw [atomCount, profile, Multiset.card_map]
  rfl

/-- **The other two bounds lift as well: six of six** — `SESSION 180`.

`179` lifted four of `178`'s six equalities to the chain and left the two
involving `N⊛` and `atomCount` at `n = 1`, naming what they needed: chain-level
`Nstar` and `atomCount`.  Both come from `chain_profile`, which was already
there — the profile of `n` haunted mass-`3` atoms is `n` copies of `(3, 2)`, so
`N⊛ = 9n` by `Nstar_from_profile` and `atomCount = n` by counting pairs.

With `179`, **every route bound of `178` is an equality at every `n`.** -/
theorem haunted_chain_attains_star_and_atoms {a : ℝ} (ha : a ≠ 1/2) (n : ℕ) :
    let C := chain a (List.replicate n ((1 : ℕ), (1 : ℕ)))
    C.Nstar = 9 * n ∧ atomCount C = n := by
  classical
  have hne : ∀ p ∈ List.replicate n ((1 : ℕ), (1 : ℕ)), p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    norm_num
  have hprof : profile (chain a (List.replicate n ((1 : ℕ), (1 : ℕ))))
      = Multiset.replicate n ((3 : ℕ), (2 : ℕ)) := by
    rw [chain_profile ha _ hne]
    simp [List.map_replicate, Multiset.coe_replicate]
  refine ⟨?_, ?_⟩
  · rw [Nstar_from_profile, hprof, Multiset.map_replicate, Multiset.sum_replicate,
      smul_eq_mul]
    norm_num
    ring
  · rw [atomCount_eq_card_profile, hprof, Multiset.card_replicate]

/-- **The mass accounting: `Nsc + 3·hauntedCount ≤ N`.**  A simple ordinate
carries one zero, a haunted one at least three, and they are disjoint. -/
theorem Nsc_add_three_mul_haunted_le_N (D : ZeroData) :
    D.Nsc + 3 * hauntedCount D ≤ D.N := by
  classical
  have key : (D.Nsc : ℤ) + 3 * (hauntedCount D : ℤ) ≤ (D.N : ℤ) := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hC : (hauntedCount D : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1 then (1 : ℤ) else 0) := by
      rw [hauntedCount, Finset.card_filter]; push_cast; rfl
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    rw [hB, hC, hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun γ _ => ?_
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, if_neg (by simp [hone]), hone]; norm_num
    · rw [if_neg hone]
      by_cases hsc : D.H γ - offAt D γ = 1
      · rw [if_pos ⟨hsc, hone⟩]
        have : (3 : ℤ) ≤ (D.H γ : ℤ) := by
          have : 3 ≤ D.H γ := by omega
          exact_mod_cast this
        linarith
      · rw [if_neg (by tauto)]
        have : (0 : ℤ) ≤ (D.H γ : ℤ) := Int.natCast_nonneg _
        linarith
  exact_mod_cast key

/-- **`084` derived from the identity**, rather than from its own sum estimate:
`3·NscStd = 3·Nsc + 3·hauntedCount ≤ 3·Nsc + (N − Nsc) = N + 2·Nsc`. -/
theorem three_mul_NscStd_le_of_identity (D : ZeroData) :
    3 * D.NscStd ≤ D.N + 2 * D.Nsc := by
  have hid := NscStd_eq_Nsc_add_haunted D
  have hmass := Nsc_add_three_mul_haunted_le_N D
  omega

/-- **The canonical bound on the haunted count: `2·hauntedCount + NscStd ≤ N`.**

Each haunted ordinate carries at least two off-line zeros; each standard-simple
ordinate carries one on-line zero; the two collections are disjoint.  So

> `hauntedCount ≤ (N − NscStd)/2`,

and with `109`'s identity `Nsc/N = NscStd/N − hauntedCount/N` this *is* `084`:
the certified row `0.50875 = 0.6725 − 0.16375` reads off directly, with
`0.16375 = (1 − 0.6725)/2`.

Every route the registers have tried to the haunted count — through `N_off`
(`083`'s coupling), through the mass accounting (`109`), through the off-line
density row (`090`) — lands on this same inequality.

**Kill condition, filed first:** *if some configuration has
`2·hauntedCount + NscStd > N`, the bound is wrong and the haunted count is not
controlled this way.*  It did not fire. -/
theorem two_mul_haunted_add_NscStd_le_N (D : ZeroData) :
    2 * hauntedCount D + D.NscStd ≤ D.N := by
  have hid := NscStd_eq_Nsc_add_haunted D
  have hmass := Nsc_add_three_mul_haunted_le_N D
  omega

/-- **And it is attained exactly on the extremal family of `104`** — mixtures of
simple and haunted mass-`3` atoms.  Equality here is equality in `084`, by the
identity, so `three_mul_NscStd_eq_iff` characterises it. -/
theorem two_mul_haunted_add_NscStd_eq_iff (D : ZeroData) :
    2 * hauntedCount D + D.NscStd = D.N ↔
      ∀ γ ∈ D.ordinates.toFinset, D.H γ = 1 ∨ (D.H γ = 3 ∧ onAt D γ = 1) := by
  rw [← three_mul_NscStd_eq_iff D]
  have hid := NscStd_eq_Nsc_add_haunted D
  have hmass := Nsc_add_three_mul_haunted_le_N D
  constructor <;> intro h <;> omega

/-- **The certified row is within `0.0007` of the best possible from the
baseline alone.**

`110` claimed the counting is finished.  Here is the provable form: a
configuration of `1000` simple atoms and `321` haunted mass-`3` atoms has

> `NscStd/N = 1321/1963 ≈ 0.67295 ≥ 0.6725`  and
> `Nsc/N = 1000/1963 ≈ 0.50942`.

So **no argument using only `ProportionStd 0.6725` can certify a row above
`0.50943`**, and the ledger certifies `0.50875`.  The gap is `0.00068`, and it is
the discretisation of `s : h`, not slack in the method.

**Kill condition, filed first:** *if no configuration achieves haunted density
near `0.16375` at `NscStd/N ≥ 0.6725`, then `0.16375` is only our bound and
`110`'s "nothing further to extract" must be downgraded at its location.*  It did
not fire. -/
theorem row_essentially_optimal {a : ℝ} (ha : a ≠ 1/2) :
    ∃ D : ZeroData, 0 < D.N ∧ 6725 * D.N ≤ 10000 * D.NscStd
      ∧ 100000 * D.Nsc ≤ 50943 * D.N := by
  classical
  set L : List (ℕ × ℕ) :=
    List.replicate 1000 (1, 0) ++ List.replicate 321 (1, 1) with hL
  have hne : ∀ x ∈ L, x.1 + 2 * x.2 ≠ 0 := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]; norm_num
    · rw [List.eq_of_mem_replicate hx]; norm_num
  have hp := chain_profile ha L hne
  rw [hL] at hp
  norm_num [List.map_append, List.map_replicate] at hp
  have hN : (chain a L).N = 1963 := by
    rw [N_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, smul_eq_mul]
  have hSc : ((chain a L).NscStd : ℤ) = 1321 := by
    rw [NscStd_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, smul_eq_mul]
    norm_num
  have hsc : ((chain a L).Nsc : ℤ) = 1000 := by
    rw [Nsc_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, smul_eq_mul]
    norm_num
  have hSc' : (chain a L).NscStd = 1321 := by exact_mod_cast hSc
  have hsc' : (chain a L).Nsc = 1000 := by exact_mod_cast hsc
  exact ⟨chain a L, by rw [hN]; norm_num, by rw [hN, hSc']; norm_num,
    by rw [hN, hsc']; norm_num⟩

/-- **The cap witness satisfies every certified consequence of the baseline.**

`112` capped baseline-only arguments at `0.50944` with the `1000 : 321` witness.
That cap is only robust if the witness also survives the facts the project has
*derived* from the baseline — otherwise one of them would exclude it and the row
could be pushed higher by adjoining it.

The full accounting of the witness: `N = 1963`, `NscStd = 1321`, `Nsc = 1000`,
`N_off = 642`, `hauntedCount = 321`.  Then

* `N_off/N = 642/1963 ≈ 0.32705 ≤ 0.3275` — inside `certified_offline` (`090`);
* `N_off + NscStd = 1963 = N` — `090`'s disjointness, **tight**;
* `2·hauntedCount + NscStd = 1963 = N` — `110`'s canonical bound, **tight**;
* `Nsc + N_off = 1642 ≤ 1963` — `Nsc_add_Noff_le_N`.

**Kill condition, filed first:** *if the witness violates any certified
consequence of the baseline, the cap is not robust.*  It did not fire: the
witness sits inside the off-line row with `0.00045` to spare and saturates the
two bounds that are supposed to be tight on it. -/
theorem cap_witness_respects_derived {a : ℝ} (ha : a ≠ 1/2) :
    ∃ D : ZeroData, D.N = 1963 ∧ D.NscStd = 1321 ∧ D.Nsc = 1000
      ∧ D.Noff = 642 ∧ hauntedCount D = 321
      ∧ 10000 * D.Noff ≤ 3275 * D.N
      ∧ D.Noff + D.NscStd = D.N
      ∧ 2 * hauntedCount D + D.NscStd = D.N := by
  classical
  set L : List (ℕ × ℕ) :=
    List.replicate 1000 (1, 0) ++ List.replicate 321 (1, 1) with hL
  have hne : ∀ x ∈ L, x.1 + 2 * x.2 ≠ 0 := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]; norm_num
    · rw [List.eq_of_mem_replicate hx]; norm_num
  have hp := chain_profile ha L hne
  rw [hL] at hp
  norm_num [List.map_append, List.map_replicate] at hp
  have hsum : ∀ f : ℕ × ℕ → ℤ,
      ((profile (chain a L)).map f).sum = 1000 * f (1, 0) + 321 * f (3, 2) := by
    intro f
    rw [hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate]
    simp [nsmul_eq_mul]
  have hN : (chain a L).N = 1963 := by
    rw [N_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, smul_eq_mul]
  have hOff : (chain a L).Noff = 642 := by
    rw [Noff_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, smul_eq_mul]
  have hSc : ((chain a L).NscStd : ℤ) = 1321 := by
    rw [NscStd_from_profile, hsum]; norm_num
  have hsc : ((chain a L).Nsc : ℤ) = 1000 := by
    rw [Nsc_from_profile, hsum]; norm_num
  have hSc' : (chain a L).NscStd = 1321 := by exact_mod_cast hSc
  have hsc' : (chain a L).Nsc = 1000 := by exact_mod_cast hsc
  have hHnt : hauntedCount (chain a L) = 321 := by
    have := NscStd_eq_Nsc_add_haunted (chain a L)
    omega
  exact ⟨chain a L, hN, hSc', hsc', hOff, hHnt,
    by rw [hOff, hN]; norm_num,
    by rw [hOff, hSc', hN],
    by rw [hHnt, hSc', hN]⟩

/-- **The blindness theorem as a literature-search oracle.**

A haunted ordinate of mass `3` and an on-line triple zero are the *same* `μ_T`
atom.  So any statement invariant under `μ_T` — every pair-correlation and
zero-repulsion result, which govern the spacing of *distinct* ordinates —
excludes both or neither.  Since no known repulsion result excludes triple
zeros, none can exclude haunting.

This is why `105`'s pattern-exclusion hypothesis cannot be found in that corpus:
not "we searched and did not find it", but **the corpus provably cannot contain
it**.  An impossibility theorem used to prune a reading queue rather than to
close a route. -/
theorem haunted_indistinguishable_from_triple {a : ℝ} :
    (configAt 0 1 1 a).ordinates = (configAt 0 3 0 a).ordinates :=
  config_ordinates_eq (by norm_num) a a

/-! ### The LI hierarchy, certified — and where `NoHaunted` sits in it

claude.ai supplies the chain `LI ⟹ all ordinates distinct ⟹ no haunting`, with
`NoHaunted` its weakest member.  Certifying it turns up a distinction the prose
form hides.

**Kill condition, filed first:** *if `NoHaunted` itself implies `N_off = 0`, it
is RH-in-window and worthless as a conditional hypothesis.*  It did not fire —
and the middle member of the chain **does** imply it. -/

/-- **Distinct ordinates ⟹ no haunting.**  A haunted ordinate carries mass
`≥ 3`. -/
theorem noHaunted_of_allDistinct (D : ZeroData) (h : ∀ γ, D.H γ ≤ 1) :
    ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 := by
  intro γ hsc
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  have := h γ
  omega

/-- **…but distinct ordinates already imply `N_off = 0`.**

The functional equation puts every off-line zero at the same height as its
partner, so an off-line zero forces mass `≥ 2`.  "All ordinates distinct" is
therefore at least as strong as RH-in-window — it *assumes the conclusion*. -/
theorem Noff_eq_zero_of_allDistinct (D : ZeroData) (h : ∀ γ, D.H γ ≤ 1) :
    D.Noff = 0 := by
  classical
  have hz : ∀ γ, offAt D γ = 0 := by
    intro γ
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    have := h γ
    omega
  have hoff : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [Noff_from_profile, profile, Multiset.map_map]; rfl
  rw [hoff]
  exact Finset.sum_eq_zero fun γ _ => hz γ

/-- **`NoHaunted` does not imply `N_off = 0`** — and this is what makes it the
only member of the chain worth conditioning on.

Witness: `configAt 0 0 1 a`, a lone off-line pair.  Its ordinate has `onAt = 0`,
so it is **unhaunted**; and `N_off = 2 > 0`.  So `NoHaunted` permits off-line
zeros — it forbids only their *coincidence with a lone critical zero*.

`LI` and "all ordinates distinct" both assume RH-in-window.  `NoHaunted` does
not.  It is not merely the weakest member of the chain; it is the only member
that is not already the conclusion. -/
theorem noHaunted_not_imp_Noff_zero {a : ℝ} (ha : a ≠ 1/2) :
    (∀ γ, (configAt 0 0 1 a).H γ - offAt (configAt 0 0 1 a) γ = 1 →
        (configAt 0 0 1 a).H γ = 1)
      ∧ (configAt 0 0 1 a).Noff ≠ 0 := by
  classical
  refine ⟨?_, ?_⟩
  · intro γ hsc
    have h1 := H_eq_onAt_add_offAt (configAt 0 0 1 a) γ
    have hon : onAt (configAt 0 0 1 a) γ = 0 := by
      by_cases hγ : γ = 0
      · subst hγ
        show Multiset.card (Multiset.filter (fun p => p.2 = 0 ∧ p.1 = 1/2)
            (Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
              + (Multiset.replicate 1 (a, (0:ℝ))
                + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))))) = 0
        have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
        rw [Multiset.filter_add, Multiset.filter_add,
          filter_replicate_neg (fun p : ℝ × ℝ => p.2 = 0 ∧ p.1 = 1/2) 1
            (a, (0:ℝ)) (fun h => ha h.2),
          filter_replicate_neg (fun p : ℝ × ℝ => p.2 = 0 ∧ p.1 = 1/2) 1
            ((1 - a : ℝ), (0:ℝ)) (fun h => ha' h.2)]
        simp
      · have : (configAt 0 0 1 a).H γ = 0 := by
          rw [ZeroData.H_eq_count, configAt_ordinates, Multiset.count_replicate,
            if_neg (by simpa using Ne.symm hγ)]
        omega
    omega
  · rw [configAt_Noff ha]
    norm_num

/-- **RH-in-window ⟹ no haunting.**  With no off-line zeros, a standard-simple
ordinate has `H = onAt = 1`.  The last link of the chain. -/
theorem noHaunted_of_Noff_zero (D : ZeroData) (h : D.Noff = 0) :
    ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 := by
  classical
  have hz : ∀ γ, offAt D γ = 0 := by
    intro γ
    have hle : offAt D γ ≤ D.Noff := by
      rw [offAt, ZeroData.Noff]
      refine Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)
      intro p hp
      exact hp.2
    omega
  intro γ hsc
  have := hz γ
  omega

/-- **The chain, complete and strict at its last link.**

> `LI` ⟹ all ordinates distinct ⟹ `N_off = 0` (RH-in-window) ⟹ `NoHaunted`,

with the final implication **strict**: a lone off-line pair is unhaunted with
`N_off = 2` (`noHaunted_not_imp_Noff_zero`).

So the project's conditional row is keyed to a hypothesis **strictly weaker than
RH restricted to the window** — every other member of the chain already contains
the conclusion. -/
theorem noHaunted_strictly_weaker_than_RH {a : ℝ} (ha : a ≠ 1/2) :
    (∀ D : ZeroData, D.Noff = 0 →
        ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1)
      ∧ ∃ D : ZeroData,
          (∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1) ∧ D.Noff ≠ 0 :=
  ⟨fun D h => noHaunted_of_Noff_zero D h,
   ⟨configAt 0 0 1 a, (noHaunted_not_imp_Noff_zero ha).1,
    (noHaunted_not_imp_Noff_zero ha).2⟩⟩

/-- **The ladder, in haunted-count form: `(m−1)·hauntedCount + NscStd ≤ N`.**

`110`'s canonical bound is the case `m = 3`.  With `109`'s identity this is
exactly `105`'s ladder rewritten, so the mass hypothesis and the density
instrument are the same statement — and the ladder's `δ` is `(1 − κ)/(m − 1)`,
not the vaguer expression `118`'s table carried. -/
theorem pred_mul_haunted_add_NscStd_le_N (D : ZeroData) (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ m ≤ D.H γ) :
    (m - 1) * hauntedCount D + D.NscStd ≤ D.N := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hid := NscStd_eq_Nsc_add_haunted D
  have h105 := mul_NscStd_le_N_add_pred_mul_Nsc D (k + 1) (by omega) h
  simp only [Nat.add_sub_cancel] at h105 ⊢
  have hexp : (k + 1) * D.NscStd
      = k * D.Nsc + k * hauntedCount D + D.NscStd := by
    rw [hid]; ring
  rw [hexp] at h105
  generalize k * D.Nsc = A at h105
  generalize k * hauntedCount D = B at h105 ⊢
  omega

/-- **The `N⊛` bound on the haunted count: `6·hauntedCount + N ≤ N⊛`.**

`Basic.six_mul_NscStd_le` read through `109`'s identity.  A haunted ordinate has
mass `≥ 3`, so it contributes `≥ 9` to `N⊛` and `3` to `N` — a surplus of `6`
each, which is exactly the `6` the `Basic` lemma carries.

This is the **third** certified upper bound on `hauntedCount`, beside
`2·hauntedCount ≤ N_off` (`083`) and `2·hauntedCount + NscStd ≤ N` (`110`), and
it is the one that consumes `(★)`. -/
theorem six_mul_haunted_add_N_le_Nstar (D : ZeroData) :
    6 * hauntedCount D + D.N ≤ D.Nstar := by
  have hid := NscStd_eq_Nsc_add_haunted D
  have h6 := ZeroData.six_mul_NscStd_le D
  omega

/-- **A fourth bound: `6·hauntedCount ≤ factMoment 3`.**

`123` said there were exactly three certified bounds on the haunted count.  There
is a fourth, from the third **factorial** moment `Σ H(H−1)(H−2)`: a haunted
ordinate has mass `≥ 3`, so it contributes `≥ 3·2·1 = 6`.

The `6` is the same `6` as in `six_mul_haunted_add_N_le_Nstar`, and for the same
reason — mass `3` is the cheapest haunted ordinate — but the two consume
different inputs, `N⊛` there and the third factorial moment here.

**Its ledger value is nil**, and that is worth stating: nothing certified bounds
`factMoment 3`, and `Optimal.moment_route_walled` shows no moment inequality of
order `≥ 3` can be made to bind.  So the fourth bound exists, is sharp at mass
`3`, and buys nothing — which is why `123` did not miss it by looking.

**`SESSION 143` — the "nothing bounds it" is now priced, not just stated.**
`Optimal.moment_route_walled` does not apply *here*: its two witnesses have
masses `≤ 2`, so their `factMoment 3` and `hauntedCount` are both zero, and it
walls prop1's LP rather than this inequality.  What actually stands between this
bound and the ledger is a **scale separation**, measured in
`forensics/w19_price.py`: a mass-`3` ordinate perturbs `∫S²` by exactly `2δL`,
a quantity with no `log log T`, while the certified S-moment asymptotics carry
`log log T` in their main term.  So an S-moment identity feeds this bound iff its
**error** term is `o(T)`.  That is a statement about the second-order term of
Fujii's expansion and is `[RECALL, UNVERIFIED]` — it carries no conclusion here.
-/
theorem six_mul_haunted_le_factMoment_three (D : ZeroData) :
    6 * hauntedCount D ≤ factMoment D 3 := by
  classical
  rw [hauntedCount, factMoment, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun γ _ => ?_
  by_cases h : D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1
  · rw [if_pos h]
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    have h3 : 3 ≤ D.H γ := by omega
    obtain ⟨t, ht⟩ : ∃ t, D.H γ = t + 3 := ⟨D.H γ - 3, by omega⟩
    rw [ht]
    simp [Nat.descFactorial]
    have hstep : 1 * (2 * 3) ≤ (t + 1) * ((t + 2) * (t + 3)) :=
      Nat.mul_le_mul (by omega)
        (Nat.mul_le_mul (by omega) (by omega))
    omega
  · rw [if_neg h]
    simp

/-! ### Counting the bounds was the wrong operation

`123` said three, `124` found a fourth.  The frame is wrong: bounds on
`hauntedCount` are *cheap*, and two more are one line each.  What matters is not
how many exist but which is sharpest on the certified inputs. -/

/-- `hauntedCount ≤ NscStd` — immediate from the identity, since `Nsc ≥ 0`. -/
theorem haunted_le_NscStd (D : ZeroData) : hauntedCount D ≤ D.NscStd := by
  have hid := NscStd_eq_Nsc_add_haunted D
  omega

/-- `3·hauntedCount ≤ N` — each haunted ordinate carries three zeros. -/
theorem three_mul_haunted_le_N (D : ZeroData) : 3 * hauntedCount D ≤ D.N := by
  have h := Nsc_add_three_mul_haunted_le_N D
  omega

/-- **Why one configuration keeps being extremal: it is the cheapest object that
haunts at all** — `SESSION 189`.

`178`–`180` and `188` found the haunted mass-`3` atom attaining **eight**
separate bounds, across the route table, the chain, and the `N_d` dictionary.
That is not a coincidence and it has a one-line reason.

`three_mul_haunted_le_N` says `3·hauntedCount ≤ N`.  So **any** configuration
with a haunted ordinate at all carries at least three zeros, and
`configAt 0 1 1 a` carries exactly three (`178`).  It is the minimum of the class,
and every bound the ledger owns that mentions `hauntedCount` is an inequality
between costs paid *per haunted ordinate* — so each is tight exactly where
haunting is cheapest, which is here.

The bounds not mentioning `hauntedCount` are tight here for the dual reason:
`NscStd = Nsc + hauntedCount` (`109`) turns every `NscStd` statement into a
haunted-count statement, and `Noff + NscStd ≤ N` is saturated when the ordinate's
whole mass is one critical zero plus its ghosts. -/
theorem minimal_haunted_configuration (D : ZeroData) (h : 1 ≤ hauntedCount D) :
    3 ≤ D.N :=
  le_trans (by omega) (three_mul_haunted_le_N D)

/-- …and the minimum is attained, by the configuration in question. -/
theorem minimal_haunted_attained {a : ℝ} (ha : a ≠ 1/2) :
    1 ≤ hauntedCount (configAt 0 1 1 a) ∧ (configAt 0 1 1 a).N = 3 := by
  obtain ⟨hN, -, -, -, -, hH, -⟩ := mass_three_atom_attains_all ha
  exact ⟨by omega, hN⟩

/-- **Both are strictly weaker than `110`'s, on the certified inputs.**

`three_mul_haunted_le_N` gives `δ ≤ 1/3 ≈ 0.3333`; `haunted_le_NscStd` gives no
numeric `δ` at all, because the baseline bounds `NscStd` from *below*.  `110`'s
`2·hauntedCount + NscStd ≤ N` gives `δ ≤ (1 − κ)/2 = 0.16375`, and `111` caps any
baseline-only argument there.

So the honest statement is not a count.  It is: **`0.16375` is the best `δ` the
certified inputs support, and no enumeration of bounds changes that** — a bound
is worth listing only when it is sharper on the inputs actually held.

✅ **Verified mechanically, `SESSION 190`, and the claim understates itself.**
Every inequality in `Riemann/*.lean` whose conclusion mentions `hauntedCount`
was enumerated (11) and evaluated on the certified inputs.  Nothing beats
`0.16375` — but **four** bounds *reach* it, through three different inputs:

| bound | via | `δ ≤` |
|---|---|---|
| `2·haunted + NscStd ≤ N` (`110`) | `NscStd/N ≥ 0.6725` | `0.16375` |
| `Nsc + 3·haunted ≤ N` | `Nsc/N ≥ 0.50875` | `0.16375` |
| `2·haunted + atomCount ≤ N` | `atomCount/N ≥ 0.6725` | `0.16375` |
| `(m−1)·haunted + NscStd ≤ N` at `m = 3` | `NscStd/N ≥ 0.6725` | `0.16375` |

Three of the remaining bounds give nothing (`6·haunted + N ≤ N⊛` and
`6·haunted ≤ factMoment 3` have no certified input; `haunted ≤ NscStd` bounds
`NscStd` from *below*), and `3·haunted ≤ N` gives the weaker `1/3`.

**The four agree because their inputs do.** In exact rationals
`1 − 0.50875 = 3 × 0.16375` and `1 − 0.6725 = 2 × 0.16375`, since `Nsc` and
`atomCount` are both minted from `κ` — `162`'s circularity, surfacing once more
as four independent-looking routes returning one number. -/
theorem best_delta_is_from_110 (D : ZeroData) :
    2 * hauntedCount D + D.NscStd ≤ D.N
      ∧ 3 * hauntedCount D ≤ D.N
      ∧ hauntedCount D ≤ D.NscStd :=
  ⟨two_mul_haunted_add_NscStd_le_N D, three_mul_haunted_le_N D,
   haunted_le_NscStd D⟩

/-- **`oddAtoms ≤ atomCount`** — the odd-mass ordinates are a subset of the
ordinates.  So a lower bound on `oddAtoms` implies one on `atomCount`, and
`130`'s two certified statements about `ζ` are not independent: the odd one
subsumes the other. -/
theorem oddAtoms_le_atomCount (D : ZeroData) : oddAtoms D ≤ atomCount D := by
  classical
  rw [oddAtoms, atomCount]
  exact Finset.card_filter_le _ _

/-- **The haunted count converts from the distinct-zeros deficit:
`2·hauntedCount + atomCount ≤ N`.**

`N − atomCount` is `N(T) − N_d(T)`, the **distinct-zeros deficit** — a named
quantity with its own literature (Cheer–Goldston and descendants).  A haunted
ordinate carries mass `≥ 3` and so contributes `≥ 2` to the deficit.

So any distinct-zeros proportion `atomCount ≥ c·N` gives
`hauntedCount ≤ (1−c)/2 · N`.  **And the project already holds such a
proportion:** `certified_atomCount` gives `c = 0.6725`, hence `δ = 0.16375` — the
same bound as `110`'s, by a route through a quantity the literature names. -/
theorem two_mul_haunted_add_atomCount_le_N (D : ZeroData) :
    2 * hauntedCount D + atomCount D ≤ D.N := by
  classical
  rw [hauntedCount, atomCount, Finset.card_filter, Finset.mul_sum,
    Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, N_eq_sum_H]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [ZeroData.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  by_cases h : D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1
  · rw [if_pos h]
    have h1 := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    omega
  · rw [if_neg h]
    omega

/-! ### The Landau excess, and why the genre's other members are location-shaped

`136` found that Aryan's `2/3` comes from an extension of the **Landau–Gonek**
formula — the object `landau` models.  `landau_discriminates` already says the
Landau weight separates configurations `μ_T` cannot.  This is the quantitative
form, and it explains the shape of the genre.

**Kill condition, filed first:** *if some off-line configuration has a smaller
Landau sum than the all-on-line one, the excess is not monotone and the
connection fails.*  It did not fire — AM–GM forbids it. -/

/-- **The Landau weight is minimised on the critical line:
`landau x D ≥ N·x^(1/2)` for `x > 0`.**

The functional equation pairs `β` with `1 − β`, so `2·landau = Σ (x^β + x^{1−β})`,
and `x^β · x^{1−β} = x` makes each summand at least `2√x` by AM–GM.

So **the excess `landau x D − N·x^(1/2)` is a non-negative measure of off-line
mass** — it is `0` exactly when every zero is on the line, and each off-line pair
contributes `2√x·(cosh((β−½)·log x) − 1)`.

**A reading, offered as such and not proved about anyone's paper:** the excess a
pair contributes vanishes as `β → 1/2`, so an off-line zero arbitrarily close to
the line is arbitrarily cheap in Landau weight.  A Landau-based route therefore
gets no purchase on the off-line count without a **horizontal separation
hypothesis**.  That *would* explain why the genre's location-shaped members
(BGST's narrow box) look the way they do — but the theorem here is the
inequality, and the explanation is a conjecture about other people's proofs that
I have not read. -/
theorem landau_ge_N_mul_sqrt {x : ℝ} (hx : 0 < x) (D : ZeroData) :
    (D.N : ℝ) * x ^ ((1:ℝ)/2) ≤ landau x D := by
  classical
  have hrefl : (D.Z.map fun p : ℝ × ℝ => x ^ (1 - p.1)).sum = landau x D := by
    conv_rhs => rw [landau, ← D.refl_inv]
    rw [Multiset.map_map]
    rfl
  have hpair : (D.Z.map fun p : ℝ × ℝ => x ^ p.1 + x ^ (1 - p.1)).sum
      = 2 * landau x D := by
    rw [Multiset.sum_map_add, hrefl, landau]
    ring
  have hlow : (D.Z.map fun _ : ℝ × ℝ => 2 * x ^ ((1:ℝ)/2)).sum
      ≤ (D.Z.map fun p : ℝ × ℝ => x ^ p.1 + x ^ (1 - p.1)).sum := by
    refine Multiset.sum_map_le_sum_map _ _ fun p _ => ?_
    have h1 : (0:ℝ) < x ^ p.1 := Real.rpow_pos_of_pos hx _
    have h2 : (0:ℝ) < x ^ (1 - p.1) := Real.rpow_pos_of_pos hx _
    have hprod : x ^ p.1 * x ^ (1 - p.1) = x := by
      rw [← Real.rpow_add hx]; norm_num
    have hs : x ^ ((1:ℝ)/2) * x ^ ((1:ℝ)/2) = x := by
      rw [← Real.rpow_add hx]; norm_num
    nlinarith [sq_nonneg (x ^ p.1 - x ^ (1 - p.1)),
      sq_nonneg (x ^ p.1 + x ^ (1 - p.1) - 2 * x ^ ((1:ℝ)/2)),
      Real.rpow_pos_of_pos hx ((1:ℝ)/2)]
  have hconst : (D.Z.map fun _ : ℝ × ℝ => 2 * x ^ ((1:ℝ)/2)).sum
      = (D.N : ℝ) * (2 * x ^ ((1:ℝ)/2)) := by
    rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    rfl
  rw [hconst, hpair] at hlow
  linarith

/-! ### Where `(★)` actually lives: between a proportion and a supremum

`no_starBound_from_proportionStd` (below) says a proportion of *simple* zeros
cannot bound `N⊛`.  This section supplies the other wall: a bound on the
**maximum** multiplicity does bound `N⊛` — but only uselessly.

**Kill condition, filed first:** *if a max-multiplicity bound gives a useful star
bound (`C < 2`), then `(★)` reduces to multiplicity control and the program's
route table is missing an entry.*  **It fired**: the constant it delivers is `M`
itself, and `M < 2` over the naturals means `M ≤ 1` — every zero simple, which is
the conclusion, not a hypothesis. -/

/-- **And `Nstar ≤ M·N` is attained, so the multiplicity bound has no slack** —
`SESSION 175`.

`169` proved `β = 1 − κ` optimal on the off-line channel, closing the question of
whether that constant was forced or habitual.  `170` then found a **second**
channel (`StarBound → Proportion (2 − C)`) that the off-line wall does not touch,
and `171` enumerated its producers.  The symmetric question was never asked of it.

`Nstar_le_of_multiplicity_le` below turns `H ≤ M` into `StarBound M`.  Equality
holds at a single ordinate of mass exactly `M`: every one of its `M` zeros sees
`H = M`, so `Nstar = M² = M·N`.  **No better `StarBound` follows from a
multiplicity bound alone.**

Combined with `171`'s arithmetic — `Proportion (2 − M)` beats the certified row
only at `M = 1` — this closes the multiplicity producer on the second channel:
its constant is optimal *and* its payout is empty above `M = 1`. -/
theorem Nstar_bound_attained (M : ℕ) (hM : 1 ≤ M) {a : ℝ} :
    (∀ γ, (configAt 0 M 0 a).H γ ≤ M)
      ∧ (configAt 0 M 0 a).Nstar = M * (configAt 0 M 0 a).N := by
  classical
  constructor
  · intro γ
    rw [configAt_H]
    split <;> omega
  · have hN : (configAt 0 M 0 a).N = M := by rw [configAt_N]; omega
    have hsum : (configAt 0 M 0 a).Nstar
        = ((configAt 0 M 0 a).Z.map fun _ : ℝ × ℝ => M).sum := by
      show ((configAt 0 M 0 a).Z.map fun p => (configAt 0 M 0 a).H p.2).sum = _
      congr 1
      refine Multiset.map_congr rfl ?_
      intro p hp
      have hp2 : p.2 = 0 := by
        have hmem : p.2 ∈ (configAt 0 M 0 a).ordinates :=
          Multiset.mem_map_of_mem _ hp
        rw [configAt_ordinates] at hmem
        exact Multiset.eq_of_mem_replicate hmem
      rw [hp2, configAt_H]
      simp
    rw [hsum, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
      Nat.mul_comm]
    rw [show Multiset.card (configAt 0 M 0 a).Z = (configAt 0 M 0 a).N from rfl, hN]

/-- **A supremum bound on multiplicity gives a star bound, at constant `M`.**
`N⊛ = Σ_ρ H(γ_ρ)`, so capping every `H` caps the sum term by term. -/
theorem Nstar_le_of_multiplicity_le (D : ZeroData) (M : ℕ)
    (h : ∀ γ, D.H γ ≤ M) : D.Nstar ≤ M * D.N := by
  classical
  have h1 : D.Nstar = (D.Z.map fun p => D.H p.2).sum := rfl
  have h2 : (D.Z.map fun p => D.H p.2).sum ≤ (D.Z.map fun _ => M).sum := by
    refine Multiset.sum_map_le_sum_map _ _ ?_
    intro p _
    exact h p.2
  have h3 : (D.Z.map fun _ : ℝ × ℝ => M).sum = M * D.N := by
    rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
    rfl
  omega

/-- **…and the constant is `M`, so the *bare* bound is useless for `prop1`.**
`prop1` needs `C < 2`; over the naturals `M < 2` forces `M ≤ 1`, i.e. every
ordinate carries at most one zero — which is what the program is trying to
*prove*.

⚠️ **Scope corrected at this location (SESSION 096).**  "Useless" is right about
the supremum *alone* and wrong about the supremum *plus a certified `Nsc` row*:
`Nstar_add_mul_Nsc_le` charges simple atoms `1` instead of `M`, giving
`C ≤ 1 + M(1 − κ)`, which is `< 2` already at `M = 2`.  See
`starBound_of_multiplicity_two`.

So `(★)`'s constant is not a supremum.  `Nstar_eq_sum_H_sq` says what it is:
`N⊛/N = Σ H² / Σ H`, the **size-biased mean multiplicity**.  That sits strictly
between the two walls — unreachable from a proportion of simple zeros
(`no_starBound_from_proportionStd`), and strictly weaker than a supremum bound. -/
theorem multiplicity_bound_useless (M : ℕ) (hM : M < 2) : M ≤ 1 := by omega

/-! ### What a `ProportionStd` does *not* buy: `N⊛` is unbounded

`090` turned the baseline around and read it as a zero-density statement.  The
same move applied to `N⊛` would hand the program its star bound for free, so it
is worth killing explicitly rather than leaving unasked.

**Kill condition, filed first:** *if `ProportionStd κ` also caps `N⊛`, the star
bound is free and everything else should stop.*  **It fired — the answer is no**,
and the witness is three lines of `chain`. -/

/-- **A high standard-simple proportion does not bound `N⊛`.**  For every `B`
there is a configuration with `4·NscStd = 3·N` — a standard-simple proportion of
`3/4`, comfortably above the `0.6725` baseline — and `N⊛ > B·N`.

The family: `3m` simple atoms beside a single atom of mass `m`.  The proportion
is `3/4` for every `m`, while `N⊛/N = (3 + m)/4` grows without bound.  **No
`ProportionStd` hypothesis, at any constant below `1`, yields a star bound.** -/
theorem no_starBound_from_proportionStd {a : ℝ} (ha : a ≠ 1/2) (B : ℕ) :
    ∃ D : ZeroData, 4 * D.NscStd = 3 * D.N ∧ B * D.N < D.Nstar := by
  classical
  set m := 4 * B + 4 with hm
  set L : List (ℕ × ℕ) := List.replicate (3 * m) (1, 0) ++ [(m, 0)] with hL
  have hm1 : m ≠ 1 := by omega
  have hne : ∀ p ∈ L, p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [hL, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.eq_of_mem_replicate hp]; norm_num
    · simp only [List.mem_singleton] at hp
      rw [hp]; omega
  have hp := chain_profile ha L hne
  rw [hL] at hp
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil] at hp
  have hN : (chain a L).N = 4 * m := by
    rw [N_from_profile, hp]; simp; try ring
  have hS : (chain a L).Nstar = 3 * m + m * m := by
    rw [Nstar_from_profile, hp]; simp; try ring
  have hSc : ((chain a L).NscStd : ℤ) = ((3 * m : ℕ) : ℤ) := by
    rw [NscStd_from_profile, hp]; simp [hm1]
  have hSc' : (chain a L).NscStd = 3 * m := by exact_mod_cast hSc
  refine ⟨chain a L, by rw [hSc', hN]; ring, ?_⟩
  rw [hN, hS]
  nlinarith [Nat.zero_le B, hm]

/-! #### The blindness is confined to *odd* crowded atoms

`gauge_orbit_size` counts the states; this locates which of them the invisible
row can even reach.  At an atom of mass `m = k + 2j`, `NscStd` counts the atom
exactly when its on-line part is `k = 1`.  For **even** `m` every state has `k`
even, so **no** state contributes — and `m`'s parity is `μ_T`-visible
(`config_parity`).

**Kill condition, stated before the section was written:** *if some even-mass
state contributed to `NscStd`, the localisation would fail and the blindness
would not be confined to odd atoms.*  It did not fire.

So the invisible row's ambiguity lives **only on odd atoms of mass `≥ 3`**:

* `m = 1` — one state, contributes `1`. Determined.
* `m` even — every state contributes `0`. **Determined, and determined by `μ_T`
  alone**, since parity is visible.
* `m` odd, `m ≥ 3` — exactly one of the `⌊m/2⌋ + 1` states contributes.
  **This is the whole shadow.** -/

lemma config_onAt (k j : ℕ) {a : ℝ} (ha : a ≠ 1/2) : onAt (config k j a) 0 = k := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  show Multiset.card (Multiset.filter (fun p => p.2 = 0 ∧ p.1 = 1/2)
      (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ))))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_pos (fun p : ℝ × ℝ => p.2 = 0 ∧ p.1 = 1/2) k ((1/2 : ℝ), (0:ℝ))
      ⟨rfl, rfl⟩,
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = 0 ∧ p.1 = 1/2) j (a, (0:ℝ))
      (fun h => ha h.2),
    filter_replicate_neg (fun p : ℝ × ℝ => p.2 = 0 ∧ p.1 = 1/2) j
      ((1 - a : ℝ), (0:ℝ)) (fun h => ha' h.2)]
  simp

/-- The `NscStd` contribution of a single fiber state: `1` exactly when its
on-line part is `1`. -/
theorem config_NscStd (k j : ℕ) {a : ℝ} (ha : a ≠ 1/2) :
    (config k j a).NscStd = if k = 1 then 1 else 0 := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  rw [NscStd_eq_onAt_functional]
  show Multiset.card (Multiset.filter (fun p => p.1 = 1/2 ∧ onAt (config k j a) p.2 = 1)
      (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ))))) = _
  rw [Multiset.filter_add, Multiset.filter_add,
    filter_replicate_neg (fun p : ℝ × ℝ => p.1 = 1/2 ∧ onAt (config k j a) p.2 = 1)
      j (a, (0:ℝ)) (fun h => ha h.1),
    filter_replicate_neg (fun p : ℝ × ℝ => p.1 = 1/2 ∧ onAt (config k j a) p.2 = 1)
      j ((1 - a : ℝ), (0:ℝ)) (fun h => ha' h.1)]
  by_cases hk : k = 1
  · rw [filter_replicate_pos (fun p : ℝ × ℝ => p.1 = 1/2 ∧ onAt (config k j a) p.2 = 1)
      k ((1/2 : ℝ), (0:ℝ)) ⟨rfl, by rw [config_onAt k j ha]; exact hk⟩, if_pos hk]
    simp [hk]
  · rw [filter_replicate_neg (fun p : ℝ × ℝ => p.1 = 1/2 ∧ onAt (config k j a) p.2 = 1)
      k ((1/2 : ℝ), (0:ℝ)) (by
        intro h
        exact hk (by rw [← config_onAt k j ha]; exact h.2)), if_neg hk]
    simp

/-- **`NscAny` on a single fiber state.**  `SESSION 196`.

`config k j a` has three distinct points when `a ≠ 1/2`: the on-line atom with
`k` copies and the two off-line atoms with `j` each.  A point is counted by
`NscAny` exactly when its own copy-count is one, so the on-line atom contributes
when `k = 1` and *each* off-line atom when `j = 1` — hence the `2 *`. -/
theorem config_NscAny (k j : ℕ) {a : ℝ} (ha : a ≠ 1/2) :
    (config k j a).NscAny
      = (if k = 1 then 1 else 0) + 2 * (if j = 1 then 1 else 0) := by
  classical
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  have hC : (a : ℝ) ≠ 1 - a := by intro h; exact ha (by linarith [h])
  -- `simp` normalises `1/2` to `2⁻¹` and does NOT normalise a `1/2`-shaped
  -- hypothesis handed to it, so the disequalities are restated in `2⁻¹` form
  -- before use.  `SESSION 188` learned this; `196` learned it again.
  have ha2 : a ≠ (2⁻¹ : ℝ) := fun h => ha (by rw [h]; norm_num)
  have ha2' : (1 - a : ℝ) ≠ (2⁻¹ : ℝ) := fun h => ha' (by rw [h]; norm_num)
  have hc0 : (config k j a).Z.count ((1/2 : ℝ), (0:ℝ)) = k := by
    show Multiset.count _ (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))) = k
    simp [Multiset.count_replicate, ha2, ha2']
  have hca : (config k j a).Z.count (a, (0:ℝ)) = j := by
    show Multiset.count _ (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))) = j
    simp [Multiset.count_replicate, Ne.symm ha2, Ne.symm hC]
  have hcb : (config k j a).Z.count ((1 - a : ℝ), (0:ℝ)) = j := by
    show Multiset.count _ (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ)))) = j
    simp [Multiset.count_replicate, Ne.symm ha2', hC]
  show Multiset.card (Multiset.filter (fun p => (config k j a).Z.count p = 1)
      (Multiset.replicate k ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate j (a, (0:ℝ))
          + Multiset.replicate j ((1 - a : ℝ), (0:ℝ))))) = _
  rw [Multiset.filter_add, Multiset.filter_add]
  by_cases hk : k = 1
  · rw [filter_replicate_pos (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
      k ((1/2 : ℝ), (0:ℝ)) (hc0.trans hk), if_pos hk]
    by_cases hj : j = 1
    · rw [filter_replicate_pos (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j (a, (0:ℝ)) (hca.trans hj),
        filter_replicate_pos (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j ((1 - a : ℝ), (0:ℝ)) (hcb.trans hj), if_pos hj]
      simp [hk, hj]
    · rw [filter_replicate_neg (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j (a, (0:ℝ)) (fun h => hj (hca.symm.trans h)),
        filter_replicate_neg (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j ((1 - a : ℝ), (0:ℝ)) (fun h => hj (hcb.symm.trans h)), if_neg hj]
      simp [hk]
  · rw [filter_replicate_neg (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
      k ((1/2 : ℝ), (0:ℝ)) (fun h => hk (hc0.symm.trans h)), if_neg hk]
    by_cases hj : j = 1
    · rw [filter_replicate_pos (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j (a, (0:ℝ)) (hca.trans hj),
        filter_replicate_pos (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j ((1 - a : ℝ), (0:ℝ)) (hcb.trans hj), if_pos hj]
      simp [hj]
    · rw [filter_replicate_neg (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j (a, (0:ℝ)) (fun h => hj (hca.symm.trans h)),
        filter_replicate_neg (fun p : ℝ × ℝ => (config k j a).Z.count p = 1)
        j ((1 - a : ℝ), (0:ℝ)) (fun h => hj (hcb.symm.trans h)), if_neg hj]
      simp

/-- **Both `NscAny` dictionary bounds are attained, and not degenerately.**
`SESSION 196`.

`Basic.lean` carries three inequalities relating `NscAny` to the ledger and none
of them had a witness.  At `config 1 1 a` — one on-line zero and one off-line
pair — `NscAny ≤ NscStd + Noff` and `NscAny ≤ N` are both *equalities*, with
`Noff` genuinely positive, so neither is attained only on the empty or all-on-
line configuration. -/
theorem nscAny_bounds_attained {a : ℝ} (ha : a ≠ 1/2) :
    (config 1 1 a).NscAny = (config 1 1 a).NscStd + (config 1 1 a).Noff
      ∧ (config 1 1 a).NscAny = (config 1 1 a).N
      ∧ 0 < (config 1 1 a).Noff := by
  rw [config_NscAny 1 1 ha, config_NscStd 1 1 ha, config_Noff ha, config_N]
  norm_num

/-- **`NscStd ≤ NscAny` is attained.**  `SESSION 196`.  On an all-on-line state
the two simplicity notions agree, so the forward dictionary entry is tight. -/
theorem nscStd_le_nscAny_attained {a : ℝ} (ha : a ≠ 1/2) :
    (config 1 0 a).NscStd = (config 1 0 a).NscAny := by
  rw [config_NscAny 1 0 ha, config_NscStd 1 0 ha]
  norm_num

/-- **…and all three are strict somewhere**, so none is an identity wearing an
inequality sign.  `SESSION 196`.

`config 0 1 a` is a lone off-line pair: two simple zeros, none on the line, so
`NscStd < NscAny`.  `config 0 2 a` is a doubled off-line pair: nothing is simple
at all, so `NscAny` falls strictly below both `NscStd + Noff` and `N`. -/
theorem nscAny_bounds_strict {a : ℝ} (ha : a ≠ 1/2) :
    (config 0 1 a).NscStd < (config 0 1 a).NscAny
      ∧ (config 0 2 a).NscAny < (config 0 2 a).NscStd + (config 0 2 a).Noff
      ∧ (config 0 2 a).NscAny < (config 0 2 a).N := by
  refine ⟨?_, ?_, ?_⟩
  · rw [config_NscAny 0 1 ha, config_NscStd 0 1 ha]; norm_num
  · rw [config_NscAny 0 2 ha, config_NscStd 0 2 ha, config_Noff ha]; norm_num
  · rw [config_NscAny 0 2 ha, config_N]; norm_num

/-- **The genre wall's arithmetic is tight, not lossy.**  `SESSION 197`.

`Basic.nscAny_import_transfer` says an import `NscAny ≥ κ·N` with `Noff ≤ c·N`
delivers `(κ − c)·N` to `NscStd`.  At `config 1 1 a` — one on-line zero, one
off-line pair — both hypotheses hold with `κ = 1` and `c = 2/3`, and the
conclusion is an **equality**: `(1 − 2/3)·3 = 1 = NscStd`.

So the loss in that transfer is the off-line mass itself and nothing else.  The
wall is not an artefact of a slack step. -/
theorem nscAny_import_transfer_attained {a : ℝ} (ha : a ≠ 1/2) :
    (1 : ℝ) * (config 1 1 a).N ≤ (config 1 1 a).NscAny
      ∧ ((config 1 1 a).Noff : ℝ) ≤ (2/3 : ℝ) * (config 1 1 a).N
      ∧ ((1 : ℝ) - 2/3) * (config 1 1 a).N = (config 1 1 a).NscStd := by
  rw [config_N, config_NscAny 1 1 ha, config_NscStd 1 1 ha, config_Noff ha]
  norm_num

/-- **`N⊛` on a pure on-line atom of mass `m`.**  `SESSION 204`.  Every one of
the `m` zeros sits at ordinate `0`, where `H = m`, so the sum is `m²`. -/
lemma config_Nstar_pure (m : ℕ) (a : ℝ) : (config m 0 a).Nstar = m * m := by
  classical
  have hH : ∀ γ' : ℝ, (config m 0 a).H γ' = if γ' = 0 then m else 0 := by
    intro γ'
    rw [config_eq_configAt, configAt_H]
    simp
  show ((config m 0 a).Z.map fun p => (config m 0 a).H p.2).sum = m * m
  have hZ : (config m 0 a).Z = Multiset.replicate m ((1/2 : ℝ), (0:ℝ)) := by
    show Multiset.replicate m ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 0 (a, (0:ℝ))
          + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))) = _
    simp
  rw [hZ, Multiset.map_replicate, hH, if_pos rfl, Multiset.sum_replicate]
  simp

/-- **`N_sc` on a pure on-line atom of mass `m`.**  `SESSION 204`.  The atom is
on the line, so the only question is whether its multiplicity is one. -/
lemma config_Nsc_pure (m : ℕ) (a : ℝ) :
    (config m 0 a).Nsc = if m = 1 then 1 else 0 := by
  classical
  have hH : (config m 0 a).H (0:ℝ) = m := by
    rw [config_eq_configAt, configAt_H]
    simp
  have hZ : (config m 0 a).Z = Multiset.replicate m ((1/2 : ℝ), (0:ℝ)) := by
    show Multiset.replicate m ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 0 (a, (0:ℝ))
          + Multiset.replicate 0 ((1 - a : ℝ), (0:ℝ))) = _
    simp
  show Multiset.card (Multiset.filter
      (fun p => p.1 = 1 / 2 ∧ (config m 0 a).H p.2 = 1) (config m 0 a).Z) = _
  rw [hZ]
  by_cases hm : m = 1
  · rw [filter_replicate_pos _ m ((1/2 : ℝ), (0:ℝ)) ⟨rfl, by rw [hH]; exact hm⟩,
      if_pos hm]
    simp [hm]
  · rw [filter_replicate_neg _ m ((1/2 : ℝ), (0:ℝ)) (by
      intro h; exact hm (by rw [← hH]; exact h.2)), if_neg hm]
    simp

/-- **`atomCount` *is* an ordinate functional**, and by definition rather than by
argument.  `SESSION 220`.  Stated so the contrast with
`NscAny_not_ordinate_functional` is a pair of theorems rather than a sentence. -/
theorem atomCount_ordinate_functional :
    ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, atomCount D = f D.ordinates :=
  ⟨fun m => m.toFinset.card, fun _ => rfl⟩

/-- **`NscAny` is not an ordinate functional.**  `SESSION 220`.

`219` observed that all three literature genres wall at the same three-zero
configuration.  They do not, however, live at the same layer of visibility.

`Blindness.thirdMoment_determined` puts the moments inside `μ_T`'s reach, and
`atomCount` is *defined* from `ordinates`, so the moment and distinct-zero
genres both bound quantities a `μ_T`-invariant theory can compute.  `NscAny`
does not: `config 3 0 a` and `config 1 1 a` share their ordinates — one atom of
mass three either way — and have `NscAny` equal to `0` and `3`.

So the simple-zero genre bounds something the certificate class cannot see,
which is why its wall (`197`, `214`, `218`) runs through the off-line import
rather than through the moment machinery.  Same wall, different reason for
being there.

This is the `NscAny` analogue of `Blindness.NscStd_not_ordinate_functional`. -/
theorem NscAny_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, D.NscAny = f D.ordinates := by
  rintro ⟨f, hf⟩
  have ha : (0:ℝ) ≠ 1/2 := by norm_num
  have hord : (config 3 0 (0:ℝ)).ordinates = (config 1 1 (0:ℝ)).ordinates :=
    config_ordinates_eq (by norm_num) 0 0
  have h1 := hf (config 3 0 (0:ℝ))
  have h2 := hf (config 1 1 (0:ℝ))
  rw [config_NscAny 3 0 ha] at h1
  rw [config_NscAny 1 1 ha] at h2
  rw [hord] at h1
  norm_num at h1 h2
  omega

/-- **…and on odd atoms of mass `≥ 3` it really is ambiguous** — the converse
half, so the localisation is witnessed in both directions.  Two states of the
same odd mass `m ≥ 3` share their ordinates and disagree on `NscStd`. -/
theorem odd_mass_NscStd_ambiguous (m : ℕ) (hm : m % 2 = 1) (h3 : 3 ≤ m)
    {a : ℝ} (ha : a ≠ 1/2) :
    (config m 0 a).ordinates = (config 1 ((m - 1) / 2) a).ordinates
      ∧ (config m 0 a).NscStd ≠ (config 1 ((m - 1) / 2) a).NscStd := by
  refine ⟨config_ordinates_eq (by omega) a a, ?_⟩
  rw [config_NscStd m 0 ha, config_NscStd 1 ((m - 1) / 2) ha,
    if_neg (by omega : m ≠ 1), if_pos rfl]
  omega

/-- **Even-mass atoms are determined, and determined by `μ_T` alone.**  Every
state over an even mass contributes `0` to `NscStd`, and parity is visible
(`config_parity`) — so the invisible row's ambiguity is confined to **odd**
atoms of mass `≥ 3`. -/
theorem even_mass_NscStd_zero (k j : ℕ) {a : ℝ} (ha : a ≠ 1/2)
    (hk : k ≠ 1) : (config k j a).NscStd = 0 := by
  rw [config_NscStd k j ha, if_neg hk]

end Blindness
end Riemann
