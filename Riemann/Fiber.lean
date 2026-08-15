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
`Blindness.no_muInvariant_theory_computes_NscStd`'s necessity.  The fiber
coordinate really is the whole residue: supply it and the target is determined;
withhold it and no `μ_T`-invariant theory can recover the target. -/
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

/-- **The residue is exactly the fiber coordinate.**  Two configurations
agreeing on `μ_T` and on the off-line mass at every ordinate have the same
`NscStd`.

With `Blindness.no_muInvariant_theory_computes_NscStd` this brackets `X` from
both sides: **withhold the fiber coordinate and no `μ_T`-invariant theory
recovers the target; supply it and the target is determined.**  Nothing beyond
`(μ_T, offAt)` is needed — which is what "the whole residue" means. -/
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

/-- **The exact obstruction: `Σm³ ≥ 3N⊛ − 2N`, for every configuration.**

Hence `C₃ ≥ 3C − 2` always, the three-moment LP's improvement term is never
positive, and the optimum stays at `prop1`'s `2 − C`.  No level-3 supplier can
move this route. -/
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

/-- **The certificate class computes an interval, not a point.**  Both endpoints
are functionals of `μ_T` alone, and `no_muInvariant_theory_computes_NscStd` says
nothing inside the interval is determined. -/
theorem NscStd_bracketed (D : ZeroData) : D.Nsc ≤ D.NscStd ∧ D.NscStd ≤ oddAtoms D :=
  ⟨ZeroData.Nsc_le_NscStd D, NscStd_le_oddAtoms D⟩

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
