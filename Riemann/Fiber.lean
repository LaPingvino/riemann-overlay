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

/-! ### The `1/2`-versus-`2⁻¹` normalisation — `SESSION 228`

`simp` normalises the literal `1/2` to `2⁻¹` in goals and does **not** normalise
a `1/2`-shaped hypothesis handed to it, so `ha : a ≠ 1/2` silently fails to fire.
`188`, `196` and `227` each lost a rebuild to this and each re-derived the same
two lines inline.

These are those lines, once. `offLine_ne_half` is the hypothesis in the form
`simp` will match; `offLine_ne_refl` is the companion every witness needs, since
an off-line abscissa differs from its own mirror. -/

/-- `a ≠ 1/2` restated in the form `simp` normalises to.  `SESSION 228`. -/
lemma offLine_ne_half {a : ℝ} (ha : a ≠ 1/2) : a ≠ (2⁻¹ : ℝ) :=
  fun h => ha (by rw [h]; norm_num)

/-- An off-line abscissa differs from its mirror.  `SESSION 228`. -/
lemma offLine_ne_refl {a : ℝ} (ha : a ≠ 1/2) : (a : ℝ) ≠ 1 - a :=
  fun h => ha (by linarith)

/-- The mirror of an off-line abscissa is off-line, in normalised form.
`SESSION 228`. -/
lemma offLine_mirror_ne_half {a : ℝ} (ha : a ≠ 1/2) : (1 - a : ℝ) ≠ (2⁻¹ : ℝ) :=
  fun h => ha (by rw [show a = 1 - (1 - a) by ring, h]; norm_num)

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

/-- **`oddAtoms` *is* an ordinate functional**, by definition.  `SESSION 229`.

The docstring below asserts that the right-hand side of `NscStd_le_oddAtoms` is
`μ_T`-visible, and it is — `oddAtoms` filters `ordinates.toFinset` on a
predicate in `H`, and `H` is `ordinates.count`.  `220` did this for `atomCount`
and the reason is the same: an assertion in a docstring is still an assertion,
and this one carries the whole point of the bracket.

*(`286`: and it is `μ_T`-visible for a sharper reason than the filter's syntax —
`oddAtoms_eq_odd_onAt` shows the off-line mass cannot affect it at all, by
parity at each ordinate.)*

With `224`'s map: `NscStd` sits at the middle level and is bracketed above by a
quantity at the top level.  That is what makes the bracket useful to a
certificate class rather than merely true. -/
theorem oddAtoms_ordinate_functional :
    ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, oddAtoms D = f D.ordinates :=
  ⟨fun m => (m.toFinset.filter fun γ => ¬ Even (m.count γ)).card, fun D => by
    classical
    rw [oddAtoms]
    congr 1
    exact Finset.filter_congr fun γ _ => by rw [D.H_eq_count γ]⟩

/-- **`oddAtoms` counts odd *on-line* multiplicity.**  `SESSION 286`.

`H = onAt + offAt` and `offAt` is always even (`even_offAt`), so `H` and `onAt`
have the same parity at every ordinate.  The definition filters on `¬ Even (H γ)`
and could equally filter on `¬ Even (onAt γ)`.

**So `oddAtoms` is an on-line quantity, not a mixed one.**  `229` established it
is `μ_T`-visible — a functional of the ordinate multiset — and that reading made
it look like a statistic about total mass.  It is not: the off-line part
contributes nothing to it, by parity, at every ordinate separately. -/
theorem oddAtoms_eq_odd_onAt (D : ZeroData) :
    oddAtoms D = (D.ordinates.toFinset.filter fun γ => ¬ Even (onAt D γ)).card := by
  classical
  rw [oddAtoms]
  congr 1
  refine Finset.filter_congr fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  constructor
  · intro hodd hev
    exact hodd (by rw [Nat.even_iff] at *; omega)
  · intro hodd hev
    exact hodd (by rw [Nat.even_iff] at *; omega)

/-- **An odd atom carries an on-line zero.**  `SESSION 286`.

Immediate from `oddAtoms_eq_odd_onAt`: odd means nonzero.  This is why
`NscStd_le_oddAtoms` can hold at all — both sides are counting ordinates that
have something on the critical line. -/
theorem onAt_pos_of_odd_H (D : ZeroData) (γ : ℝ) (h : ¬ Even (D.H γ)) :
    0 < onAt D γ := by
  have he := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  rcases Nat.eq_zero_or_pos (onAt D γ) with h0 | hp
  · exact absurd (by rw [Nat.even_iff]; omega) h
  · exact hp

/-- **`NscStd` counts ordinates with exactly one on-line zero.**  `SESSION 287`.

`H − offAt` *is* `onAt` (`H_eq_onAt_add_offAt`), so the `NscStd` filter is a
condition on the on-line count alone.  Like `oddAtoms` (`286`), this quantity
cannot see the off-line mass at all.

**So `286`'s finding was not a special case.**  There is a second level inside
`224`'s `μ_T`-visible class: quantities that read the total mass at an ordinate
(`N`, `N⊛`, `N_sc`, `atomCount`) and quantities that read only its on-line part
(`NscStd`, `oddAtoms`).  The map had one label where the mathematics has two. -/
theorem NscStd_eq_onAt_one (D : ZeroData) :
    D.NscStd = (D.ordinates.toFinset.filter fun γ => onAt D γ = 1).card := by
  classical
  have key : (D.NscStd : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset, (if onAt D γ = 1 then (1:ℤ) else 0) := by
    have hA : (D.NscStd : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ - offAt D γ = 1 then (1 : ℤ) else 0) := by
      rw [NscStd_from_profile, profile, Multiset.map_map]; rfl
    rw [hA]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h := H_eq_onAt_add_offAt D γ
    congr 1
    simp only [eq_iff_iff]
    omega
  have hc : ((D.ordinates.toFinset.filter fun γ => onAt D γ = 1).card : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset, (if onAt D γ = 1 then (1:ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  exact_mod_cast key.trans hc.symm

/-- **The bracket's upper half, as a subset.**  `SESSION 287`.

With `NscStd_eq_onAt_one` and `286`'s `oddAtoms_eq_odd_onAt` both sides count
ordinates by a condition on `onAt`, and `onAt = 1` implies `onAt` odd.  The
summation this replaces was written before either characterisation existed. -/
theorem NscStd_le_oddAtoms (D : ZeroData) : D.NscStd ≤ oddAtoms D := by
  classical
  rw [NscStd_eq_onAt_one, oddAtoms_eq_odd_onAt]
  refine Finset.card_le_card fun γ hγ => ?_
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, by rw [hγ.2]; decide⟩

/-- **The bracket's upper gap.**  `293` wrote this filter inline; `SESSION 313`
promotes it to a definition, because `R29` says the complement is where the
information is and an inline filter cannot be cited. -/
noncomputable def oddAbove (D : ZeroData) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => ¬ Even (onAt D γ) ∧ onAt D γ ≠ 1).card

/-- **The bracket's upper gap, named.**  `SESSION 293`.

`287` made `NscStd ≤ oddAtoms` a subset relation but left the difference
unnamed.  Both sides are filters on `onAt`, so the gap is the partition's other
part: ordinates whose on-line count is **odd and above one**.

With `288`'s `NscStd = N_sc + hauntedCount`, the bracket
`N_sc ≤ NscStd ≤ oddAtoms` now has both gaps written down —
`{onAt = 1, offAt ≠ 0}` below and `{onAt odd, onAt ≠ 1}` above — and neither is
slack in an estimate. -/
theorem oddAtoms_eq_NscStd_add_oddAbove (D : ZeroData) :
    oddAtoms D = D.NscStd + oddAbove D := by
  classical
  rw [oddAtoms_eq_odd_onAt, NscStd_eq_onAt_one, oddAbove]
  have hone : (D.ordinates.toFinset.filter fun γ => onAt D γ = 1)
      = (D.ordinates.toFinset.filter fun γ => ¬ Even (onAt D γ)).filter
          fun γ => onAt D γ = 1 := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun γ _ => ?_
    constructor
    · intro h; exact ⟨by rw [h]; decide, h⟩
    · intro h; exact h.2
  rw [hone, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not _).symm

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

**`339`: the slack is named further down.**  `onLineOrdinates_add_offLinePoints`
is the exact partition of `distinctZeros`, and the bound below is that identity
plus `offLinePoints_le_Noff`, with `point_slack_exact` giving the difference as an
identity.  Those sit further down rather than here because they need
`onLineOrdinates`, which is defined later (`R23`).

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

/-! #### The dictionary, priced — `SESSION 338`

`337` made half the vendored dependency reachable (`statement_index` went
`126 → 2345` reachable declarations), and the first thing to look for there was
an unconditional distinct-zeros proportion, which `PRICES.md` has carried as an
open one-cycle check.  It is there: `Zeta23.Final.thmC_cumulative` gives
`3/4` and `Zeta23.ThmD.thmD₀_dist_mult_cumulative` gives `GD 1 = 0.83625`, both
unconditional, both reachable today.

**They are in the wrong count, and the docstring above already said so** —
*"the dictionary runs the wrong way for us"*.  What is new here is the
quantitative half: how much a point-count proportion is worth after the only
conversion on disk. -/

/-- **What a distinct-*zero* proportion is worth for `atomCount`.**  Through
`distinctZeros_le_atomCount_add_Noff`, a point-count proportion `c` and an
off-line bound `k` give `c − k` for `atomCount` and no more. -/
theorem atomCount_of_distinctZeros_and_Noff (D : ZeroData) {c k : ℝ}
    (hd : c * (D.N : ℝ) ≤ (distinctZeros D : ℝ))
    (hoff : (D.Noff : ℝ) ≤ k * (D.N : ℝ)) :
    (c - k) * (D.N : ℝ) ≤ (atomCount D : ℝ) := by
  have h : (distinctZeros D : ℝ) ≤ (atomCount D : ℝ) + (D.Noff : ℝ) := by
    exact_mod_cast distinctZeros_le_atomCount_add_Noff D
  nlinarith [hd, hoff, h]

/-- **The margin is an identity.**  `Riemann.zeta23_GD_eq_of_HD` says
`GD lam = (1 + HD lam)/2`, so with `h = HD 1` the conversion above runs at
`c = (1+h)/2` against `k = 1 − h` — and `c − k` is `(3h−1)/2`, which is the
`Nsc` row's own formula, while the shortfall against `h` itself is exactly
`(1−h)/2`, the haunting bound.  Both by `ring`, so neither is a coincidence of
the decimals. -/
theorem distinct_route_margin (h : ℝ) :
    (1 + h) / 2 - (1 - h) = (3 * h - 1) / 2 ∧ h - (3 * h - 1) / 2 = (1 - h) / 2 :=
  ⟨by ring, by ring⟩

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

/-- **Under multiplicity `≤ 2` the star constant is exact:** `N⊛ + Nsc = 2·N`.
Per atom, `H² + [H = 1] = 2H` with `H ∈ {1, 2}` — an identity, not an estimate.
So `C = 2 − Nsc/N`, and `prop1`'s output `2 − C` is exactly `Nsc/N`.

`250`: the converse holds too — see `boundedMult_two_iff_star_exact`, which
makes this hypothesis and this equality the same condition. -/
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

/-- **Under multiplicity `≤ 2` the odd atoms are exactly the simple ones.**
`SESSION 251`.  Pure parity: every atom has `H ≥ 1`, so `H ≤ 2` leaves
`H ∈ {1, 2}`, and there `¬ Even H ↔ H = 1`.  No off-line hypothesis enters —
`Nsc`'s on-line clause is free, because `refl_inv` makes a lone zero its own
mirror. -/
theorem oddAtoms_eq_Nsc_of_mult_le_two (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    oddAtoms D = D.Nsc := by
  classical
  have key : (oddAtoms D : ℤ) = (D.Nsc : ℤ) := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    have hO : (oddAtoms D : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if ¬ Even (D.H γ) then (1 : ℤ) else 0) := by
      rw [oddAtoms, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun γ _ => by split <;> simp_all
    rw [hO, hB]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hpos : 0 < D.H γ := by
      rw [ZeroData.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 hγ
    have h2 := h γ
    have hpar : ¬ Even (D.H γ) ↔ D.H γ = 1 := by
      rw [Nat.even_iff]; omega
    by_cases hone : D.H γ = 1
    · rw [if_pos (hpar.2 hone), if_pos hone]
    · rw [if_neg (fun hc => hone (hpar.1 hc)), if_neg hone]
  exact_mod_cast key

/-- **`2·N ≤ N⊛ + N_sc`, with no hypothesis at all.**  `SESSION 250`.

Per atom `2H ≤ H² + [H = 1]`: at `H = 1` both sides are `2`, at `H = 2` both are
`4`, and from `H = 3` the square runs away.  This is the floor whose matching
ceiling is `Nstar_add_pred_mul_Nsc_le` at `M = 2`. -/
theorem two_mul_N_le_Nstar_add_Nsc (D : ZeroData) :
    2 * D.N ≤ D.Nstar + D.Nsc := by
  classical
  have key : 2 * (D.N : ℤ) ≤ (D.Nstar : ℤ) + D.Nsc := by
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
    refine Finset.sum_le_sum fun γ hγ => ?_
    have hpos : 0 < D.H γ := by
      rw [ZeroData.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 hγ
    by_cases hone : D.H γ = 1
    · rw [if_pos hone, hone]; norm_num
    · rw [if_neg hone]
      have hm : (2 : ℤ) ≤ (D.H γ : ℤ) := by
        have : 2 ≤ D.H γ := by omega
        exact_mod_cast this
      nlinarith
  exact_mod_cast key

/-- **Multiplicity `≤ 2` is exactly the equality class of the star bound.**
`SESSION 250`.

`097` proved `H ≤ 2 → N⊛ + N_sc = 2·N`.  With the unconditional floor
`two_mul_N_le_Nstar_add_Nsc` in hand the converse is available too, because a
single atom of mass `3` already makes the per-atom inequality strict
(`9 + 0 > 6`) and the other atoms only add slack.

So `C = 2 − κ` is not a bound the class happens to satisfy — the class **is**
the set on which `C = 2 − N_sc/N` holds with equality.  That is the shared
mechanism behind the three places `2 − c` has turned up: the star bound at
multiplicity two (`097`), its `prop1` image `2 − C = N_sc/N` (`242`), and the
turning point of the odd-atom class (`249`). -/
theorem boundedMult_two_iff_star_exact (D : ZeroData) :
    (∀ γ, D.H γ ≤ 2) ↔ D.Nstar + D.Nsc = 2 * D.N := by
  classical
  refine ⟨Nstar_add_Nsc_eq_two_mul_N D, fun heq γ₀ => ?_⟩
  by_contra hbig
  have hmem : γ₀ ∈ D.ordinates.toFinset := by
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, ← ZeroData.H_eq_count]
    omega
  have key : 2 * (D.N : ℤ) < (D.Nstar : ℤ) + D.Nsc := by
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
    refine Finset.sum_lt_sum (fun γ hγ => ?_) ⟨γ₀, hmem, ?_⟩
    · have hpos : 0 < D.H γ := by
        rw [ZeroData.H_eq_count, Multiset.count_pos]
        exact Multiset.mem_toFinset.1 hγ
      by_cases hone : D.H γ = 1
      · rw [if_pos hone, hone]; norm_num
      · rw [if_neg hone]
        have hm : (2 : ℤ) ≤ (D.H γ : ℤ) := by
          have : 2 ≤ D.H γ := by omega
          exact_mod_cast this
        nlinarith
    · have hone : ¬ D.H γ₀ = 1 := by omega
      rw [if_neg hone]
      have hm : (3 : ℤ) ≤ (D.H γ₀ : ℤ) := by
        have : 3 ≤ D.H γ₀ := by omega
        exact_mod_cast this
      nlinarith
  have : 2 * (D.N : ℤ) = (D.Nstar : ℤ) + D.Nsc := by exact_mod_cast heq.symm
  omega

/-- **`249`'s third appearance, as a theorem.**  `SESSION 251`.

`249` observed that the odd-atom class `oddAtoms ≥ c·N` turns at `2 − c`, and
`250` shipped that as a reading because the step from `oddAtoms` to `N_sc` was
checked by hand.  `oddAtoms_eq_Nsc_of_mult_le_two` supplies it, so on the
multiplicity-two class the star count is *exactly* `2·N − oddAtoms`, and a
hypothesis `oddAtoms ≥ c·N` gives `N⊛ ≤ (2 − c)·N` with nothing left over.

`oddAtoms` is `μ_T`-visible (`229`) and `N_sc` is too, so this is not a change
of level — it is the same currency under two names, which is `S102`'s shape a
second time. -/
theorem Nstar_add_oddAtoms_eq_two_mul_N (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    D.Nstar + oddAtoms D = 2 * D.N := by
  rw [oddAtoms_eq_Nsc_of_mult_le_two D h]
  exact Nstar_add_Nsc_eq_two_mul_N D h

/-- **The odd-atom equality characterises the class too.**  `SESSION 252`.

`251` gave one direction by routing through `N_sc`.  The converse does not
route back the same way — `oddAtoms` and `N_sc` are only equal *given* `H ≤ 2`,
which is what is being concluded — so it is proved directly: for `H ≥ 3`,
`H² + [H odd] ≥ 3H > 2H`, strict whatever the parity does.

So `oddAtoms` is not a weaker currency than `N_sc` for this purpose.  Both
equalities cut out the same class. -/
theorem boundedMult_two_iff_oddAtom_exact (D : ZeroData) :
    (∀ γ, D.H γ ≤ 2) ↔ D.Nstar + oddAtoms D = 2 * D.N := by
  classical
  refine ⟨Nstar_add_oddAtoms_eq_two_mul_N D, fun heq γ₀ => ?_⟩
  by_contra hbig
  have hmem : γ₀ ∈ D.ordinates.toFinset := by
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, ← ZeroData.H_eq_count]
    omega
  have key : 2 * (D.N : ℤ) < (D.Nstar : ℤ) + oddAtoms D := by
    have hO : (oddAtoms D : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if ¬ Even (D.H γ) then (1 : ℤ) else 0) := by
      rw [oddAtoms, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun γ _ => by split <;> simp_all
    have hN0 : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
      rw [N_from_profile, profile, Multiset.map_map]; rfl
    have hN : (D.N : ℤ) = ∑ γ ∈ D.ordinates.toFinset, (D.H γ : ℤ) := by
      rw [hN0, Nat.cast_sum]
    have hS : (D.Nstar : ℤ)
        = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℤ) * (D.H γ : ℤ)) := by
      rw [Nstar_eq_sum_H_sq D, Nat.cast_sum]; push_cast; rfl
    rw [hS, hO, hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_lt_sum (fun γ hγ => ?_) ⟨γ₀, hmem, ?_⟩
    · have hpos : 0 < D.H γ := by
        rw [ZeroData.H_eq_count, Multiset.count_pos]
        exact Multiset.mem_toFinset.1 hγ
      have hpar : ¬ Even (D.H γ) ↔ D.H γ % 2 = 1 := by rw [Nat.even_iff]; omega
      by_cases hone : D.H γ = 1
      · rw [if_pos (hpar.2 (by omega)), hone]; norm_num
      · have hm : (2 : ℤ) ≤ (D.H γ : ℤ) := by
          have : 2 ≤ D.H γ := by omega
          exact_mod_cast this
        have hite : (0 : ℤ) ≤ (if ¬ Even (D.H γ) then (1 : ℤ) else 0) := by
          split <;> norm_num
        nlinarith
    · have hm : (3 : ℤ) ≤ (D.H γ₀ : ℤ) := by
        have : 3 ≤ D.H γ₀ := by omega
        exact_mod_cast this
      have hite : (0 : ℤ) ≤ (if ¬ Even (D.H γ₀) then (1 : ℤ) else 0) := by
        split <;> norm_num
      nlinarith
  have : 2 * (D.N : ℤ) = (D.Nstar : ℤ) + oddAtoms D := by exact_mod_cast heq.symm
  omega

/-- **The sharp form at every `M`: `N⊛ + (M−1)·Nsc ≤ M·N`.**

`096` proved `N⊛ + M·Nsc ≤ (1 + M)·N`, which is loose by `N − Nsc`: it charges a
simple atom `1` and *also* keeps a spare `H`.  The tight linear-in-`H` estimate is

> per atom, `H² + (M − 1)·[H = 1] ≤ M·H`,

with **equality at `H = 1` and at `H = M`** — so the bound cannot be improved
within this shape.  *(`258`: both equality cases are on disk and this docstring
did not say where — `Nstar_bound_attained` for the `H = M` side,
`haunted_atom_saturates` for a certified instance at `M = 3`.)*  Dividing by `N`: `C ≤ M − (M − 1)·κ`, which is `< 2` exactly
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
give.  *(`257`: that last clause was an assertion in a docstring for seventy-six
cycles; it is now `noHaunted_no_starBound`, which exhibits an unhaunted
configuration of star ratio `m` for every `m`.)* -/
theorem noHaunted_of_mult_le_two (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 := by
  intro γ hsc
  have h1 := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  have := h γ
  omega

/-- **`H ≤ 2` gives `N_sc = NscStd`, as a corollary rather than a second proof.**

`SESSION 256`.  This carried its own twenty-line copy of
`Nsc_eq_NscStd_of_noHaunted`'s summation argument from `097` until a duplication
sweep found the two conclusions identical.  It is the composite of that theorem
with `noHaunted_of_mult_le_two`, and reads as one now. -/
theorem Nsc_eq_NscStd_of_mult_le_two (D : ZeroData) (h : ∀ γ, D.H γ ≤ 2) :
    D.Nsc = D.NscStd :=
  Nsc_eq_NscStd_of_noHaunted D (noHaunted_of_mult_le_two D h)

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

/-- **The threshold is exactly two: `H ≤ 3` does not give `NoHaunted`.**
`SESSION 260`.

`255` proved `H ≤ 2 → NoHaunted` and `noHaunted_not_mult_le_two` proved the
implication strict.  That leaves open how far up the cap can be relaxed, and the
answer is not at all: one step to `H ≤ 3` already admits a haunted ordinate.

`configAt 0 1 1 a` — one on-line zero and one mirror pair at the same ordinate —
has `H = 3` and `offAt = 2`, so `H − offAt = 1` with `H ≠ 1`, which is haunted by
definition.  `mass_three_atom_attains_all` is the fuller account of this
configuration; it is the object at which every route constant is tight.

So the implication `BoundedMult M → NoHaunted` holds at `M = 2` and fails at
every `M ≥ 3`, and it is `noSmallHaunted_three` that explains why there is
nothing in between: a haunted ordinate carries mass at least three, so capping
at two excludes them by arithmetic and capping at three admits the smallest one
exactly. -/
theorem noHaunted_fails_at_mult_three {a : ℝ} (ha : a ≠ 1/2) :
    (∀ γ, (configAt 0 1 1 a).H γ ≤ 3)
      ∧ ¬ (∀ γ, (configAt 0 1 1 a).H γ - offAt (configAt 0 1 1 a) γ = 1 →
              (configAt 0 1 1 a).H γ = 1) := by
  classical
  have hH0 : (configAt 0 1 1 a).H 0 = 3 := by
    simp only [configAt_H, if_true]
  have hO0 : offAt (configAt 0 1 1 a) 0 = 2 := by
    rw [offAt_configAt_self ha]
  refine ⟨fun γ => ?_, fun hcon => ?_⟩
  · by_cases hz : γ = 0
    · subst hz; omega
    · simp only [configAt_H, if_neg hz]; omega
  · have := hcon 0 (by omega)
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

/-- **A haunted ordinate carries mass at least three, pointwise.**  `SESSION 289`.

`Basic.three_le_H_of_haunted` says this about a *zero* — a point of `Z` with
`count = 1` on the line — because `Basic.lean` precedes `onAt` and `offAt` and
cannot speak about an ordinate's on-line part.  Here it is about the ordinate,
and the proof is arithmetic: the hypothesis gives `onAt = 1`, so `H = 1 + offAt`,
so `H ≠ 1` forces `offAt ≠ 0`, and `offAt` is even, hence at least two.

This is `noSmallHaunted_three`'s content — the ladder's free rung — with no
appeal to the zero-level statement. -/
theorem three_le_H_of_haunted_at (D : ZeroData) {γ : ℝ}
    (h : D.H γ - offAt D γ = 1) (h1 : D.H γ ≠ 1) : 3 ≤ D.H γ := by
  have hsum := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  omega

/-- **`N_sc` counts ordinates with one on-line zero and no off-line mass.**
`SESSION 292`.

`H = 1` forces `offAt = 0` — `offAt` is even and at most `H` — and then
`onAt = 1`; conversely those two give `H = 1`.  So `N_sc` joins `NscStd` (`287`)
and `hauntedCount` (`288`) in having a reading in the `(onAt, offAt)`
coordinates.

Together the three are a **partition**: `{onAt = 1}` splits by whether `offAt`
vanishes, which is `NscStd_eq_Nsc_add_haunted` below. -/
theorem Nsc_eq_onAt_one_offAt_zero (D : ZeroData) :
    D.Nsc = (D.ordinates.toFinset.filter fun γ => onAt D γ = 1 ∧ offAt D γ = 0).card := by
  classical
  have key : (D.Nsc : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset,
        (if onAt D γ = 1 ∧ offAt D γ = 0 then (1:ℤ) else 0) := by
    have hB : (D.Nsc : ℤ) = ∑ γ ∈ D.ordinates.toFinset,
        (if D.H γ = 1 then (1 : ℤ) else 0) := by
      rw [Nsc_from_profile, profile, Multiset.map_map]; rfl
    rw [hB]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    congr 1
    simp only [eq_iff_iff]
    omega
  have hc : ((D.ordinates.toFinset.filter
        fun γ => onAt D γ = 1 ∧ offAt D γ = 0).card : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset,
        (if onAt D γ = 1 ∧ offAt D γ = 0 then (1:ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  exact_mod_cast key.trans hc.symm

/-- **A haunted ordinate is a lone on-line zero with off-line mass beside it.**
`SESSION 288`.

`hauntedCount` filters on `H − offAt = 1 ∧ H ≠ 1`.  By
`H_eq_onAt_add_offAt` the first clause is `onAt = 1`, and given that, `H` is
`1 + offAt`, so the second is `offAt ≠ 0`.

**This is the `NscStd`/`N_sc` gap, named.**  `NscStd_eq_Nsc_add_haunted` says the
two counts differ by exactly `hauntedCount`; `287` placed `NscStd` among the
quantities that read only the on-line part and `N_sc` among those that read the
total mass.  The difference between them is therefore precisely the ordinates
where the on-line part is one and there is off-line mass to see — the gap is not
a slack in an inequality but the price of looking off the critical line. -/
theorem hauntedCount_eq_onAt_one_offAt_pos (D : ZeroData) :
    hauntedCount D
      = (D.ordinates.toFinset.filter fun γ => onAt D γ = 1 ∧ offAt D γ ≠ 0).card := by
  classical
  rw [hauntedCount]
  congr 1
  refine Finset.filter_congr fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  omega

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

/-! #### The same profile in `(onAt, offAt)` coordinates — `SESSION 294`

`profile` records `(mass, off-line mass)`; `292`/`293` read the ledger's counts
as filters on `(onAt, offAt)` instead.  Those are two vocabularies for the same
per-ordinate datum, and the project has been carrying both without writing the
translation down.

**Kill condition, filed first:** *if `NscStd` still needs truncated subtraction
after the change of coordinates — if its predicate cannot become `q.1 = 1` —
then the coordinate change buys nothing at the profile level and the identities
below are bookkeeping.*  It did not fire; `NscStd`, `N_sc` and `hauntedCount` all
lose the `q.1 - q.2`. -/

/-- The per-ordinate datum in `293`'s coordinates: `(on-line count, off-line
count)`. -/
noncomputable def onProfile (D : ZeroData) : Multiset (ℕ × ℕ) :=
  D.ordinates.toFinset.val.map fun γ => (onAt D γ, offAt D γ)

/-- Each is a map-image of the other, forwards… -/
theorem onProfile_eq_profile_map (D : ZeroData) :
    onProfile D = (profile D).map fun q => (q.1 - q.2, q.2) := by
  classical
  rw [onProfile, profile, Multiset.map_map]
  refine Multiset.map_congr rfl fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  simp only [Function.comp_apply]
  rw [h]; simp

/-- …and back.  The return trip uses `+`, so it needs no side condition. -/
theorem profile_eq_onProfile_map (D : ZeroData) :
    profile D = (onProfile D).map fun q => (q.1 + q.2, q.2) := by
  classical
  rw [onProfile, profile, Multiset.map_map]
  refine Multiset.map_congr rfl fun γ _ => ?_
  simp only [Function.comp_apply]
  rw [H_eq_onAt_add_offAt]

/-- `NscStd` in the new coordinates.  Compare `NscStd_from_profile`, whose
predicate is `q.1 - q.2 = 1`. -/
theorem NscStd_from_onProfile (D : ZeroData) :
    D.NscStd = Multiset.card ((onProfile D).filter fun q => q.1 = 1) := by
  classical
  rw [NscStd_eq_onAt_one, onProfile, Multiset.filter_map, Multiset.card_map]
  rfl

/-- `hauntedCount` in the new coordinates.  Compare `hauntedCount_from_profile`,
whose predicate is `q.1 - q.2 = 1 ∧ q.1 ≠ 1`. -/
theorem hauntedCount_from_onProfile (D : ZeroData) :
    hauntedCount D
      = Multiset.card ((onProfile D).filter fun q => q.1 = 1 ∧ q.2 ≠ 0) := by
  classical
  rw [hauntedCount_eq_onAt_one_offAt_pos, onProfile, Multiset.filter_map,
    Multiset.card_map]
  rfl

/-- `N_sc` in the new coordinates — the `hauntedCount` predicate with `q.2 = 0`
in place of `q.2 ≠ 0`, which is `288`'s partition read off the entry. -/
theorem Nsc_from_onProfile (D : ZeroData) :
    D.Nsc = Multiset.card ((onProfile D).filter fun q => q.1 = 1 ∧ q.2 = 0) := by
  classical
  rw [Nsc_eq_onAt_one_offAt_zero, onProfile, Multiset.filter_map,
    Multiset.card_map]
  rfl

/-! #### Where the two new quantities sit relative to the ledger — `SESSION 295`

`292`–`294` promoted `hauntedCount` and `oddAtoms` to first-class readings of the
per-ordinate entry. The five ledger counts each have an independence witness
already (`N_not_determined_by_ledger` and its four siblings, `217`); these two
had none.

**Kill condition, filed first:** *if `oddAtoms` is a functional of the five
ledger counts, then `293`'s bracket sits inside the ledger and its upper gap
carries nothing the ledger lacks.* It did not fire — but the search that
settled it is the content, and it is recorded in `SESSION 295`: nothing at five
atoms and total mass `≤ 12`, because `N⊛` pins `oddAtoms` modulo `4` and a
witness therefore needs a gap of at least `4`. -/

private lemma sq_mod_four (m : ℕ) : m * m % 4 = (if Even m then 0 else 1) := by
  have hlt : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have he : Even m ↔ m % 4 = 0 ∨ m % 4 = 2 := by
    rw [Nat.even_iff]
    have : m % 4 % 2 = m % 2 := Nat.mod_mod_of_dvd m (by norm_num)
    omega
  have hsq : m * m % 4 = (m % 4) * (m % 4) % 4 := by
    conv_lhs => rw [← Nat.mod_add_div m 4]
    ring_nf
    omega
  interval_cases h' : (m % 4) <;> simp_all

private lemma ms_mod_four (s : Multiset (ℕ × ℕ)) :
    ((s.map fun q => q.1 * q.1).sum) % 4
      = Multiset.card (s.filter fun q => ¬ Even q.1) % 4 := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
      by_cases h : ¬ Even q.1
      · rw [if_pos h]
        simp only [Multiset.card_add, Multiset.card_singleton]
        have : q.1 * q.1 % 4 = 1 := by rw [sq_mod_four]; simp [h]
        omega
      · rw [if_neg (by simpa using h)]
        simp only [zero_add]
        have : q.1 * q.1 % 4 = 0 := by rw [sq_mod_four]; simp at h; simp [h]
        omega

/-- **`N⊛` pins `oddAtoms` modulo `4`.**

An odd mass squares to `1` mod `4` and an even mass to `0`, so the atom-wise sum
`N⊛ = Σ m²` counts the odd atoms mod `4` and nothing else about them. This is
why a witness separating `oddAtoms` from the ledger has to be as large as it is:
the two sides must differ by a multiple of `4`. -/
theorem oddAtoms_mod_four (D : ZeroData) : D.Nstar % 4 = oddAtoms D % 4 := by
  rw [Nstar_from_profile, oddAtoms_from_profile, ms_mod_four]

/-- **`oddAtoms` is not.** The pin of `oddAtoms_mod_four` does not tighten below
`4`: five atoms of masses `6, 2, 2, 2, 2` against four of masses `5, 3, 3, 3`.
All on the line, so `N_off = 0` and `N_sc = NscStd = 0` on both sides; `N = 14`
and `N⊛ = 52` on both; `oddAtoms` is `0` against `4`.

`293`'s upper gap separates them too, since `NscStd` vanishes on both and
`oddAtoms = NscStd + oddAbove`. -/
theorem oddAtoms_not_determined_by_ledger {a : ℝ} (ha : a ≠ 1/2) :
    (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).N = (chain a [(5,0),(3,0),(3,0),(3,0)]).N
      ∧ (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).Nstar = (chain a [(5,0),(3,0),(3,0),(3,0)]).Nstar
      ∧ (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).Noff = (chain a [(5,0),(3,0),(3,0),(3,0)]).Noff
      ∧ (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).Nsc = (chain a [(5,0),(3,0),(3,0),(3,0)]).Nsc
      ∧ (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).NscStd = (chain a [(5,0),(3,0),(3,0),(3,0)]).NscStd
      ∧ oddAtoms (chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]) ≠ oddAtoms (chain a [(5,0),(3,0),(3,0),(3,0)]) := by
  have pA := chain_profile ha [(6,0),(2,0),(2,0),(2,0),(2,0)] (by decide)
  have pB := chain_profile ha [(5,0),(3,0),(3,0),(3,0)] (by decide)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide
  · have : ((chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).Nsc : ℤ) = ((chain a [(5,0),(3,0),(3,0),(3,0)]).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((chain a [(6,0),(2,0),(2,0),(2,0),(2,0)]).NscStd : ℤ) = ((chain a [(5,0),(3,0),(3,0),(3,0)]).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [oddAtoms_from_profile, oddAtoms_from_profile, pA, pB]; decide

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
    have h3 : offAt (configAt 0 0 2 a) 0 = 4 := by rw [offAt_configAt_self ha]
    have h4 : offAt (superpose (configAt 0 0 1 a) (configAt 0 0 1 b)) 0 = 4 := by
      rw [offAt_superpose, offAt_configAt_self ha, offAt_configAt_self hb]
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
  rw [NscStd_eq_onAt_one, Nsc_eq_onAt_one_offAt_zero,
    hauntedCount_eq_onAt_one_offAt_pos, ← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- **`hauntedCount` *is* a ledger functional** — immediately from `288`'s partition above,
the converse direction to `295`'s `oddAtoms_not_determined_by_ledger`; `NscStd = N_sc + hauntedCount`. Natural subtraction is safe in this
direction because `N_sc ≤ NscStd`. -/
theorem hauntedCount_eq_NscStd_sub_Nsc (D : ZeroData) :
    hauntedCount D = D.NscStd - D.Nsc := by
  rw [NscStd_eq_Nsc_add_haunted]; omega

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
      · rw [configAt_H, offAt_configAt_self ha]; simp
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
the line; `Noff` counts how *many* sit off it, and off-line is a
predicate rather than a distance: a zero at `β = 1/2 + 10⁻⁶/log T` counts once,
like one at `β = 0.9`.  For
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
carries one zero, a haunted one at least three, and they are disjoint.

**Collapsed at `SESSION 318`.**  This carried its own twenty-line sum estimate
over `ordinates.toFinset`, and `317`'s `forensics/equiv_check.py` put it in one
class with `three_mul_NscStd_le_N_add_two_mul_Nsc`, which runs the *same*
argument — its docstring states the same mechanism, that a haunted atom has mass
at least three while contributing one to each count.  Two proofs of one estimate,
which is `256`'s case to collapse rather than `256`'s case to keep: no route is
lost, because there was only ever one route. -/
theorem Nsc_add_three_mul_haunted_le_N (D : ZeroData) :
    D.Nsc + 3 * hauntedCount D ≤ D.N := by
  have h := three_mul_NscStd_le_N_add_two_mul_Nsc D
  have hid := NscStd_eq_Nsc_add_haunted D
  omega

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
`≥ 3`. 

**Dominated, `SESSION 265`.**  `H ≤ 1` reaches this conclusion through
`Noff_eq_zero_of_allDistinct` into `noHaunted_of_Noff_zero`, and also through
`le_trans` into `noHaunted_of_mult_le_two`; both composites typecheck against
this signature.  Kept as the statement in the vocabulary of distinctness. -/
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
not the vaguer expression `118`'s table carried.

**Superseded as a route, kept as a fact (`SESSION 263`).**  `Gaps`'s ladder no
longer consumes this: `263` found the off-line resource reproduces it exactly,
because `offLineImport_of_proportionStd` converts `ProportionStd κ` into an
off-line import at `β = 1 − κ`.  This remains the direct `N`-resource statement
and the shorter thing to cite when the off-line detour is not wanted. -/
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


/-- **The same ladder, paid for out of `N_off` instead of `N`.**  `SESSION 262`.

`pred_mul_haunted_add_NscStd_le_N` charges the rung against `N`.  This charges it
against the off-line count, which is a different resource and buys a different
hypothesis at the family level: a haunted ordinate has `offAt = H − 1`, and the
rung forces `H ≥ m`, so each one costs `m − 1` off-line zeros and they sit at
distinct ordinates.

At `m = 3` this is the `2·haunted ≤ N_off` that
`hauntedDensity_of_offLineImport` reaches indirectly through the coupling; above
`m = 3` it is sharper, and unlike the `N`-resource ladder it needs no
`ProportionStd`. -/
theorem pred_mul_haunted_le_Noff (D : ZeroData) (m : ℕ)
    (h : ∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1 ∨ m ≤ D.H γ) :
    (m - 1) * hauntedCount D ≤ D.Noff := by
  classical
  have hN : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [Noff_from_profile, profile, Multiset.map_map]; rfl
  set S := D.ordinates.toFinset.filter
    (fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1) with hS
  have hlow : ∀ γ ∈ S, m - 1 ≤ offAt D γ := by
    intro γ hγ
    rw [hS, Finset.mem_filter] at hγ
    obtain ⟨-, h1, h2⟩ := hγ
    rcases h γ h1 with hone | hbig
    · exact absurd hone h2
    · omega
  calc (m - 1) * hauntedCount D = ∑ _γ ∈ S, (m - 1) := by
        rw [hauntedCount, ← hS, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ γ ∈ S, offAt D γ := Finset.sum_le_sum hlow
    _ ≤ ∑ γ ∈ D.ordinates.toFinset, offAt D γ :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = D.Noff := hN.symm

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

/-! #### A quantity both vocabularies name — `SESSION 308`

`307` searched the vendored tree for our `oddAtoms` and found the dependency
tracks *simple* zeros and *all* zeros, never *odd* ones.  The mirror question is
what **they** name that we do not.  `Zeta23/Defs.lean:155` has
`N0star T₁ T₂ := (Z.window T₁ T₂ ∩ onLine).ncard` — the count of **distinct
on-line zeros**.  A zero on the line is determined by its ordinate, so that is
the number of ordinates carrying at least one on-line zero.

`onOrd` has been in this file since `SESSION 157`; the card of its support had no
name.  It does now, and it sits inside the bracket the rest of this section is
about.

**Kill condition, filed first:** *if a lower bound on this quantity supplies the
odd-atom route, then `307`'s "no supplier" is wrong and the correction is the
deliverable.*  **It resolves the other way, and that is worth writing down:**
`oddAtoms ≤ onLineOrdinates`, so bounding `onLineOrdinates` from below bounds
`oddAtoms` from below by nothing.  `N0star_lower_explicit` and its siblings in
`Zeta23.Assembly` are the wrong direction for `proportion_of_oddAtoms`, and the
next cycle to reach for them should stop here.

**Correction, `SESSION 309`.**  *"Bounds `oddAtoms` from below by nothing"* and
*"should stop here"* are too strong.  A lower bound on `onLineOrdinates` plus an
**upper** bound on the gap `evenOnAt` does bound `oddAtoms` below —
`onLineOrdinates = oddAtoms + evenOnAt` is a partition, not an inequality.  The
route is the right direction and fails on the arithmetic instead:
`evenOnAt_add_atomCount_le_N` gives `evenOnAt ≤ N − atomCount`, and with the
certified `atomCount ≥ 0.6725·N` the composite needs
`onLineOrdinates ≥ c₀·N` with `c₀ > 1` (`onLineOrdinates_route_threshold`),
while `onLineOrdinates ≤ N`.  Vacuous, not misdirected — and it becomes live if
the deficit bound improves. -/

/-- **The dependency's `N0star`, in our vocabulary**: ordinates carrying at least
one on-line zero. -/
noncomputable def onLineOrdinates (D : ZeroData) : ℕ := (onOrd D).toFinset.card

/-- Its support, spelled as a filter on the ordinates. -/
lemma onOrd_toFinset (D : ZeroData) :
    (onOrd D).toFinset = D.ordinates.toFinset.filter fun γ => onAt D γ ≠ 0 := by
  classical
  ext γ
  simp only [Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · intro h
    have hc : onAt D γ ≠ 0 := by
      rw [← count_onOrd]; simpa using (Multiset.count_pos.2 h).ne'
    refine ⟨?_, hc⟩
    rw [onOrd, Multiset.mem_map] at h
    obtain ⟨p, hp, rfl⟩ := h
    exact Multiset.mem_map_of_mem _ (Multiset.mem_of_mem_filter hp)
  · rintro ⟨-, hc⟩
    rw [← count_onOrd] at hc
    exact Multiset.count_pos.1 (Nat.pos_of_ne_zero hc)

/-- **An odd on-line count is a positive one** (`293`'s `onAt_pos_of_odd_H`
read as a cardinality), so the new quantity sits above `oddAtoms`. -/
theorem oddAtoms_le_onLineOrdinates (D : ZeroData) :
    oddAtoms D ≤ onLineOrdinates D := by
  classical
  rw [oddAtoms_eq_odd_onAt, onLineOrdinates]
  refine Finset.card_le_card fun γ hγ => ?_
  rw [Finset.mem_filter] at hγ
  rw [Multiset.mem_toFinset, ← Multiset.count_pos, count_onOrd]
  exact Nat.pos_of_ne_zero fun h => hγ.2 (by rw [h]; decide)

/-- …and below `atomCount`, since an ordinate with an on-line zero has a zero. -/
theorem onLineOrdinates_le_atomCount (D : ZeroData) :
    onLineOrdinates D ≤ atomCount D := by
  classical
  rw [onLineOrdinates, atomCount]
  refine Finset.card_le_card fun γ hγ => ?_
  rw [Multiset.mem_toFinset] at hγ
  rw [onOrd, Multiset.mem_map] at hγ
  obtain ⟨p, hp, rfl⟩ := hγ
  exact Multiset.mem_toFinset.2
    (Multiset.mem_map_of_mem _ (Multiset.mem_of_mem_filter hp))

/-! #### Why the on-line dictionary is an equality where the general one is not — `SESSION 339`

`338` priced the general dictionary and found it one-way: their `Ndist` is the
`ncard` of the zero *set*, ours is a count of *ordinates*, and
`atomCount_le_distinctZeros` runs the wrong way.  On the critical line that
asymmetry disappears, and the reason is trivial once said: a zero on the line is
`(1/2, γ)`, so its ordinate determines it.  Below, that as a theorem.

**Kill condition, filed first:** *if the bijection needs a hypothesis beyond
`ZeroData`'s own structure — if `refl_inv` or a distinctness assumption has to be
invoked — I report the obstruction rather than adding hypotheses until it works.*
It did not fire: the map is `Prod.snd` and injectivity is `Prod.ext` on the first
coordinate being `1/2` for both.

This is what makes the docstring below — *"their `N0star` is our `oddAtoms` plus
this gap"* — a statement about comparable quantities. **The bridge to
`Zeta23.N0star` itself is still unproved and is not assumed anywhere.** -/

/-- **`onLineOrdinates` is also a count of distinct on-line zeros.**  Counting
on-line ordinates and counting on-line points give the same number, because
`p ↦ p.2` is a bijection between them: a zero on the line is `(1/2, γ)`. -/
theorem onLineOrdinates_eq_onLinePoints (D : ZeroData) :
    onLineOrdinates D = (D.Z.toFinset.filter fun p => p.1 = 1/2).card := by
  classical
  rw [onLineOrdinates, onOrd_toFinset]
  refine (Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Multiset.mem_toFinset] at hp
    obtain ⟨hpZ, hp1⟩ := hp
    refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ?_, ?_⟩
    · exact Multiset.mem_map_of_mem _ hpZ
    · rw [onAt]
      have : p ∈ D.Z.filter fun q => q.2 = p.2 ∧ q.1 = 1/2 :=
        Multiset.mem_filter.2 ⟨hpZ, rfl, hp1⟩
      have := Multiset.card_pos_iff_exists_mem.2 ⟨p, this⟩
      omega
  · intro p hp q hq h
    simp only [Finset.mem_filter, Multiset.mem_toFinset] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · intro γ hγ
    simp only [Finset.mem_filter, Multiset.mem_toFinset] at hγ
    have hpos : 0 < Multiset.card (D.Z.filter fun q => q.2 = γ ∧ q.1 = 1/2) := by
      rw [onAt] at hγ; omega
    obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
    obtain ⟨hpZ, hp2, hp1⟩ := Multiset.mem_filter.1 hp
    exact ⟨p, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hpZ, hp1⟩, hp2⟩

/-- The complement: distinct zeros **off** the line.  `R29` — the bound above is
between two counts on one carrier, so the partition names what is left. -/
noncomputable def offLinePoints (D : ZeroData) : ℕ :=
  (D.Z.toFinset.filter fun p => ¬ (p.1 = 1/2)).card

/-- **The point count partitions as on-line ordinates plus off-line points**, an
equality.  This is the exact form of `distinctZeros_le_atomCount_add_Noff`: that
bound is this identity followed by `onLineOrdinates_le_atomCount` and
`offLinePoints_le_Noff`, and it names the slack those two inequalities spend. -/
theorem onLineOrdinates_add_offLinePoints (D : ZeroData) :
    onLineOrdinates D + offLinePoints D = distinctZeros D := by
  classical
  rw [onLineOrdinates_eq_onLinePoints, offLinePoints, distinctZeros]
  exact Finset.card_filter_add_card_filter_not _

/-- Off-line points are at most off-line zeros — `toFinset` can only lose. -/
theorem offLinePoints_le_Noff (D : ZeroData) : offLinePoints D ≤ D.Noff := by
  classical
  rw [offLinePoints, ZeroData.Noff, ← Multiset.toFinset_filter]
  exact Multiset.toFinset_card_le _

/-- **The gap between the two vocabularies**: ordinates whose on-line count is
even and positive.  `308`'s might-mean called this the quantity neither project
had bounded; `SESSION 309` bounds it. -/
noncomputable def evenOnAt (D : ZeroData) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => Even (onAt D γ) ∧ onAt D γ ≠ 0).card

/-- **And the two vocabularies partition.**  Their `N0star` is our `oddAtoms`
plus this gap — an equality, which is why `308`'s "wrong direction" was wrong.

**`339`: why the two are comparable at all.**  `onLineOrdinates_eq_onLinePoints`
above shows our on-line ordinate count *is* an on-line point count, which is the
kind of quantity their `N0star` is — and `338` shows the same does not hold off
the line.  The bridge from `onLineOrdinates` to `Zeta23.N0star` itself remains
unproved; this sentence compares vocabularies, not theorems. -/
theorem onLineOrdinates_eq_oddAtoms_add_evenOnAt (D : ZeroData) :
    onLineOrdinates D = oddAtoms D + evenOnAt D := by
  classical
  rw [onLineOrdinates, onOrd_toFinset, oddAtoms_eq_odd_onAt, evenOnAt]
  have e1 : (D.ordinates.toFinset.filter fun γ => ¬ Even (onAt D γ))
      = (D.ordinates.toFinset.filter fun γ => onAt D γ ≠ 0).filter
          fun γ => ¬ Even (onAt D γ) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun γ _ => ?_
    constructor
    · intro h; exact ⟨fun h0 => h (by rw [h0]; decide), h⟩
    · intro h; exact h.2
  have e2 : (D.ordinates.toFinset.filter fun γ => Even (onAt D γ) ∧ onAt D γ ≠ 0)
      = (D.ordinates.toFinset.filter fun γ => onAt D γ ≠ 0).filter
          fun γ => ¬ ¬ Even (onAt D γ) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun γ _ => ?_
    constructor
    · intro h; exact ⟨h.2, by simpa using h.1⟩
    · intro h; exact ⟨by simpa using h.2, h.1⟩
  rw [e1, e2]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- **The gap costs mass.**  An even positive on-line count is at least two, so
each such ordinate contributes at least one to the distinct-zeros deficit. -/
theorem evenOnAt_add_atomCount_le_N (D : ZeroData) :
    evenOnAt D + atomCount D ≤ D.N := by
  classical
  rw [evenOnAt, atomCount, N_eq_sum_H, Finset.card_filter,
    Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [D.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  by_cases h : Even (onAt D γ) ∧ onAt D γ ≠ 0
  · rw [if_pos h]
    have h2 : 2 ≤ onAt D γ := by obtain ⟨k, hk⟩ := h.1; omega
    have := H_eq_onAt_add_offAt D γ
    omega
  · rw [if_neg h]; omega

/-- `onLineOrdinates ≤ N`, from the same bound. -/
theorem onLineOrdinates_le_N (D : ZeroData) : onLineOrdinates D ≤ D.N := by
  have h1 := onLineOrdinates_le_atomCount D
  have h2 := evenOnAt_add_atomCount_le_N D
  omega

/-- `oddAbove` from the profile: `onAt` is `mass − off-line mass`. -/
theorem oddAbove_from_profile (D : ZeroData) :
    oddAbove D = Multiset.card ((profile D).filter
      fun q => ¬ Even (q.1 - q.2) ∧ q.1 - q.2 ≠ 1) := by
  classical
  rw [oddAbove, profile, Multiset.filter_map, Multiset.card_map]
  show Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
      = Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
  congr 1
  refine Multiset.filter_congr fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  simp only [Function.comp_apply]
  rw [show D.H γ - offAt D γ = onAt D γ by omega]

/-- `evenOnAt` from the profile, the same way. -/
theorem evenOnAt_from_profile (D : ZeroData) :
    evenOnAt D = Multiset.card ((profile D).filter
      fun q => Even (q.1 - q.2) ∧ q.1 - q.2 ≠ 0) := by
  classical
  rw [evenOnAt, profile, Multiset.filter_map, Multiset.card_map]
  show Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
      = Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
  congr 1
  refine Multiset.filter_congr fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  simp only [Function.comp_apply]
  rw [show D.H γ - offAt D γ = onAt D γ by omega]


/-! #### The last gap in the chain — `SESSION 310`

`309`'s snag was that an inequality between two counts of subsets of one set is
a partition with the complement thrown away.  Sweeping `Fiber.lean` for
count-vs-count bounds on the ordinate carrier, the chain

> `N_sc ≤ NscStd ≤ oddAtoms ≤ onLineOrdinates ≤ atomCount`

had three of its four gaps named — `hauntedCount` (`292`), the odd-above filter
(`293`, inline in `oddAtoms_eq_NscStd_add_oddAbove`), `evenOnAt` (`309`) — and
one not.

**Kill condition, filed first:** *if the sweep finds no unnamed gap, the pattern
is exhausted and I say so rather than manufacturing one.*  It found exactly one:
the ordinates with **no** on-line zero at all. -/

/-- **Ordinates every one of whose zeros is off the critical line.**  `RH` says
there are none; `offLineOnly_le_Noff` is the unconditional half of that. -/
noncomputable def offLineOnly (D : ZeroData) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => onAt D γ = 0).card

/-- **The chain's last partition.** -/
theorem onLineOrdinates_add_offLineOnly (D : ZeroData) :
    onLineOrdinates D + offLineOnly D = atomCount D := by
  classical
  rw [onLineOrdinates, onOrd_toFinset, offLineOnly, atomCount]
  have e : (D.ordinates.toFinset.filter fun γ => onAt D γ = 0)
      = D.ordinates.toFinset.filter fun γ => ¬ (onAt D γ ≠ 0) := by
    refine Finset.filter_congr fun γ _ => ?_
    simp
  rw [e]
  exact Finset.card_filter_add_card_filter_not _

/-- **The exact slack in `338`'s conversion.**  `SESSION 339`.

`distinctZeros ≤ atomCount + N_off` is one inequality wide, and this is the
identity underneath it: combining `onLineOrdinates_add_offLinePoints` with the
partition above, the two sides differ by naming *which* off-line count each uses
— `offLinePoints` on the point side, `offLineOnly` on the ordinate side.

So the only inequality the `338` bound spends is `offLinePoints_le_Noff`, and the
`offLineOnly` term is what the ordinate count keeps that the point count does not
see separately. -/
theorem point_slack_exact (D : ZeroData) :
    distinctZeros D + offLineOnly D = atomCount D + offLinePoints D := by
  have h := onLineOrdinates_add_offLinePoints D
  have h2 := onLineOrdinates_add_offLineOnly D
  omega

/-- **Each costs two off-line zeros.**  Such an ordinate has `onAt = 0`, so its
mass is `offAt`, which is even (`even_offAt`) and positive — hence at least two.
So `N_off = 0` forces `offLineOnly = 0`: with no off-line mass, every ordinate
carries an on-line zero. -/
theorem offLineOnly_le_Noff (D : ZeroData) : 2 * offLineOnly D ≤ D.Noff := by
  classical
  have hoff : D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
    rw [Noff_from_profile, profile, Multiset.map_map]; rfl
  rw [offLineOnly, hoff, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [D.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  by_cases h : onAt D γ = 0
  · rw [if_pos h]
    have hsum := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    omega
  · rw [if_neg h]; omega

/-! #### Which gaps `N_off = 0` closes — `SESSION 312`

`311`'s closing sentence read *"the whole distance between our vocabulary and
the literature's is priced in off-line mass."*  **It is not**, and this section
is the correction: two of the chain's four gaps vanish with `N_off`, and two
survive.

**Kill condition, filed first:** *if all four gaps vanish under `N_off = 0`,
`311`'s sentence is right and the deliverable is the theorem confirming it; if
some survive, the sentence is an overclaim and the correction is the
deliverable.*  **Two survive.** -/

/-- With no off-line mass, every ordinate carries an on-line zero. -/
theorem offLineOnly_eq_zero_of_Noff_zero (D : ZeroData) (h : D.Noff = 0) :
    offLineOnly D = 0 := by
  have := offLineOnly_le_Noff D; omega

/-- …and nothing is haunted, since a haunted ordinate needs off-line mass. -/
theorem hauntedCount_eq_zero_of_Noff_zero (D : ZeroData) (h : D.Noff = 0) :
    hauntedCount D = 0 := by
  have h1 := pred_mul_haunted_le_Noff D 3
    (fun γ hγ => (em (D.H γ = 1)).imp id (three_le_H_of_haunted_at D hγ))
  omega

/-- **But the `oddAtoms ≤ onLineOrdinates` gap survives `N_off = 0`.**

A **double zero on the critical line** has no off-line mass at all, is invisible
to `oddAtoms` (its `onAt` is even), and is counted by `onLineOrdinates`.  So the
distance between the two vocabularies is *not* priced in off-line mass — the part
priced that way is `offLineOnly` and `hauntedCount`; the rest is multiplicity on
the line, which `N_off` says nothing about. -/
theorem evenOnAt_survives_Noff_zero {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 2 0 a).Noff = 0 ∧ evenOnAt (configAt 0 2 0 a) = 1
      ∧ oddAtoms (configAt 0 2 0 a) = 0
      ∧ onLineOrdinates (configAt 0 2 0 a) = 1 := by
  classical
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 2) (j := 0) (by norm_num)
  norm_num at hp
  have he : evenOnAt (configAt 0 2 0 a) = 1 := by
    rw [evenOnAt_from_profile, hp]; decide
  have ho : oddAtoms (configAt 0 2 0 a) = 0 := by
    rw [oddAtoms_from_profile, hp]; decide
  have hl := onLineOrdinates_eq_oddAtoms_add_evenOnAt (configAt 0 2 0 a)
  exact ⟨by rw [configAt_Noff ha], he, ho, by omega⟩

/-- **And that is all of it.**  `SESSION 313`.

`312` showed two of the chain's four gaps survive `N_off = 0` and left them
unaccounted.  They account for exactly the ordinates that are not simple: with no
off-line mass, the simple ordinates plus `oddAbove` plus `evenOnAt` are every
ordinate there is.

**Kill condition, filed first:** *if the two surviving gaps sum to something
other than `atomCount − N_sc` — if a third contribution appears — the picture is
incomplete and I report the discrepancy.*  It did not fire; the proof is `omega`
over the four partitions and the two vanishing theorems, which is the chain
closing on itself.

So under `N_off = 0` the distance between `N_sc` and `atomCount` is the
multiple-zero count, and `309`'s wall — the distinct-zeros deficit — is not one
obstruction among several but the whole of what is left. -/
theorem Nsc_add_gaps_eq_atomCount_of_Noff_zero (D : ZeroData) (h : D.Noff = 0) :
    D.Nsc + oddAbove D + evenOnAt D = atomCount D := by
  have g1 := hauntedCount_eq_zero_of_Noff_zero D h
  have g2 := NscStd_eq_Nsc_add_haunted D
  have g3 := oddAtoms_eq_NscStd_add_oddAbove D
  have g4 := onLineOrdinates_eq_oddAtoms_add_evenOnAt D
  have g5 := onLineOrdinates_add_offLineOnly D
  have g6 := offLineOnly_eq_zero_of_Noff_zero D h
  omega

/-! #### The decomposition without the hypothesis — `SESSION 314`

`313` proved the sum under `N_off = 0` and stopped there.  The four partitions
it composes carry no hypothesis, so the same `omega` gives the unconditional
statement, and `313`'s is its corollary.  That is `R30`'s failure mode with the
polarity reversed: not a claim quantified past what was checked, but a claim
*restricted* below what was proved.

**Kill condition, filed first:** *if the five-way decomposition is already on
disk, this is a re-derivation and the deliverable is the pointer.*  Searched with
`statement_index --find 'atomCount'`, reading all twelve `ZeroData` rows.  It did
not fire. -/

/-- **Every ordinate is exactly one of five things.**

`N_sc` simple; `hauntedCount` one on-line zero with off-line company; `oddAbove`
an odd on-line count above one; `evenOnAt` an even positive one; `offLineOnly`
none at all. -/
theorem atomCount_decomposition (D : ZeroData) :
    D.Nsc + hauntedCount D + oddAbove D + evenOnAt D + offLineOnly D
      = atomCount D := by
  have g2 := NscStd_eq_Nsc_add_haunted D
  have g3 := oddAtoms_eq_NscStd_add_oddAbove D
  have g4 := onLineOrdinates_eq_oddAtoms_add_evenOnAt D
  have g5 := onLineOrdinates_add_offLineOnly D
  omega

/-- `offLineOnly` read off the profile: `onAt = 0` is `mass = off-line mass`. -/
theorem offLineOnly_from_profile (D : ZeroData) :
    offLineOnly D = Multiset.card ((profile D).filter fun q => q.1 = q.2) := by
  classical
  rw [offLineOnly, profile, Multiset.filter_map, Multiset.card_map]
  show Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
      = Multiset.card (Multiset.filter _ D.ordinates.toFinset.val)
  congr 1
  refine Multiset.filter_congr fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  simp only [Function.comp_apply]
  omega

/-! #### The dictionary completed — `SESSION 321`

Four of the five classes could already be read off the profile — `N_sc`,
`NscStd`, `hauntedCount`, `offLineOnly`.  `oddAbove` and `evenOnAt` could not,
which is why `314`'s five-class witness had to reach them through three
partitions instead of computing them.

**Kill condition, filed first:** *if the two readings do not make a witness
computation shorter — if a configuration's `oddAbove` still cannot be settled by
`decide` on its profile — the dictionary is decorative and I ship the readings
without the claim.*  It did not fire: `oddAbove_survives_Noff_zero` below is
`decide` on a one-entry profile. -/

/-- **`312`'s second surviving gap, exhibited.**

That cycle proved two of the chain's four gaps survive `N_off = 0` and showed a
witness for one of them.  This is the other: an ordinate of multiplicity three
with **all three zeros on the line** has no off-line mass, and `oddAbove` counts
it.  It is `305`'s separating configuration, reached here by `decide` on a
one-entry profile. -/
theorem oddAbove_survives_Noff_zero {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 3 0 a).Noff = 0 ∧ oddAbove (configAt 0 3 0 a) = 1
      ∧ evenOnAt (configAt 0 3 0 a) = 0 := by
  classical
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 3) (j := 0) (by norm_num)
  norm_num at hp
  refine ⟨by rw [configAt_Noff ha], ?_, ?_⟩
  · rw [oddAbove_from_profile, hp]; decide
  · rw [evenOnAt_from_profile, hp]; decide

/-- **No part of the decomposition is redundant** — one configuration puts a
single ordinate in each of the five classes at once. -/
theorem atomCount_decomposition_all_inhabited {a : ℝ} (ha : a ≠ 1/2) :
    let L : List (ℕ × ℕ) := [(1,0),(1,1),(3,0),(2,0),(0,1)]
    (chain a L).Nsc = 1 ∧ hauntedCount (chain a L) = 1 ∧ oddAbove (chain a L) = 1
      ∧ evenOnAt (chain a L) = 1 ∧ offLineOnly (chain a L) = 1
      ∧ atomCount (chain a L) = 5 := by
  classical
  intro L
  have hp := chain_profile ha L (by decide)
  norm_num [L] at hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : ((chain a L).Nsc : ℤ) = 1 := by rw [Nsc_from_profile, hp]; decide
    exact_mod_cast this
  · rw [hauntedCount_from_profile, hp]; decide
  · rw [oddAbove_from_profile, hp]; decide
  · rw [evenOnAt_from_profile, hp]; decide
  · rw [offLineOnly_from_profile, hp]; decide
  · rw [atomCount_eq_card_profile, hp]; decide

/-! #### The general moment — `SESSION 331`

`330`'s snag: two nearly identical fifty-line proofs, `329`'s at `N⊛` and `330`'s
at the third moment, differing in four constants.  Its docstring named the
missing piece — `Hᵏ − H ≥ mᵏ − m` for `H ≥ m ≥ 1` — and declined to write it.

**Kill condition, filed first:** *if the general-`k` lemma cannot be proved
without more machinery than the two copies it replaces — if it costs more lines
than the hundred it saves — the copies stay and I report the cost.*  It did not
fire: the excess lemma is thirteen lines, and both earlier theorems become
two-line corollaries.

The excess lemma's shape is what made it cheap.  Write `H = m + d` and factor
`H^(j+1) = H^j·m + H^j·d`; then `m^(j+1) ≤ H^j·m` and `d ≤ H^j·d` because
`H^j ≥ 1`, and `omega` closes it.  No induction, no subtraction. -/


-- H^k - H >= m^k - m for 1 <= m <= H, k >= 1, written without subtraction.
private lemma pow_excess_mono {m H k : ℕ} (hm : 1 ≤ m) (h : m ≤ H) (hk : 1 ≤ k) :
    m ^ k + H ≤ H ^ k + m := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, H = m + d := ⟨H - m, by omega⟩
  have hH : 1 ≤ m + d := by omega
  have hP : 1 ≤ (m + d) ^ j := Nat.one_le_pow _ _ hH
  have h1 : m ^ (j + 1) ≤ (m + d) ^ j * m := by
    rw [pow_succ]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) j) le_rfl
  have h2 : (m + d) ^ (j + 1) = (m + d) ^ j * m + (m + d) ^ j * d := by
    rw [pow_succ]; ring
  have h3 : d ≤ (m + d) ^ j * d := Nat.le_mul_of_pos_left d (by omega)
  omega

private lemma moment_weight (n f k : ℕ) (hf : f % 2 = 0) (hpos : 0 < n + f)
    (hk : 1 ≤ k) :
    (3 ^ k - 3) * (if n = 1 ∧ f ≠ 0 then 1 else 0)
      + (3 ^ k - 3) * (if ¬ Even n ∧ n ≠ 1 then 1 else 0)
      + (2 ^ k - 2) * (if Even n ∧ n ≠ 0 then 1 else 0)
      + (2 ^ k - 2) * (if n = 0 then 1 else 0)
      + (n + f) ≤ (n + f) ^ k := by
  have h2le : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have h3le : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have hkey := pow_excess_mono (m := 2) (H := 0 + f) (k := k) (by omega) (by omega) hk
    rw [if_neg (by omega : ¬ ((0:ℕ) = 1 ∧ f ≠ 0)),
      if_neg (by simp : ¬ (¬ Even 0 ∧ (0:ℕ) ≠ 1)),
      if_neg (by simp : ¬ (Even 0 ∧ (0:ℕ) ≠ 0)), if_pos rfl]
    omega
  · rcases eq_or_ne n 1 with h1 | h1
    · subst h1
      rcases eq_or_ne f 0 with hz | hz
      · subst hz
        rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp)]
        simp
      · have hkey := pow_excess_mono (m := 3) (H := 1 + f) (k := k) (by omega) (by omega) hk
        rw [if_pos ⟨rfl, hz⟩, if_neg (by simp), if_neg (by simp), if_neg (by simp)]
        omega
    · have h2 : 2 ≤ n := by omega
      by_cases he : Even n
      · have hkey := pow_excess_mono (m := 2) (H := n + f) (k := k) (by omega) (by omega) hk
        rw [if_neg (by tauto : ¬ (n = 1 ∧ f ≠ 0)),
          if_neg (by tauto : ¬ (¬ Even n ∧ n ≠ 1)),
          if_pos ⟨he, by omega⟩, if_neg (by omega : ¬ n = 0)]
        omega
      · have h3 : 3 ≤ n := by
          rcases Nat.lt_or_ge n 3 with h | h
          · exfalso; interval_cases n; simp_all
          · exact h
        have hkey := pow_excess_mono (m := 3) (H := n + f) (k := k) (by omega) (by omega) hk
        rw [if_neg (by tauto : ¬ (n = 1 ∧ f ≠ 0)), if_pos ⟨he, h1⟩,
          if_neg (by tauto : ¬ (Even n ∧ n ≠ 0)), if_neg (by omega : ¬ n = 0)]
        omega

theorem momentK_charges_every_class (D : Riemann.ZeroData) {k : ℕ} (hk : 1 ≤ k) :
    (3 ^ k - 3) * hauntedCount D + (3 ^ k - 3) * oddAbove D
      + (2 ^ k - 2) * evenOnAt D + (2 ^ k - 2) * offLineOnly D
      + D.N ≤ momentK D k := by
  classical
  rw [hauntedCount_eq_onAt_one_offAt_pos, oddAbove, evenOnAt, offLineOnly,
    N_eq_sum_H, momentK, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [D.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  have hsum := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  have := moment_weight (onAt D γ) (offAt D γ) k (by omega) (by omega) hk
  rw [← hsum] at this
  convert this using 3

/-- `momentK` at `2` is `N⊛`. -/
lemma momentK_two (D : ZeroData) : momentK D 2 = D.Nstar := by
  rw [momentK, Nstar_eq_sum_H_sq]
  exact Finset.sum_congr rfl fun γ _ => by ring

/-- `momentK` at `3` is the third moment. -/
lemma momentK_three (D : ZeroData) : momentK D 3 = thirdMoment D := by
  rw [momentK, thirdMoment]
  exact Finset.sum_congr rfl fun γ _ => by ring

/-- **Every class charged its minimum mass in the `N⊛` currency**, now a
corollary of `momentK_charges_every_class` at `k = 2`.  `329` proved it directly
in fifty lines. -/
theorem star_charges_every_class (D : ZeroData) :
    6 * hauntedCount D + 6 * oddAbove D + 2 * evenOnAt D + 2 * offLineOnly D
      + D.N ≤ D.Nstar := by
  have h := momentK_charges_every_class D (k := 2) (by omega)
  rw [momentK_two] at h
  norm_num at h
  exact h

/-- **The same at the third moment**, a corollary at `k = 3`.  `330` proved it
directly, and `331`'s snag is that the two proofs differed in four constants. -/
theorem thirdMoment_charges_every_class (D : ZeroData) :
    24 * hauntedCount D + 24 * oddAbove D + 6 * evenOnAt D + 6 * offLineOnly D
      + D.N ≤ thirdMoment D := by
  have h := momentK_charges_every_class D (k := 3) (by omega)
  rw [momentK_three] at h
  norm_num at h
  exact h

/-- **The two weight vectors are not parallel**, so the third moment is a
different constraint rather than a rescaling of `N⊛`'s. -/
theorem third_moment_weights_not_parallel : 24 * 2 ≠ 6 * 6 := by decide

/-! #### Which configurations saturate the whole family — `SESSION 333`

`332` showed the charge is an equality at every `k` on one configuration, and gave
the reason: its five ordinates sit exactly at their class minima.  That reason
does not mention the configuration, so it should hold of a class of them.

**Kill condition, filed first:** *if the equality condition differs between two
moments — if some configuration is tight at `k = 2` and slack at `k = 3` — then
the family's members have different equality sets and the characterisation is
per-`k`.*  **It did not fire**, and the condition turns out to be one the project
already names: **mass at most three at every ordinate.**

Why the classes line up with it: at `H = 1` the ordinate is `N_sc` and its weight
is `0`; at `H = 2` the on-line count is `0` or `2`, so the class is `offLineOnly`
or `evenOnAt` and the minimum is `2`; at `H = 3` it is `1` or `3`, so `hauntedCount`
or `oddAbove` and the minimum is `3`.  Mass at most three **is** sitting at the
class minimum, for every class at once, and the `k` never enters. -/

/-- The pointwise equality, under mass at most three.  With `f` even and
`n + f ≤ 3` there are five cases and `interval_cases` takes them. -/
private lemma moment_weight_eq (n f k : ℕ) (hf : f % 2 = 0) (hpos : 0 < n + f)
    (hk : 1 ≤ k) (h3 : n + f ≤ 3) :
    (3 ^ k - 3) * (if n = 1 ∧ f ≠ 0 then 1 else 0)
      + (3 ^ k - 3) * (if ¬ Even n ∧ n ≠ 1 then 1 else 0)
      + (2 ^ k - 2) * (if Even n ∧ n ≠ 0 then 1 else 0)
      + (2 ^ k - 2) * (if n = 0 then 1 else 0)
      + (n + f) = (n + f) ^ k := by
  have h2le : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have h3le : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
  have hn : n ≤ 3 := by omega
  have hfb : f ≤ 3 := by omega
  interval_cases n <;> interval_cases f <;>
    (simp_all [Nat.even_iff]; try omega)

/-- **Mass at most three saturates every moment at once.**  `SESSION 333`.

`332`'s configuration is one instance; this is the class.  The condition does not
depend on `k`, so a single hypothesis makes the whole countable family of `331`
an equality.

**The converse is proved at `334`** — `momentK_charges_eq_iff`, for `k ≥ 2`.
`333` wrote here that it would want a strict variant of `pow_excess_mono` and an
argument off `Finset.sum_eq_sum_iff_of_le`; the strict variant was needed and that
`Finset` lemma was not, since `Finset.sum_lt_sum` does the sum step directly. -/
theorem momentK_charges_eq_of_mult_le_three (D : ZeroData) {k : ℕ} (hk : 1 ≤ k)
    (h3 : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ 3) :
    (3 ^ k - 3) * hauntedCount D + (3 ^ k - 3) * oddAbove D
      + (2 ^ k - 2) * evenOnAt D + (2 ^ k - 2) * offLineOnly D
      + D.N = momentK D k := by
  classical
  rw [hauntedCount_eq_onAt_one_offAt_pos, oddAbove, evenOnAt, offLineOnly,
    N_eq_sum_H, momentK, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [D.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  have hsum := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  have hb := h3 γ hγ
  have := moment_weight_eq (onAt D γ) (offAt D γ) k (by omega) (by omega) hk
    (by omega)
  rw [← hsum] at this
  convert this using 3

/-! #### The converse, which `333` left open — `SESSION 334`

`333` proved mass at most three saturates every moment and recorded what the
converse needed: a **strict** form of `331`'s excess lemma, plus a pointwise
argument.  Both are below.

**Kill condition, filed first:** *if the strict lemma or the pointwise step needs
more than the non-strict version did — if the sum step will not factor through a
per-ordinate strict inequality — I report the obstruction rather than the
theorem.*  It did not fire.  `pow_excess_strict` is the same `H = m + d`
factorisation with `d ≥ 1` and `H^j ≥ 2`, and `Finset.sum_lt_sum` takes the sum
step directly, so `Finset.sum_eq_sum_iff_of_le` — which `333` guessed at — was not
needed at all. -/


private lemma pow_excess_strict {m H k : ℕ} (hm : 1 ≤ m) (h : m < H) (hk : 2 ≤ k) :
    m ^ k + H < H ^ k + m := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, H = m + d := ⟨H - m, by omega⟩
  have hd : 1 ≤ d := by omega
  have hH2 : 2 ≤ m + d := by omega
  have hj : 1 ≤ j := by omega
  have hP : 2 ≤ (m + d) ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ (m + d) ^ 1 := Nat.pow_le_pow_left hH2 1
    _ ≤ (m + d) ^ j := Nat.pow_le_pow_right (by omega) hj
  have h1 : m ^ (j + 1) ≤ (m + d) ^ j * m := by
    rw [pow_succ]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) j) le_rfl
  have h2 : (m + d) ^ (j + 1) = (m + d) ^ j * m + (m + d) ^ j * d := by
    rw [pow_succ]; ring
  have h3 : 2 * d ≤ (m + d) ^ j * d := Nat.mul_le_mul hP le_rfl
  omega

private lemma moment_weight_lt (n f k : ℕ) (hf : f % 2 = 0) (hk : 2 ≤ k)
    (h4 : 4 ≤ n + f) :
    (3 ^ k - 3) * (if n = 1 ∧ f ≠ 0 then 1 else 0)
      + (3 ^ k - 3) * (if ¬ Even n ∧ n ≠ 1 then 1 else 0)
      + (2 ^ k - 2) * (if Even n ∧ n ≠ 0 then 1 else 0)
      + (2 ^ k - 2) * (if n = 0 then 1 else 0)
      + (n + f) < (n + f) ^ k := by
  have h2le : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have h3le : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have hkey := pow_excess_strict (m := 2) (H := 0 + f) (by omega) (by omega) hk
    rw [if_neg (by omega : ¬ ((0:ℕ) = 1 ∧ f ≠ 0)),
      if_neg (by simp : ¬ (¬ Even 0 ∧ (0:ℕ) ≠ 1)),
      if_neg (by simp : ¬ (Even 0 ∧ (0:ℕ) ≠ 0)), if_pos rfl]
    omega
  · rcases eq_or_ne n 1 with h1 | h1
    · subst h1
      have hz : f ≠ 0 := by omega
      have hkey := pow_excess_strict (m := 3) (H := 1 + f) (by omega) (by omega) hk
      rw [if_pos ⟨rfl, hz⟩, if_neg (by simp), if_neg (by simp), if_neg (by simp)]
      omega
    · by_cases he : Even n
      · have hkey := pow_excess_strict (m := 2) (H := n + f) (by omega) (by omega) hk
        rw [if_neg (by tauto : ¬ (n = 1 ∧ f ≠ 0)),
          if_neg (by tauto : ¬ (¬ Even n ∧ n ≠ 1)),
          if_pos ⟨he, by omega⟩, if_neg (by omega : ¬ n = 0)]
        omega
      · have hkey := pow_excess_strict (m := 3) (H := n + f) (by omega) (by omega) hk
        rw [if_neg (by tauto : ¬ (n = 1 ∧ f ≠ 0)), if_pos ⟨he, h1⟩,
          if_neg (by tauto : ¬ (Even n ∧ n ≠ 0)), if_neg (by omega : ¬ n = 0)]
        omega

/-- **One ordinate above mass three makes the charge strict.**  `SESSION 334`. -/
theorem momentK_charges_lt_of_big (D : Riemann.ZeroData) {k : ℕ} (hk : 2 ≤ k)
    {γ₀ : ℝ} (hγ₀ : γ₀ ∈ D.ordinates.toFinset) (h4 : 4 ≤ D.H γ₀) :
    (3 ^ k - 3) * hauntedCount D + (3 ^ k - 3) * oddAbove D
      + (2 ^ k - 2) * evenOnAt D + (2 ^ k - 2) * offLineOnly D
      + D.N < momentK D k := by
  classical
  rw [hauntedCount_eq_onAt_one_offAt_pos, oddAbove, evenOnAt, offLineOnly,
    N_eq_sum_H, momentK, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_lt_sum (fun γ hγ => ?_) ⟨γ₀, hγ₀, ?_⟩
  · have hpos : 0 < D.H γ := by
      rw [D.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 hγ
    have hsum := H_eq_onAt_add_offAt D γ
    obtain ⟨r, hr⟩ := even_offAt D γ
    have := moment_weight (onAt D γ) (offAt D γ) k (by omega) (by omega) (by omega)
    rw [← hsum] at this
    convert this using 3
  · have hsum := H_eq_onAt_add_offAt D γ₀
    obtain ⟨r, hr⟩ := even_offAt D γ₀
    have := moment_weight_lt (onAt D γ₀) (offAt D γ₀) k (by omega) hk (by omega)
    rw [← hsum] at this
    convert this using 3

/-- **Mass at most three is exactly the saturating condition.**  `SESSION 334`,
closing the converse `333` left open.

`k ≥ 2` rather than `k ≥ 1`: at `k = 1` the charge is `N ≤ N`, an equality for
every configuration, so the characterisation cannot hold there and the hypothesis
is not cosmetic. -/
theorem momentK_charges_eq_iff (D : ZeroData) {k : ℕ} (hk : 2 ≤ k) :
    ((3 ^ k - 3) * hauntedCount D + (3 ^ k - 3) * oddAbove D
        + (2 ^ k - 2) * evenOnAt D + (2 ^ k - 2) * offLineOnly D
        + D.N = momentK D k)
      ↔ ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ 3 := by
  constructor
  · intro heq γ hγ
    by_contra hb
    have hlt := momentK_charges_lt_of_big D hk hγ (by omega)
    omega
  · exact fun h => momentK_charges_eq_of_mult_le_three D (by omega) h

/-- `momentK` read off the profile. -/
lemma momentK_from_profile (D : ZeroData) (k : ℕ) :
    momentK D k = ((profile D).map fun q => q.1 ^ k).sum := by
  classical
  rw [momentK, profile, Multiset.map_map]
  rfl

/-- `314`'s five-class configuration has masses `1, 3, 3, 2, 2`, so its `k`-th
moment is `1 + 2·3ᵏ + 2·2ᵏ`. -/
lemma momentK_five_class {a : ℝ} (ha : a ≠ 1/2) (k : ℕ) :
    momentK (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]) k = 1 + 2 * 3 ^ k + 2 * 2 ^ k := by
  classical
  have hp := chain_profile ha [(1,0),(1,1),(3,0),(2,0),(0,1)] (by decide)
  norm_num at hp
  rw [momentK_from_profile, hp]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- **Every member of the family is sharp, and at the same configuration.**
`SESSION 332`.

`331` proved the charge at every `k`; this says it is an **equality** at `314`'s
five-class configuration, for every `k ≥ 1` at once.  Each of its five ordinates
sits exactly at its class minimum — masses `1, 3, 3, 2, 2` — so the weight
`mᵏ − m` is what that ordinate actually contributes, at every order.

So the countable family `331` produced is not a sequence in which later members
are slack: they are simultaneously attained. -/
theorem momentK_charges_tight {a : ℝ} (ha : a ≠ 1/2) {k : ℕ} (hk : 1 ≤ k) :
    (3 ^ k - 3) * hauntedCount (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
        + (3 ^ k - 3) * oddAbove (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
        + (2 ^ k - 2) * evenOnAt (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
        + (2 ^ k - 2) * offLineOnly (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
        + (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]).N = momentK (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]) k := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := atomCount_decomposition_all_inhabited ha
  have hp := chain_profile ha [(1,0),(1,1),(3,0),(2,0),(0,1)] (by decide)
  norm_num at hp
  have hN : (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]).N = 11 := by
    rw [N_from_profile, hp]; decide
  have h2le : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have h3le : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
  rw [momentK_five_class ha, h1, h2, h3, h4, h5, hN] at *
  omega

/-! #### Blindness, extended to the decomposition — `SESSION 325`

`324` settled `E.md`'s thesis with a **partial** witness:
`no_muInvariant_theory_computes_NscStd` covers one nature and one quantity.
`314` split the ordinates into five classes, so the question is which of them a
`μ_T`-invariant theory can compute.  `N_sc` it can — `Nsc_eq_ordinate_functional`
— and `oddAtoms` too.  The four gaps are the question.

**Kill condition, filed first:** *if the existing gauge pair does not separate all
four gaps — if some gap agrees on `Gauge.triple` and `Gauge.haunted` — then that
gap is `μ_T`-computable and I report which, rather than extending the
blindness.*  **It fired.**  The mass-three pair separates `hauntedCount` and
`oddAbove` and is **silent** on `evenOnAt` and `offLineOnly`, which are `0` on
both configurations.  Blindness at mass three does not reach the two classes that
need an ordinate of even on-line count.

So there is a second pair, at mass two, and between them the four gaps are
covered. -/

/-- **The mass-three gauge pair separates two of the four gaps.**
`Gauge.triple` is three on-line zeros at one height, `Gauge.haunted` is one
on-line zero with a mirror pair — same `μ_T`, and the ordinate is `oddAbove` for
the first and `hauntedCount` for the second. -/
theorem gauge_pair_separates_haunted_and_oddAbove :
    hauntedCount Gauge.triple = 0 ∧ oddAbove Gauge.triple = 1
      ∧ hauntedCount Gauge.haunted = 1 ∧ oddAbove Gauge.haunted = 0 := by
  classical
  obtain ⟨f, hf⟩ := oddAtoms_ordinate_functional
  have hodd : oddAtoms Gauge.triple = oddAtoms Gauge.haunted := by
    rw [hf, hf, Gauge.ordinates_eq]
  have hnsc := Gauge.Nsc_gauge_invariant
  have h1 := NscStd_eq_Nsc_add_haunted Gauge.triple
  have h2 := NscStd_eq_Nsc_add_haunted Gauge.haunted
  have h3 := oddAtoms_eq_NscStd_add_oddAbove Gauge.triple
  have h4 := oddAtoms_eq_NscStd_add_oddAbove Gauge.haunted
  have ht := Gauge.NscStd_triple
  have hh := Gauge.NscStd_haunted
  have hac : atomCount Gauge.haunted = 1 := by
    rw [atomCount, ← Gauge.ordinates_eq]
    show (Multiset.map Prod.snd (Multiset.replicate 3 ((1/2 : ℝ), (0:ℝ)))).toFinset.card = 1
    rw [Multiset.map_replicate, Multiset.toFinset_replicate, if_neg (by norm_num)]
    rfl
  have hle := oddAtoms_le_atomCount Gauge.haunted
  have hge := NscStd_le_oddAtoms Gauge.haunted
  omega

/-- **A second gauge pair, at mass two, separates the other two.**  One ordinate
of multiplicity two: both zeros on the line, or one mirror pair.  Same `μ_T` by
`configAt_ordinates`, and the ordinate is `evenOnAt` for the first and
`offLineOnly` for the second. -/
theorem gauge_pair_two_separates_even_and_offLine {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 2 0 a).ordinates = (configAt 0 0 1 a).ordinates
      ∧ evenOnAt (configAt 0 2 0 a) = 1 ∧ offLineOnly (configAt 0 2 0 a) = 0
      ∧ evenOnAt (configAt 0 0 1 a) = 0 ∧ offLineOnly (configAt 0 0 1 a) = 1 := by
  classical
  have h2 := configAt_profile (γ := (0:ℝ)) ha (k := 2) (j := 0) (by norm_num)
  have h0 := configAt_profile (γ := (0:ℝ)) ha (k := 0) (j := 1) (by norm_num)
  norm_num at h2 h0
  refine ⟨by rw [configAt_ordinates, configAt_ordinates], ?_, ?_, ?_, ?_⟩
  · rw [evenOnAt_from_profile, h2]; decide
  · rw [offLineOnly_from_profile, h2]; decide
  · rw [evenOnAt_from_profile, h0]; decide
  · rw [offLineOnly_from_profile, h0]; decide

/-! #### …and the four necessity theorems — `SESSION 326`

`325` produced the separating pairs; these are what they are for.
`Blindness.not_muInvariant_computable_of_separating` abstracts the quantity out
of `#7`'s argument, so each gap costs one line of instantiation.  Three of the
four are new; `hauntedCount`'s was already proved at `225` by a different route.

Together with `ZeroData.Nsc_eq_ordinate_functional` and
`oddAtoms_ordinate_functional` — both of which **are** `μ_T` functionals — this
splits `314`'s decomposition cleanly: the ordinate count and the simple count are
visible, and every gap between them is not. -/

/-- `oddAbove` is not an ordinate functional.

(`hauntedCount`'s case is **not** here: `hauntedCount_not_ordinate_functional`
has been below since `225`, routed through
`Blindness.hauntedSet_card_not_ordinate_functional`.  `326` wrote a second one
from the new pair before searching, and the build refused it.) -/
theorem oddAbove_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, oddAbove D = f D.ordinates := by
  intro ⟨f, hf⟩
  obtain ⟨_, h2, _, h4⟩ := gauge_pair_separates_haunted_and_oddAbove
  exact Blindness.not_muInvariant_computable_of_separating (q := oddAbove)
    Gauge.ordinates_eq (by omega) (fun _ => True) (fun _ _ _ => Iff.rfl)
    (Or.inl trivial) ⟨f, fun D _ => hf D⟩

/-- `evenOnAt` is not an ordinate functional — and this one needs `325`'s second
pair, since the mass-three pair reads `0` on both sides. -/
theorem evenOnAt_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, evenOnAt D = f D.ordinates := by
  intro ⟨f, hf⟩
  obtain ⟨ho, h2, _, h4, _⟩ := gauge_pair_two_separates_even_and_offLine
    (a := (1/4 : ℝ)) (by norm_num)
  exact Blindness.not_muInvariant_computable_of_separating (q := evenOnAt)
    ho (by omega) (fun _ => True) (fun _ _ _ => Iff.rfl)
    (Or.inl trivial) ⟨f, fun D _ => hf D⟩

/-- `offLineOnly` is not an ordinate functional, from the same pair. -/
theorem offLineOnly_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, offLineOnly D = f D.ordinates := by
  intro ⟨f, hf⟩
  obtain ⟨ho, _, h3, _, h5⟩ := gauge_pair_two_separates_even_and_offLine
    (a := (1/4 : ℝ)) (by norm_num)
  exact Blindness.not_muInvariant_computable_of_separating (q := offLineOnly)
    ho (by omega) (fun _ => True) (fun _ _ _ => Iff.rfl)
    (Or.inl trivial) ⟨f, fun D _ => hf D⟩

/-! #### What each class costs — `SESSION 315`

`314` made the counting vocabulary a partition.  A partition invites a weight:
each class has a minimum mass, and summing those over the ordinates charges the
whole decomposition against `N`.

* `N_sc` — `H = 1`, costs nothing above the ordinate itself;
* `hauntedCount` — `onAt = 1` with even nonzero `offAt`, so `H ≥ 3`: **two**;
* `oddAbove` — `onAt` odd and above one, so `H ≥ 3`: **two**;
* `evenOnAt` — `onAt` even and positive, so `H ≥ 2`: **one**;
* `offLineOnly` — `onAt = 0` and `offAt` even positive, so `H ≥ 2`: **one**.

**Kill condition, filed first:** *if a joint bound charging all four gaps is
already on disk, this is a re-derivation and the deliverable is the pointer.*
Searched with `statement_index --find 'le_N$|≤ D.N'`, reading every
`ZeroData`-argument row.  It did not fire.

**And it does not move the certified row.**  `Nsc_add_gaps_le_N` specialises at
`oddAbove = evenOnAt = offLineOnly = 0` to `110`'s
`Nsc_add_three_mul_haunted_le_N`, which is the row's engine; the extra terms are
non-negative, so they tighten the bound without loosening the consumer.  What
they would buy needs an *upper* bound on one of the three, and none is on
disk. -/

/-- **Every class charged its minimum mass.**  Subsumes
`two_mul_haunted_add_atomCount_le_N` and `evenOnAt_add_atomCount_le_N`, which are
this with the other classes' weights set to zero.

**Kept long, deliberately — `SESSION 318`.**  `317` put this in one class with
`two_mul_atomCount_add_oddAtoms_le`, so the three lines
`have e := two_mul_atomCount_add_oddAtoms_le D; …; omega` would prove it.  That
proof is **not** taken, and the reason is the opposite of
`Nsc_add_three_mul_haunted_le_N`'s: the weights `2, 2, 1, 1` are this theorem's
content, and the per-ordinate `split_ifs` below is where they are *checked*.
Routing through the older inequality would leave them asserted by the statement
and verified nowhere.  `256`'s case to keep.

**Correction, `SESSION 316`.**  It is **equivalent** to
`two_mul_atomCount_add_oddAtoms_le`, which predates this whole arc — substituting
the four partitions turns each into the other, and the `example` below runs both
directions by `omega`.  So this is a **re-coordinatisation**, not a stronger
bound, and `315`'s *"they tighten the bound without loosening its consumer"* is
wrong: they tighten nothing.  What the decomposition buys is a reading — the
existing inequality **is** "each class charged its minimum mass", and the weights
`3, 3, 2, 2` are its content.

`317` mechanised the check (`forensics/equiv_check.py`) and confirmed it: of the
`25` hypothesis-free `ℕ`-linear `ZeroData` inequalities, `7` follow from the four
partitions alone and the remaining `18` fall into `14` classes.  Two classes have
more than one member — this one, and `110`'s
`three_mul_NscStd_le_N_add_two_mul_Nsc` = `Nsc_add_three_mul_haunted_le_N` =
`two_mul_haunted_add_NscStd_le_N`. -/
theorem mass_charges_every_class (D : ZeroData) :
    2 * hauntedCount D + 2 * oddAbove D + evenOnAt D + offLineOnly D
      + atomCount D ≤ D.N := by
  classical
  rw [hauntedCount_eq_onAt_one_offAt_pos, oddAbove, evenOnAt, offLineOnly,
    atomCount, N_eq_sum_H, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hpos : 0 < D.H γ := by
    rw [D.H_eq_count, Multiset.count_pos]
    exact Multiset.mem_toFinset.1 hγ
  have hsum := H_eq_onAt_add_offAt D γ
  obtain ⟨r, hr⟩ := even_offAt D γ
  split_ifs <;> simp only [Nat.even_iff] at * <;> omega

/-- **The same bound with `314`'s partition substituted in**, so the simple
ordinates appear on the left with the gaps' full weights.  At
`oddAbove = evenOnAt = offLineOnly = 0` this is `110`'s
`Nsc_add_three_mul_haunted_le_N`. -/
theorem Nsc_add_gaps_le_N (D : ZeroData) :
    D.Nsc + 3 * hauntedCount D + 3 * oddAbove D + 2 * evenOnAt D
      + 2 * offLineOnly D ≤ D.N := by
  have h1 := mass_charges_every_class D
  have h2 := atomCount_decomposition D
  omega

/-! **The equivalence, kept as `example`s.**  `SESSION 316`, and `R25`: attempt
the composite before believing two routes differ.  Both directions are `omega`
over the four partitions, so `315`'s bound and `two_mul_atomCount_add_oddAtoms_le`
are one inequality in two coordinate systems.  Unnamed, because a named theorem
here would be a shared conclusion (`256`). -/
example (D : ZeroData) :
    2 * atomCount D + oddAtoms D ≤ D.N + 2 * D.Nsc := by
  have m := mass_charges_every_class D
  have p2 := NscStd_eq_Nsc_add_haunted D
  have p3 := oddAtoms_eq_NscStd_add_oddAbove D
  have p4 := onLineOrdinates_eq_oddAtoms_add_evenOnAt D
  have p5 := onLineOrdinates_add_offLineOnly D
  omega

example (D : ZeroData) :
    2 * hauntedCount D + 2 * oddAbove D + evenOnAt D + offLineOnly D
      + atomCount D ≤ D.N := by
  have e := two_mul_atomCount_add_oddAtoms_le D
  have p2 := NscStd_eq_Nsc_add_haunted D
  have p3 := oddAtoms_eq_NscStd_add_oddAbove D
  have p4 := onLineOrdinates_eq_oddAtoms_add_evenOnAt D
  have p5 := onLineOrdinates_add_offLineOnly D
  omega

/-- **The weights cannot be raised.**  `SESSION 316`.

`314`'s five-class configuration attains `Nsc_add_gaps_le_N` with equality:
masses `1, 3, 3, 2, 2` give `N = 11`, and `1 + 3 + 3 + 2 + 2 = 11`.  So each of
`3, 3, 2, 2` is the largest weight its class admits, and the re-coordinatisation
is at least a **sharp** reading rather than merely a different one. -/
theorem Nsc_add_gaps_le_N_tight {a : ℝ} (ha : a ≠ 1/2) :
    (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]).Nsc + 3 * hauntedCount (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
      + 3 * oddAbove (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]) + 2 * evenOnAt (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)])
      + 2 * offLineOnly (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]) = (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]).N := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := atomCount_decomposition_all_inhabited ha
  have hp := chain_profile ha [(1,0),(1,1),(3,0),(2,0),(0,1)] (by decide)
  norm_num at hp
  have hN : (chain a [(1,0),(1,1),(3,0),(2,0),(0,1)]).N = 11 := by rw [N_from_profile, hp]; decide
  rw [h1, h2, h3, h4, h5, hN]

/-! #### `oddAtoms`, bracketed by the ledger it does not belong to — `SESSION 302`

`295` showed `oddAtoms` is not a functional of the five ledger counts, and gave
`oddAtoms ≡ N⊛ (mod 4)` as what `N⊛` does pin.  The remaining question is what
the ledger *bounds*.  Below, `287`'s `NscStd ≤ oddAtoms`.  Above, this.

**Kill condition, filed first:** *if a ledger-only upper bound already exists —
if anything bounds `oddAtoms` by `N`, `N⊛`, `N_sc`, `NscStd`, `N_off` alone —
this is a re-derivation and the deliverable is the pointer.*  Searched with
`statement_index --find 'oddAtoms'`, reading all twelve `ZeroData` rows:
`Noff_add_oddAtoms_le_N` is ledger-only but weak, and
`two_mul_atomCount_add_oddAtoms_le` is sharp but spends `atomCount`, which is
not a ledger count.  It did not fire. -/

/-- **`3·oddAtoms ≤ N + 2·N_sc`** — the ledger's upper bound on a quantity the
ledger does not determine.

Two steps: `two_mul_atomCount_add_oddAtoms_le` and `oddAtoms ≤ atomCount`.  It is
strictly stronger than `Noff_add_oddAtoms_le_N` wherever `N_off` is small — on
`295`'s witness (`N = 14`, `N_off = 0`, `N_sc = 0`) that bound gives `14` and
this one gives `4`, which the witness attains. -/
theorem three_mul_oddAtoms_le (D : ZeroData) :
    3 * oddAtoms D ≤ D.N + 2 * D.Nsc := by
  have h1 := two_mul_atomCount_add_oddAtoms_le D
  have h2 := oddAtoms_le_atomCount D
  omega

/-- **And it is attained at every size**, by `n` on-line atoms of mass three —
the `t = 0` end of `bracket_tight_chain`'s family.  There `N = 3n`, `N_sc = 0`
and every ordinate is odd, so both sides are `3n`. -/
theorem three_mul_oddAtoms_attained {a : ℝ} (ha : a ≠ 1/2) (n : ℕ) :
    3 * oddAtoms (chain a (List.replicate n ((3:ℕ), (0:ℕ))))
      = (chain a (List.replicate n ((3:ℕ), (0:ℕ)))).N
        + 2 * (chain a (List.replicate n ((3:ℕ), (0:ℕ)))).Nsc := by
  have hb := bracket_tight_chain ha n 0 (Nat.zero_le n)
  have hn := Noff_tight_chain ha n 0 (Nat.zero_le n)
  simp only [List.replicate_zero, List.nil_append, Nat.sub_zero] at hb hn
  omega

/-- **Equality does not need pure triples.**  `SESSION 303`, correcting `302`.

*(`322`: this proof stays long.  `321`'s profile readings collapse a witness whose
profile is a small **literal** — `decide` settles five entries — but this one's
profile is built with `List.replicate`, so `decide` would face `1321` of them.
The readings shorten witnesses, not all witnesses.)*

Every quantity in `three_mul_oddAtoms_le` is atom-additive, and the per-atom
slack `mass + 2·[mass = 1] − 3·[mass odd]` vanishes at mass `1` as well as at
mass `3`.  So the equality set is *every ordinate of mass one or three* — which
is `104`/`110`'s extremal family, not only its all-triples end.

`112`'s cap witness is the mixture: `1000` simple atoms beside `321` haunted
mass-`3` atoms, `3 · 1321 = 3963 = 1963 + 2 · 1000`. -/
theorem three_mul_oddAtoms_eq_cap_witness {a : ℝ} (ha : a ≠ 1/2) :
    3 * oddAtoms (chain a (List.replicate 1000 ((1:ℕ),(0:ℕ))
        ++ List.replicate 321 ((1:ℕ),(1:ℕ))))
      = (chain a (List.replicate 1000 ((1:ℕ),(0:ℕ))
          ++ List.replicate 321 ((1:ℕ),(1:ℕ)))).N
        + 2 * (chain a (List.replicate 1000 ((1:ℕ),(0:ℕ))
          ++ List.replicate 321 ((1:ℕ),(1:ℕ)))).Nsc := by
  classical
  set L := List.replicate 1000 ((1:ℕ),(0:ℕ)) ++ List.replicate 321 ((1:ℕ),(1:ℕ))
    with hL
  have hne : ∀ x ∈ L, x.1 + 2 * x.2 ≠ 0 := by
    intro x hx; rw [hL, List.mem_append] at hx
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
  have hO : oddAtoms (chain a L) = 1321 := by
    rw [oddAtoms_from_profile, hp]
    simp only [Multiset.filter_coe, List.filter_append, List.filter_replicate]
    norm_num
  have hs : ((chain a L).Nsc : ℤ) = 1000 := by
    rw [Nsc_from_profile, hp]
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate]
    norm_num
  have hs' : (chain a L).Nsc = 1000 := by exact_mod_cast hs
  rw [hN, hO, hs']

/-! #### The equality set itself — `SESSION 305`

`303` corrected `302`'s claim about when `three_mul_oddAtoms_le` is tight and
backed the correction with one witness.  A witness is not a characterisation.
This is the characterisation, and it is a **different** one from the sibling
already on disk: `three_mul_NscStd_eq_iff` pins `H = 1 ∨ (H = 3 ∧ onAt = 1)`,
while this pins `H = 1 ∨ H = 3` with no condition on the split.  The gap between
the two is the ordinate of mass three carrying **three** on-line zeros — odd
`onAt` above one, which is `293`'s upper gap.

**Kill condition, filed first:** *if the multiset-sum route does not land, ship
the pointwise slack lemma and the forward direction and report the
characterisation as open.*  It did not fire. -/

/-- The per-atom slack in `three_mul_oddAtoms_le`, in `ℤ` so it can be
negative-free without truncation. -/
private noncomputable def oddSlack (q : ℕ × ℕ) : ℤ :=
  (q.1 : ℤ) + 2 * (if q.1 = 1 then 1 else 0) - 3 * (if ¬ Even q.1 then 1 else 0)

/-- The slack is `0` at mass `1` and mass `3`, and positive elsewhere.  Mass `0`
is excluded: it also gives `0`, and the hypothesis is what rules it out. -/
private lemma oddSlack_spec (q : ℕ × ℕ) (h0 : q.1 ≠ 0) :
    0 ≤ oddSlack q ∧ (oddSlack q = 0 ↔ q.1 = 1 ∨ q.1 = 3) := by
  rw [oddSlack]
  by_cases h1 : q.1 = 1
  · rw [if_pos h1, if_pos (by rw [h1]; decide), h1]; norm_num
  · rw [if_neg h1]
    by_cases h2 : ¬ Even q.1
    · have hm : q.1 % 2 = 1 := Nat.not_even_iff.mp h2
      rw [if_pos h2]
      refine ⟨by push_cast; omega, ⟨fun h => ?_, fun h => ?_⟩⟩
      · right; push_cast at h; omega
      · rcases h with h | h
        · exact absurd h h1
        · rw [h]; norm_num
    · have hm : q.1 % 2 = 0 := Nat.even_iff.mp (not_not.mp h2)
      rw [if_neg h2]
      refine ⟨by push_cast; omega, ⟨fun h => ?_, fun h => ?_⟩⟩
      · exfalso; push_cast at h; omega
      · exfalso; rcases h with h | h <;> rw [h] at hm <;> simp at hm

private lemma oddIndicator_sum (s : Multiset (ℕ × ℕ)) :
    ((s.map fun q => if ¬ Even q.1 then (1:ℤ) else 0)).sum
      = (Multiset.card (s.filter fun q => ¬ Even q.1) : ℤ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons, ih]
      by_cases h : ¬ Even q.1
      · rw [if_pos h, if_pos h]; simp [add_comm]
      · rw [if_neg h, if_neg h]; simp

private lemma oddSlack_sum_spec (s : Multiset (ℕ × ℕ))
    (hpos : ∀ q ∈ s, q.1 ≠ 0) :
    0 ≤ (s.map oddSlack).sum
      ∧ ((s.map oddSlack).sum = 0 ↔ ∀ q ∈ s, q.1 = 1 ∨ q.1 = 3) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      have hq := hpos q (Multiset.mem_cons_self q s)
      have hs : ∀ r ∈ s, r.1 ≠ 0 := fun r hr => hpos r (Multiset.mem_cons_of_mem hr)
      obtain ⟨hn, hz⟩ := ih hs
      obtain ⟨hqn, hqz⟩ := oddSlack_spec q hq
      rw [Multiset.map_cons, Multiset.sum_cons]
      refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
      · have h1 : oddSlack q = 0 := by linarith
        have h2 : (s.map oddSlack).sum = 0 := by linarith
        intro r hr
        rcases Multiset.mem_cons.1 hr with hr | hr
        · rw [hr]; exact hqz.1 h1
        · exact (hz.1 h2) r hr
      · have h1 : oddSlack q = 0 := hqz.2 (h q (Multiset.mem_cons_self q s))
        have h2 : (s.map oddSlack).sum = 0 :=
          hz.2 fun r hr => h r (Multiset.mem_cons_of_mem hr)
        rw [h1, h2]; ring

private lemma sum_oddSlack (s : Multiset (ℕ × ℕ)) :
    (s.map oddSlack).sum = ((s.map fun q => (q.1:ℤ)).sum)
      + 2 * ((s.map fun q => if q.1 = 1 then (1:ℤ) else 0).sum)
      - 3 * ((s.map fun q => if ¬ Even q.1 then (1:ℤ) else 0).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, oddSlack]
      ring

private lemma sum_fst_cast (s : Multiset (ℕ × ℕ)) :
    ((s.map fun q => (q.1:ℤ)).sum) = ((s.map Prod.fst).sum : ℕ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]; push_cast; ring

/-- **`302`'s bound is tight when every ordinate has mass one or three.**
`SESSION 305`.

Compare `three_mul_NscStd_eq_iff`, whose condition is
`H = 1 ∨ (H = 3 ∧ onAt = 1)`.  This one drops the `onAt` clause: a mass-three
ordinate carrying three on-line zeros satisfies this and fails that, and it is
the configuration `293` named as the bracket's upper gap.

`112`'s cap witness satisfies both, which is why `303`'s single witness could not
tell the two characterisations apart. -/
theorem three_mul_oddAtoms_eq_iff (D : ZeroData) :
    3 * oddAtoms D = D.N + 2 * D.Nsc ↔
      ∀ γ ∈ D.ordinates.toFinset, D.H γ = 1 ∨ D.H γ = 3 := by
  classical
  have hmem : ∀ q ∈ profile D, q.1 ≠ 0 := by
    intro q hq
    rw [profile, Multiset.mem_map] at hq
    obtain ⟨γ, hγ, rfl⟩ := hq
    have : 0 < D.H γ := by
      rw [D.H_eq_count, Multiset.count_pos]
      exact Multiset.mem_toFinset.1 (by simpa using hγ)
    omega
  obtain ⟨_, hz⟩ := oddSlack_sum_spec (profile D) hmem
  have hval : ((profile D).map oddSlack).sum
      = (D.N : ℤ) + 2 * (D.Nsc : ℤ) - 3 * (oddAtoms D : ℤ) := by
    rw [sum_oddSlack, sum_fst_cast, ← N_from_profile, oddIndicator_sum,
      ← oddAtoms_from_profile, ← Nsc_from_profile]
  have hcond : (∀ q ∈ profile D, q.1 = 1 ∨ q.1 = 3) ↔
      ∀ γ ∈ D.ordinates.toFinset, D.H γ = 1 ∨ D.H γ = 3 := by
    constructor
    · intro h γ hγ
      exact h (D.H γ, offAt D γ)
        (by rw [profile, Multiset.mem_map]; exact ⟨γ, by simpa using hγ, rfl⟩)
    · intro h q hq
      rw [profile, Multiset.mem_map] at hq
      obtain ⟨γ, hγ, rfl⟩ := hq
      exact h γ (by simpa using hγ)
  rw [← hcond, ← hz, hval]
  constructor <;> intro h <;> omega

/-- **And the two characterisations are genuinely different.**  `SESSION 305`.

One ordinate of mass three with all three zeros on the line: `N = 3`,
`N_sc = 0`, `oddAtoms = 1`, `NscStd = 0`.  It satisfies
`three_mul_oddAtoms_eq_iff`'s condition and fails `three_mul_NscStd_eq_iff`'s,
so the pair is two theorems rather than one restated (`256`). -/
theorem three_mul_oddAtoms_eq_iff_separates {a : ℝ} (ha : a ≠ 1/2) :
    (3 * oddAtoms (configAt 0 3 0 a)
        = (configAt 0 3 0 a).N + 2 * (configAt 0 3 0 a).Nsc)
      ∧ ¬ (3 * (configAt 0 3 0 a).NscStd
            = (configAt 0 3 0 a).N + 2 * (configAt 0 3 0 a).Nsc) := by
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 3) (j := 0) (by norm_num)
  norm_num at hp
  have hsc : ((configAt 0 3 0 a).Nsc : ℤ) = 0 := by
    rw [Nsc_from_profile, hp]; decide
  have h2 : (configAt 0 3 0 a).Nsc = 0 := by exact_mod_cast hsc
  have hstd : ((configAt 0 3 0 a).NscStd : ℤ) = 0 := by
    rw [NscStd_from_profile, hp]; decide
  have h3 : (configAt 0 3 0 a).NscStd = 0 := by exact_mod_cast hstd
  constructor
  · rw [oddAtoms_from_profile, N_from_profile, hp, h2]; decide
  · rw [N_from_profile, hp, h2, h3]; decide

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

/-- **`NoHaunted` buys no star bound at all.**  `SESSION 257`.

`181` put this in a docstring — *"what `H ≤ 2` buys beyond the row is the star
bound `C ≤ 1.3275`, which hauntedness alone does not give"* — and left it there.
`229` made the same move on `oddAtoms` and the answer was that an assertion in a
docstring is still an assertion.  This is the witness.

`configAt 0 (m+1) 0 a` has no off-line zeros whatever, which is the strongest
form of unhauntedness available, and `Nstar_bound_attained` gives
`N⊛ = (m+1)·N`.  So the star ratio runs to infinity inside the class, and no
`StarBound C` survives it for any real `C`.

Read against `255`: multiplicity `≤ 2` implies `NoHaunted` and the implication
is strict, so `H ≤ 2` is the stronger hypothesis — and this is what the extra
strength is spent on.  The two hypotheses agree on the `Nsc` row and part
company on the star row. -/
theorem noHaunted_no_starBound (C : ℝ) {a : ℝ} (ha : a ≠ 1/2) :
    ∃ D : ZeroData, D.Noff = 0
      ∧ (∀ γ, D.H γ - offAt D γ = 1 → D.H γ = 1)
      ∧ 0 < D.N ∧ C * (D.N : ℝ) < (D.Nstar : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have hoff : (configAt 0 (m + 1) 0 a).Noff = 0 := by
    rw [configAt_Noff ha]
  have hN : (configAt 0 (m + 1) 0 a).N = m + 1 := by
    rw [configAt_N]
  obtain ⟨-, hstar⟩ := Nstar_bound_attained (M := m + 1) (a := a) (by omega)
  refine ⟨configAt 0 (m + 1) 0 a, hoff, noHaunted_of_Noff_zero _ hoff, ?_, ?_⟩
  · rw [hN]; omega
  · rw [hstar, hN]
    push_cast
    have hm1 : C < (m : ℝ) + 1 := by linarith
    nlinarith

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
  have ha2 := offLine_ne_half ha
  have ha2' := offLine_mirror_ne_half ha
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

/-- **`NscAny` is not a functional of `(μ_T, offAt)` either.**  `SESSION 221`.

`220` put `NscAny` outside `μ_T`'s reach.  This puts it outside the *fiber*
coordinate's reach as well — the pair `(μ_T, offAt)` that `ledger_determined`
shows is enough to compute the entire ledger.

Two configurations at one ordinate, both with four off-line zeros and nothing on
the line, so `μ_T` and `offAt` agree everywhere: one doubled mirror pair, versus
two distinct mirror pairs.  The first has every point of multiplicity two, so
`NscAny = 0`; the second has a point of multiplicity one, so `NscAny > 0`.

The consequence for the simple-zero genre: no bound on `NscAny` follows from the
data that determines the ledger.  `197`/`214`/`218` had to route through the
off-line import, and this says that was not a choice of convenience. -/
theorem NscAny_not_fiber_functional {a b : ℝ} (ha : a ≠ 1/2) (hb : b ≠ 1/2)
    (hab : a ≠ b) (hab' : a ≠ 1 - b) :
    (config 0 2 a).ordinates = (superpose (config 0 1 a) (config 0 1 b)).ordinates
      ∧ (∀ γ : ℝ, offAt (config 0 2 a) γ
          = offAt (superpose (config 0 1 a) (config 0 1 b)) γ)
      ∧ (config 0 2 a).NscAny
          ≠ (superpose (config 0 1 a) (config 0 1 b)).NscAny := by
  classical
  have hord : (config 0 2 a).ordinates
      = (superpose (config 0 1 a) (config 0 1 b)).ordinates := by
    rw [add_ordinates, config_ordinates, config_ordinates, config_ordinates]
    rw [show (0 + 2 * 2 : ℕ) = 4 by norm_num,
      show (0 + 2 * 1 : ℕ) = 2 by norm_num, ← Multiset.replicate_add]
  have hoff : ∀ γ : ℝ, offAt (config 0 2 a) γ
      = offAt (superpose (config 0 1 a) (config 0 1 b)) γ := by
    intro γ
    rw [offAt_superpose]
    by_cases hγ : γ = 0
    · subst hγ
      rw [config_eq_configAt, config_eq_configAt, config_eq_configAt,
        offAt_configAt_self ha, offAt_configAt_self ha, offAt_configAt_self hb]
    · rw [config_eq_configAt, config_eq_configAt, config_eq_configAt,
        offAt_configAt_other (a := a) hγ 0 2,
        offAt_configAt_other (a := a) hγ 0 1,
        offAt_configAt_other (a := b) hγ 0 1]
  refine ⟨hord, hoff, ?_⟩
  have hA : (config 0 2 a).NscAny = 0 := by
    rw [config_NscAny 0 2 ha]; norm_num
  -- the second configuration has a point of multiplicity one
  have hcount : (superpose (config 0 1 a) (config 0 1 b)).Z.count (a, (0:ℝ)) = 1 := by
    show Multiset.count (a, (0:ℝ))
        ((Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
            + (Multiset.replicate 1 (a, (0:ℝ))
              + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))))
          + (Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
            + (Multiset.replicate 1 (b, (0:ℝ))
              + Multiset.replicate 1 ((1 - b : ℝ), (0:ℝ))))) = 1
    have h1 : (a : ℝ) ≠ 1 - a := fun h => ha (by linarith)
    have h2 : (a : ℝ) ≠ 1 - b := hab'
    simp [Multiset.count_replicate, h1, h2, hab]
  have hmem : (a, (0:ℝ)) ∈ (superpose (config 0 1 a) (config 0 1 b)).Z :=
    Multiset.count_pos.1 (by rw [hcount]; norm_num)
  have hB : 0 < (superpose (config 0 1 a) (config 0 1 b)).NscAny := by
    show 0 < Multiset.card (Multiset.filter
      (fun p => (superpose (config 0 1 a) (config 0 1 b)).Z.count p = 1)
      (superpose (config 0 1 a) (config 0 1 b)).Z)
    rw [Multiset.card_pos_iff_exists_mem]
    exact ⟨(a, (0:ℝ)), Multiset.mem_filter.2 ⟨hmem, hcount⟩⟩
  omega

/-- **`distinctZeros` is not a functional of `(μ_T, offAt)` either.**
`SESSION 223`.

The literature's `N_d` counts distinct zeros as *points*; `atomCount` counts
distinct *ordinates* and is an ordinate functional by definition
(`atomCount_ordinate_functional`).  `221`'s pair separates the two notions
sharply: same ordinates, same `offAt`, and one doubled mirror pair has two
distinct points where two distinct mirror pairs have four.

`distinctZeros_not_profile_functional` already put `N_d` outside the profile.
This puts it outside the finer fiber coordinate, and does it with the pair that
already did the same for `NscAny` — so the two literature quantities the project
brackets are invisible to its coordinates for the same reason and at the same
witness.

Proved by strict inclusion rather than by counting `B`, per `R22`. -/
theorem distinctZeros_not_fiber_functional {a b : ℝ} (ha : a ≠ 1/2) (hb : b ≠ 1/2)
    (hab : a ≠ b) (hab' : a ≠ 1 - b) :
    (config 0 2 a).ordinates = (superpose (config 0 1 a) (config 0 1 b)).ordinates
      ∧ (∀ γ : ℝ, offAt (config 0 2 a) γ
          = offAt (superpose (config 0 1 a) (config 0 1 b)) γ)
      ∧ distinctZeros (config 0 2 a)
          < distinctZeros (superpose (config 0 1 a) (config 0 1 b)) := by
  classical
  obtain ⟨hord, hoff, -⟩ := NscAny_not_fiber_functional ha hb hab hab'
  refine ⟨hord, hoff, ?_⟩
  have hmemA : ∀ x : ℝ × ℝ, x ∈ (config 0 2 a).Z ↔ (x = (a, (0:ℝ)) ∨ x = ((1 - a : ℝ), (0:ℝ))) := by
    intro x
    show x ∈ Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 2 (a, (0:ℝ))
          + Multiset.replicate 2 ((1 - a : ℝ), (0:ℝ))) ↔ _
    simp
    tauto
  have hmemB : ∀ x : ℝ × ℝ,
      x ∈ (superpose (config 0 1 a) (config 0 1 b)).Z ↔
        (x = (a, (0:ℝ)) ∨ x = ((1 - a : ℝ), (0:ℝ))
          ∨ x = (b, (0:ℝ)) ∨ x = ((1 - b : ℝ), (0:ℝ))) := by
    intro x
    show x ∈ (Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 1 (a, (0:ℝ))
          + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))))
      + (Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 1 (b, (0:ℝ))
          + Multiset.replicate 1 ((1 - b : ℝ), (0:ℝ)))) ↔ _
    simp
    tauto
  have hsub : (config 0 2 a).Z.toFinset
      ⊆ (superpose (config 0 1 a) (config 0 1 b)).Z.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx ⊢
    rcases (hmemA x).1 hx with h | h
    · exact (hmemB x).2 (Or.inl h)
    · exact (hmemB x).2 (Or.inr (Or.inl h))
  have hin : (b, (0:ℝ)) ∈ (superpose (config 0 1 a) (config 0 1 b)).Z.toFinset := by
    rw [Multiset.mem_toFinset]; exact (hmemB _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hout : (b, (0:ℝ)) ∉ (config 0 2 a).Z.toFinset := by
    rw [Multiset.mem_toFinset]
    intro h
    rcases (hmemA _).1 h with h1 | h1
    · exact hab (congrArg Prod.fst h1).symm
    · exact hab' (by have := congrArg Prod.fst h1; simp at this; linarith)
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨_, hin, hout⟩)

/-- **`NscAny ≤ distinctZeros`** — the two literature quantities, related.
`SESSION 227`.

`224`'s map puts both on the bottom level: neither is a functional of
`(μ_T, offAt)`.  They are still related to each other, and the relation is the
obvious one — a zero of multiplicity one is in particular a distinct point, so
the simple-zero count never exceeds `N_d`.

The proof is that the multiplicity-one zeros form a duplicate-free sub-multiset:
each has count `1` in `Z`, hence count `1` in the filter, so its card is the card
of its `toFinset`, which sits inside `Z.toFinset`.

Consequence for the two genres: any lower bound on `NscAny` is a lower bound on
`N_d`.  Both sit outside this project's coordinates, and the inequality between
them holds anyway. -/
theorem NscAny_le_distinctZeros (D : ZeroData) : D.NscAny ≤ distinctZeros D := by
  classical
  have hcount : ∀ p ∈ D.Z.filter (fun p => D.Z.count p = 1),
      (D.Z.filter (fun p => D.Z.count p = 1)).count p = 1 := by
    intro p hp
    have hq : D.Z.count p = 1 := (Multiset.mem_filter.1 hp).2
    rw [Multiset.count_filter, if_pos hq, hq]
  have hnodup : (D.Z.filter (fun p => D.Z.count p = 1)).Nodup :=
    Multiset.nodup_iff_count_le_one.2 fun p => by
      by_cases hp : p ∈ D.Z.filter (fun p => D.Z.count p = 1)
      · exact le_of_eq (hcount p hp)
      · exact le_of_eq_of_le (Multiset.count_eq_zero.2 hp) (by norm_num)
  have hcard : (D.Z.filter (fun p => D.Z.count p = 1)).card
      = (D.Z.filter (fun p => D.Z.count p = 1)).toFinset.card :=
    (Multiset.toFinset_card_of_nodup hnodup).symm
  have hsub : (D.Z.filter (fun p => D.Z.count p = 1)).toFinset ⊆ D.Z.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx ⊢
    exact Multiset.mem_of_mem_filter hx
  show Multiset.card (D.Z.filter (fun p => D.Z.count p = 1)) ≤ D.Z.toFinset.card
  rw [hcard]
  exact Finset.card_le_card hsub

/-- **…and the bound is attained, and strict somewhere.**  `SESSION 227`.
`config 1 1 a` has three distinct zeros, all simple; `config 0 2 a` has two
distinct zeros and none simple. -/
theorem NscAny_le_distinctZeros_attained_and_strict {a : ℝ} (ha : a ≠ 1/2) :
    (config 1 1 a).NscAny = distinctZeros (config 1 1 a)
      ∧ (config 0 2 a).NscAny < distinctZeros (config 0 2 a) := by
  classical
  have hA : distinctZeros (config 1 1 a) = 3 := by
    show (config 1 1 a).Z.toFinset.card = 3
    have hZ : (config 1 1 a).Z = Multiset.replicate 1 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 1 (a, (0:ℝ))
          + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))) := rfl
    have h1 : ((1/2 : ℝ), (0:ℝ)) ≠ (a, (0:ℝ)) := by
      intro h; exact ha (congrArg Prod.fst h).symm
    have h2 : ((1/2 : ℝ), (0:ℝ)) ≠ ((1 - a : ℝ), (0:ℝ)) := by
      intro h; exact ha (by have := congrArg Prod.fst h; simp at this; linarith)
    have h3 : (a, (0:ℝ)) ≠ ((1 - a : ℝ), (0:ℝ)) := by
      intro h; exact ha (by have := congrArg Prod.fst h; simp at this; linarith)
    have ha2 := offLine_ne_half ha
    have ha3 := offLine_ne_refl ha
    have ha4 : (2⁻¹ : ℝ) ≠ 1 - a := Ne.symm (offLine_mirror_ne_half ha)
    rw [hZ]
    simp [Multiset.toFinset_add, ha2, ha3, ha4, Ne.symm ha2, Ne.symm ha3,
      Ne.symm ha4, Finset.card_insert_of_notMem]
  have hB : distinctZeros (config 0 2 a) = 2 := by
    show (config 0 2 a).Z.toFinset.card = 2
    have hZ : (config 0 2 a).Z = Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
        + (Multiset.replicate 2 (a, (0:ℝ))
          + Multiset.replicate 2 ((1 - a : ℝ), (0:ℝ))) := rfl
    have h3 : (a, (0:ℝ)) ≠ ((1 - a : ℝ), (0:ℝ)) := by
      intro h; exact ha (by have := congrArg Prod.fst h; simp at this; linarith)
    rw [hZ]; simp [Multiset.toFinset_add, h3]
  constructor
  · rw [hA, config_NscAny 1 1 ha]; norm_num
  · rw [hB, config_NscAny 0 2 ha]; norm_num

/-- **Equal ordinates and equal `offAt` give equal profiles.**  `SESSION 222`.
The profile is built from exactly those two, so this is bookkeeping — but naming
it turns `221`'s witnesses into a profile-level statement for free. -/
theorem profile_eq_of_ordinates_offAt {D D' : ZeroData}
    (hord : D.ordinates = D'.ordinates) (hoff : ∀ γ, offAt D γ = offAt D' γ) :
    profile D = profile D' := by
  classical
  have hH : ∀ γ, D.H γ = D'.H γ := fun γ => by
    rw [D.H_eq_count, D'.H_eq_count, hord]
  rw [profile, profile, hord]
  exact Multiset.map_congr rfl fun γ _ => by rw [hH, hoff]

/-- **`NscAny` is not a functional of the profile.**  `SESSION 222`.

`221`'s two configurations agree in ordinates and in `offAt`, so by
`profile_eq_of_ordinates_offAt` they share a profile, and their `NscAny` differ.

This is why `196`'s dictionary entries are **inequalities**.  `NscStd ≤ NscAny`
and `NscAny ≤ NscStd + Noff` bound the literature's quantity from the project's
own, and no sharpening to an identity is available: the profile determines every
ledger entry (`N_from_profile` and its four companions) and does not determine
`NscAny`.  `196` proved the three bounds attained and each strict somewhere;
this says the strictness is structural rather than a gap in the witnesses. -/
theorem NscAny_not_profile_functional {a b : ℝ} (ha : a ≠ 1/2) (hb : b ≠ 1/2)
    (hab : a ≠ b) (hab' : a ≠ 1 - b) :
    profile (config 0 2 a) = profile (superpose (config 0 1 a) (config 0 1 b))
      ∧ (config 0 2 a).NscAny
          ≠ (superpose (config 0 1 a) (config 0 1 b)).NscAny := by
  obtain ⟨hord, hoff, hne⟩ := NscAny_not_fiber_functional ha hb hab hab'
  exact ⟨profile_eq_of_ordinates_offAt hord hoff, hne⟩

/-- The unconditional form: no function of the profile computes `NscAny`.
`SESSION 222`. -/
theorem no_profile_function_computes_NscAny :
    ¬ ∃ f : Multiset (ℕ × ℕ) → ℕ, ∀ D : ZeroData, D.NscAny = f (profile D) := by
  rintro ⟨f, hf⟩
  obtain ⟨hp, hne⟩ := NscAny_not_profile_functional (a := 0) (b := 1/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hne (by rw [hf, hf, hp])

/-- **…but the fiber coordinate does see it.**  `SESSION 225`.

`ledger_determined` computes `N_sc` and `NscStd` from `(μ_T, offAt)`, so the
master identity pins `hauntedSet.card` too.  With
`Blindness.hauntedSet_card_not_ordinate_functional` this places the haunted
count in the middle level of `224`'s map, beside `NscStd` and `N_off`: invisible
to `μ_T`, visible to the fiber. -/
theorem hauntedSet_card_determined {D D' : ZeroData}
    (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) :
    D.hauntedSet.card = D'.hauntedSet.card := by
  obtain ⟨-, -, hsc, hstd, -⟩ := ledger_determined hord hoff
  have h1 := ZeroData.NscStd_eq_Nsc_add_haunted D
  have h2 := ZeroData.NscStd_eq_Nsc_add_haunted D'
  omega

/-- **A no-haunted bundle computes `NscStd` from `μ_T`.**  `SESSION 230`.

`Blindness.separating_bundle_excludes` is the negative side of the bundle
question: any hypothesis that lets `μ_T` compute `NscStd` must exclude one of
two legitimate configurations.  Its docstring says what a useful bundle does —
*"it rules out the world in which the coordinate is ambiguous"* — and the
development had no instance of one.

Here is the instance the board already prices.  `NoHaunted` forces
`hauntedCount = 0`, the master identity collapses `NscStd` onto `N_sc`, and
`N_sc` **is** a `μ_T` functional (`ZeroData.Nsc_eq_ordinate_functional`).  So the
invisible row becomes visible under exactly that hypothesis.

Note the shape, which is `224`'s map talking to `RULING.md`'s board: the
hypothesis itself is *not* `μ_T`-checkable — `226` puts `hauntedCount` outside
`μ_T` — so a certificate class cannot verify it and can only assume it.  That is
what buying a row on the board costs. -/
theorem noHaunted_bundle_computes_NscStd (B : ZeroData → Prop)
    (hB : ∀ D, B D → hauntedCount D = 0) :
    ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, B D → D.NscStd = f D.ordinates := by
  classical
  refine ⟨fun m => (m.filter fun γ => Multiset.count γ m = 1).card, fun D hD => ?_⟩
  have h := NscStd_eq_Nsc_add_haunted D
  rw [hB D hD, Nat.add_zero] at h
  rw [h, ZeroData.Nsc_eq_ordinate_functional]

/-- **…and such a bundle must exclude one of the two gauge configurations.**
`SESSION 230`.  The consistency check: feeding the bundle above into
`separating_bundle_excludes` returns the exclusion it predicts. -/
theorem noHaunted_bundle_excludes (B : ZeroData → Prop)
    (hB : ∀ D, B D → hauntedCount D = 0) :
    ¬ (B Gauge.triple ∧ B Gauge.haunted) :=
  separating_bundle_excludes B (noHaunted_bundle_computes_NscStd B hB)

/-- **The two haunted counts are the same number.**  `SESSION 226`.

The development carries two of them, in two namespaces, and they are used in
different halves of the project:

* `ZeroData.hauntedSet` counts haunted **zeros** — on-line, multiplicity one, at
  a crowded ordinate — and `ZeroData.NscStd_eq_Nsc_add_haunted` is the master
  identity in terms of its cardinality.
* `Blindness.hauntedCount` counts haunted **ordinates**, and
  `Blindness.NscStd_eq_Nsc_add_haunted` is the same identity in terms of it.
  This is the one `HauntedDensity` and every conditional route use.

Both identities subtract to the same thing, so the two counts agree — and no
lemma said so.  They have been provably equal since `181` wrote the second
identity.

This matters for `225`: `hauntedSet_card_not_ordinate_functional` and
`hauntedSet_card_determined` were stated on the `hauntedSet` side, which is not
the side the ledger's haunted row runs through.  The two corollaries below carry
them across. -/
theorem hauntedCount_eq_hauntedSet_card (D : ZeroData) :
    hauntedCount D = D.hauntedSet.card := by
  have h1 := NscStd_eq_Nsc_add_haunted D
  have h2 := ZeroData.NscStd_eq_Nsc_add_haunted D
  omega

/-- `225`'s invisibility, on the count the routes actually use. -/
theorem hauntedCount_not_ordinate_functional :
    ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, hauntedCount D = f D.ordinates := by
  rintro ⟨f, hf⟩
  exact hauntedSet_card_not_ordinate_functional
    ⟨f, fun D => by rw [← hauntedCount_eq_hauntedSet_card, hf]⟩

/-- `225`'s fiber-visibility, on the count the routes actually use. -/
theorem hauntedCount_determined {D D' : ZeroData}
    (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) :
    hauntedCount D = hauntedCount D' := by
  rw [hauntedCount_eq_hauntedSet_card, hauntedCount_eq_hauntedSet_card]
  exact hauntedSet_card_determined hord hoff

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

/-! #### What the whole moment family can and cannot compute — `SESSION 335`

`331`–`334` built the family `momentK D k` and settled its equality set.  This
asks the blindness question about the family rather than about one member: given
**every** moment at once, which of `314`'s five classes can be recovered?

**Kill condition, filed first:** *if the reduction from "computable from the
moment family" to "a functional of the ordinates" needs a choice of
representative `ZeroData` per multiset — if the witnessing `f` cannot be written
in the multiset alone — the reduction fails and the deliverable is that
obstruction, not a theorem.*  It did not fire: `momentK` unfolds to a sum of
powers of `ordinates.count`, which is a multiset expression outright.

**`moment_determined` already had the determinedness** (`SESSION 211`, in
raw-sum form, general in `k`).  What is new below is the packaging — an explicit
functional, the reduction it powers, and the five corollaries. -/

/-- **`Σm^k` in the ordinates alone.**  `momentK` is a sum of powers of
`ordinates.count`, with no reference to the `Z` multiset's real parts. -/
lemma momentK_eq_count_sum (D : ZeroData) (k : ℕ) :
    momentK D k = ∑ γ ∈ D.ordinates.toFinset, D.ordinates.count γ ^ k := by
  classical
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [D.H_eq_count]

/-- **Every moment is an ordinate functional, with the functional exhibited.**
The `∃` form is what the reduction below needs; `moment_determined` gives the
same content as an equality between two configurations sharing their ordinates. -/
theorem momentK_ordinate_functional :
    ∃ f : ℕ → Multiset ℝ → ℕ, ∀ (D : ZeroData) (k : ℕ),
      momentK D k = f k D.ordinates :=
  ⟨fun k s => ∑ γ ∈ s.toFinset, s.count γ ^ k, fun D k => momentK_eq_count_sum D k⟩

/-- **The reduction: nothing the ordinates hide is recoverable from the moments,
all of them together.**  A quantity computed by some `F` from the whole sequence
`fun k => momentK D k` is thereby a functional of `D.ordinates`, so anything
already known *not* to be an ordinate functional is not moment-computable
either. -/
theorem not_momentK_computable_of_not_ordinate_functional {q : ZeroData → ℕ}
    (hq : ¬ ∃ f : Multiset ℝ → ℕ, ∀ D : ZeroData, q D = f D.ordinates) :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, q D = F (momentK D) := by
  rintro ⟨F, hF⟩
  obtain ⟨f, hf⟩ := momentK_ordinate_functional
  exact hq ⟨fun s => F fun k => f k s, fun D => by
    rw [hF D]; exact congrArg F (funext fun k => hf D k)⟩

/-- `hauntedCount` is not computable from the moment family. -/
theorem hauntedCount_not_momentK_computable :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, hauntedCount D = F (momentK D) :=
  not_momentK_computable_of_not_ordinate_functional hauntedCount_not_ordinate_functional

/-- `oddAbove` is not computable from the moment family. -/
theorem oddAbove_not_momentK_computable :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, oddAbove D = F (momentK D) :=
  not_momentK_computable_of_not_ordinate_functional oddAbove_not_ordinate_functional

/-- `evenOnAt` is not computable from the moment family. -/
theorem evenOnAt_not_momentK_computable :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, evenOnAt D = F (momentK D) :=
  not_momentK_computable_of_not_ordinate_functional evenOnAt_not_ordinate_functional

/-- `offLineOnly` is not computable from the moment family. -/
theorem offLineOnly_not_momentK_computable :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, offLineOnly D = F (momentK D) :=
  not_momentK_computable_of_not_ordinate_functional offLineOnly_not_ordinate_functional

/-- `NscStd` is not computable from the moment family either — the ledger row the
project actually reports, not only the four gaps. -/
theorem NscStd_not_momentK_computable :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ D : ZeroData, D.NscStd = F (momentK D) :=
  not_momentK_computable_of_not_ordinate_functional NscStd_not_ordinate_functional

/-- **The positive end of the family.**  `k = 0` counts atoms.  With
`momentK_one` and `momentK_two` (`= N` and `= N⊛`), the first three moments are
`atomCount`, `N` and `N⊛`.

**`342` corrects what this said.**  It read *"exactly the three ledger counts the
ordinates already determine"*, which is wrong twice: `atomCount` is not a ledger
row, and `ZeroData.Nsc_eq_ordinate_functional` makes `N_sc` a fourth quantity the
ordinates determine.  The accurate statement is the flat one above. -/
lemma momentK_zero (D : ZeroData) : momentK D 0 = atomCount D := by
  classical
  rw [momentK, atomCount]
  simp

/-- `momentK` at `1` is `N`. -/
lemma momentK_one (D : ZeroData) : momentK D 1 = D.N := by
  classical
  rw [momentK, N_eq_sum_H]
  simp

/-! **Wildcard — is one moment ever enough for `N_sc`?**

`N_sc` *is* an ordinate functional (`Nsc_eq_ordinate_functional`), so the
reduction above says nothing against it.  The question a single moment answers is
narrower.

**Kill condition, filed first:** *if computing `momentK` and `N_sc` on a chain of
`n` simple atoms needs infrastructure the file lacks, I report the gap rather
than building it.*  It did not fire — `chain_profile`, `momentK_from_profile` and
`Nsc_from_onProfile` were all already there. -/

/-- The profile of `n` simple on-line atoms is `n` copies of `(1, 0)`. -/
lemma simple_chain_profile {a : ℝ} (ha : a ≠ 1/2) (n : ℕ) :
    profile (chain a (List.replicate n ((1 : ℕ), (0 : ℕ))))
      = Multiset.replicate n ((1 : ℕ), (0 : ℕ)) := by
  classical
  have hne : ∀ p ∈ List.replicate n ((1 : ℕ), (0 : ℕ)), p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    norm_num
  rw [chain_profile ha _ hne]
  simp [List.map_replicate, Multiset.coe_replicate]

/-- Every moment of `n` simple atoms is `n` — the mass is `1`, so `k` never
enters. -/
lemma simple_chain_momentK {a : ℝ} (ha : a ≠ 1/2) (n k : ℕ) :
    momentK (chain a (List.replicate n ((1 : ℕ), (0 : ℕ)))) k = n := by
  classical
  rw [momentK_from_profile, simple_chain_profile ha n, Multiset.map_replicate,
    Multiset.sum_replicate, smul_eq_mul]
  simp

/-- `n` simple atoms have `N_sc = n`. -/
lemma simple_chain_Nsc {a : ℝ} (ha : a ≠ 1/2) (n : ℕ) :
    (chain a (List.replicate n ((1 : ℕ), (0 : ℕ)))).Nsc = n := by
  classical
  rw [Nsc_from_onProfile, onProfile_eq_profile_map, simple_chain_profile ha n,
    Multiset.map_replicate,
    Multiset.filter_eq_self.2 (fun q hq => by
      rw [Multiset.eq_of_mem_replicate hq]; exact ⟨rfl, rfl⟩),
    Multiset.card_replicate]

/-- One pure on-line atom of mass `m` has `k`-th moment `m^k`.  The chain-level
form of `config_momentK_pure`, and it does not need `1 ≤ k`. -/
lemma pure_chain_momentK {a : ℝ} (ha : a ≠ 1/2) (m k : ℕ) (hm : m ≠ 0) :
    momentK (chain a [((m : ℕ), (0 : ℕ))]) k = m ^ k := by
  classical
  have hne : ∀ p ∈ [((m : ℕ), (0 : ℕ))], p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    simp at hp
    subst hp
    simpa using hm
  rw [momentK_from_profile, chain_profile ha _ hne]
  simp

/-- One pure on-line atom of mass at least two has `N_sc = 0`. -/
lemma pure_chain_Nsc {a : ℝ} (ha : a ≠ 1/2) (m : ℕ) (hm : 2 ≤ m) :
    (chain a [((m : ℕ), (0 : ℕ))]).Nsc = 0 := by
  classical
  have hne : ∀ p ∈ [((m : ℕ), (0 : ℕ))], p.1 + 2 * p.2 ≠ 0 := by
    intro p hp
    simp at hp
    subst hp
    omega
  rw [Nsc_from_onProfile, onProfile_eq_profile_map, chain_profile ha _ hne]
  simp
  omega

/-- **No single moment determines `N_sc`, at any `k`.**  One atom of mass two and
`2^k` simple atoms have the same `k`-th moment and `N_sc` equal to `0` and `2^k`
— the widest possible disagreement at that moment's value.

The hypothesis is on the moment's *index*, not on the configurations: for each
`k` the pair is built to collide at that `k` and nowhere else.  So this bounds
what one moment can do and says nothing about the family, which is what
`momentK_ordinate_functional` addresses. -/
theorem single_momentK_not_determine_Nsc {a : ℝ} (ha : a ≠ 1/2) (k : ℕ) :
    momentK (chain a [((2 : ℕ), (0 : ℕ))]) k
        = momentK (chain a (List.replicate (2 ^ k) ((1 : ℕ), (0 : ℕ)))) k
      ∧ (chain a [((2 : ℕ), (0 : ℕ))]).Nsc = 0
      ∧ (chain a (List.replicate (2 ^ k) ((1 : ℕ), (0 : ℕ)))).Nsc = 2 ^ k := by
  refine ⟨?_, pure_chain_Nsc ha 2 le_rfl, simple_chain_Nsc ha _⟩
  rw [pure_chain_momentK ha 2 k (by norm_num), simple_chain_momentK ha _ k]


/-! #### A multiplicity cap does not bound `N_sc` — it computes it — `SESSION 336`

`200`–`206` characterised the *unconditional* linear bounds `a·N + b·N⊛ ≤ N_sc`
by the mass test `a·m + b·m² ≤ [m = 1]` at every `m ≥ 1`, and `linearBound_iff`
showed only masses `1` and `2` bind.  Under a cap the picture changes kind: with
three counts instead of two, `N_sc` stops being bounded and becomes determined.

`Nstar_add_Nsc_eq_two_mul_N` and `boundedMult_two_iff_star_exact` are the cap-`2`
case and have been on disk since `178`-era work — two unknowns, two equations,
no `atomCount` needed.  Below are the caps at `3` and `4`.

**Kill condition, filed first:** *if the cap-`3` identity holds only under the
cap — if the corresponding pointwise inequality fails somewhere above `3` in the
wrong direction — then it is a conditional identity and not a member of this
file's inequality inventory, and I say so rather than dressing it as a bound.*
It did not fire: the pointwise gap is `(m−2)(m−3)`, so the inequality is
unconditional and the cap is exactly its equality case.  Both statements below
are therefore hypothesis-free `≤` plus an `iff`, which is `334`'s skeleton. -/

/-- `N_sc` as a `ℕ`-valued sum over the atoms.  `Nsc_eq_sum_mass_one` is the
same fact in `ℤ`; the `ℕ` form is what the sum-inequality lemmas want. -/
lemma Nsc_eq_sum_mass_one_nat (D : ZeroData) :
    D.Nsc = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then 1 else 0) := by
  classical
  have h := Nsc_eq_sum_mass_one D
  have : ((D.Nsc : ℤ)) = ((∑ γ ∈ D.ordinates.toFinset,
      (if D.H γ = 1 then 1 else 0) : ℕ) : ℤ) := by
    rw [h]
    push_cast
    exact Finset.sum_congr rfl fun γ _ => by by_cases hg : D.H γ = 1 <;> simp [hg]
  exact_mod_cast this

/-- An ordinate in the support has mass at least one.  Spelled out because
`interval_cases` needs both bounds in scope (`329`). -/
lemma one_le_H_of_mem {D : ZeroData} {γ : ℝ} (hγ : γ ∈ D.ordinates.toFinset) :
    1 ≤ D.H γ := by
  classical
  rw [D.H_eq_count γ]
  exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 hγ)

/-- The cap-`3` pointwise inequality, `2·[m = 1] + 5m ≤ m² + 6`.  The gap is
`(m−2)(m−3)`, written here as the two cases the naturals make cheap. -/
lemma cap_three_pointwise {m : ℕ} (hm : 1 ≤ m) :
    2 * (if m = 1 then 1 else 0) + 5 * m ≤ m * m + 6 := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> norm_num
  · rw [if_neg (by omega)]
    have : 5 * m ≤ m * m := Nat.mul_le_mul h le_rfl
    omega

/-- …strict from `4` up, which is the contrapositive half of the `iff`. -/
lemma cap_three_pointwise_lt {m : ℕ} (h : 4 ≤ m) :
    2 * (if m = 1 then 1 else 0) + 5 * m < m * m + 6 := by
  rw [if_neg (by omega)]
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · have hm4 : m = 4 := by omega
    subst hm4
    norm_num
  · have : 5 * m ≤ m * m := Nat.mul_le_mul h5 le_rfl
    omega

/-- **`2·N_sc + 5·N ≤ N⊛ + 6·atomCount`, for every configuration.**

Three ordinate functionals on the right, `N_sc` on the left.  Contrast
`no_NscStd_coefficient_at_three`: under the same cap `NscStd` cannot hold *any*
coefficient in a bound of that shape, while `N_sc` is pinned exactly. -/
theorem two_mul_Nsc_add_five_mul_N_le (D : ZeroData) :
    2 * D.Nsc + 5 * D.N ≤ D.Nstar + 6 * atomCount D := by
  classical
  rw [Nsc_eq_sum_mass_one_nat, N_eq_sum_H, Nstar_eq_sum_H_sq, atomCount,
    Finset.card_eq_sum_ones, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun γ hγ => by
    simpa using cap_three_pointwise (one_le_H_of_mem hγ)

/-- **…with equality exactly under a multiplicity cap of three.**  So on capped
configurations `N_sc` is not merely bounded by `atomCount`, `N` and `N⊛` — it is
*computed* by them, which is what a cap buys that no unconditional bound can.

The same hypothesis is what `Proportion.starBound_of_mult_le_three` turns into
`StarBound 1.9825` for `zetaFamily`; this is a second, exact consequence of it. -/
theorem two_mul_Nsc_eq_iff (D : ZeroData) :
    (2 * D.Nsc + 5 * D.N = D.Nstar + 6 * atomCount D)
      ↔ ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ 3 := by
  classical
  rw [Nsc_eq_sum_mass_one_nat, N_eq_sum_H, Nstar_eq_sum_H_sq, atomCount,
    Finset.card_eq_sum_ones, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  constructor
  · intro heq γ hγ
    by_contra hb
    have hlt : ∑ x ∈ D.ordinates.toFinset,
          (2 * (if D.H x = 1 then 1 else 0) + 5 * D.H x)
        < ∑ x ∈ D.ordinates.toFinset, (D.H x * D.H x + 6 * 1) := by
      refine Finset.sum_lt_sum (fun x hx => by
        simpa using cap_three_pointwise (one_le_H_of_mem hx))
        ⟨γ, hγ, by simpa using cap_three_pointwise_lt (show 4 ≤ D.H γ by omega)⟩
    omega
  · intro h
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have h1 := one_le_H_of_mem hγ
    have h3 := h γ hγ
    interval_cases hm : (D.H γ) <;> norm_num

/-- **The moment family's equality set is exactly where three moments compute
`N_sc`.**  `334` characterised the charge's equality by the cap at three; this
cycle characterises the `N_sc` identity by the same cap.  Composing them says
the two saturations are one condition, and `momentK_zero`, `momentK_one` and
`momentK_two` are the three counts on the right-hand side. -/
theorem momentK_charges_eq_iff_Nsc_computed (D : ZeroData) {k : ℕ} (hk : 2 ≤ k) :
    ((3 ^ k - 3) * hauntedCount D + (3 ^ k - 3) * oddAbove D
        + (2 ^ k - 2) * evenOnAt D + (2 ^ k - 2) * offLineOnly D
        + D.N = momentK D k)
      ↔ (2 * D.Nsc + 5 * D.N = D.Nstar + 6 * atomCount D) :=
  (momentK_charges_eq_iff D hk).trans (two_mul_Nsc_eq_iff D).symm

/-! **Wildcard — does the cap at four do the same thing, and in which
direction?**

**Kill condition, filed first:** *if the strict tail above `4` needs cubic
positivity the naturals will not give cheaply, I ship the cap-`4` identity as a
conditional one and record that the unconditional form was not reached.*  It did
not fire — substituting `m = j + 5` turns the gap `(m−2)(m−3)(m−4)` into
`(j+1)(j+2)(j+3)`, a sum of positive terms with no subtraction anywhere. -/

/-- The cap-`4` pointwise inequality.  Note the **direction**: the odd-degree gap
`(m−2)(m−3)(m−4)` is positive above `4`, so the sides swap relative to the
cap-`3` statement. -/
lemma cap_four_pointwise {m : ℕ} (hm : 1 ≤ m) :
    9 * (m * m) + 24 * 1 ≤ 6 * (if m = 1 then 1 else 0) + m * m * m + 26 * m := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> norm_num
  · rw [if_neg (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
    have key : (j + 5) * (j + 5) * (j + 5) + 26 * (j + 5)
        = 9 * ((j + 5) * (j + 5)) + 24 * 1
          + (j * j * j + 6 * (j * j) + 11 * j + 6) := by ring
    omega

/-- …strict from `5` up. -/
lemma cap_four_pointwise_lt {m : ℕ} (h : 5 ≤ m) :
    9 * (m * m) + 24 * 1 < 6 * (if m = 1 then 1 else 0) + m * m * m + 26 * m := by
  rw [if_neg (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  have key : (j + 5) * (j + 5) * (j + 5) + 26 * (j + 5)
      = 9 * ((j + 5) * (j + 5)) + 24 * 1
        + (j * j * j + 6 * (j * j) + 11 * j + 6) := by ring
  omega

/-- **`9·N⊛ + 24·atomCount ≤ 6·N_sc + Σm³ + 26·N`, for every configuration** —
the cap-`4` bound, with `N_sc` now on the *large* side. -/
theorem nine_mul_Nstar_add_atomCount_le (D : ZeroData) :
    9 * D.Nstar + 24 * atomCount D ≤ 6 * D.Nsc + thirdMoment D + 26 * D.N := by
  classical
  rw [Nsc_eq_sum_mass_one_nat, N_eq_sum_H, Nstar_eq_sum_H_sq, thirdMoment,
    atomCount, Finset.card_eq_sum_ones, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun γ hγ => cap_four_pointwise (one_le_H_of_mem hγ)

/-- **…with equality exactly under a multiplicity cap of four.**  So the cap at
`m` computes `N_sc` from the first `m` moments, and the direction of the bound
that surrounds it alternates with `m`: at `3` the identity's `N_sc` side is the
small one, at `4` it is the large one.  Only two rungs are witnessed here, so the
alternation is stated for `3` and `4` and not for general `m`. -/
theorem nine_mul_Nstar_add_atomCount_eq_iff (D : ZeroData) :
    (9 * D.Nstar + 24 * atomCount D = 6 * D.Nsc + thirdMoment D + 26 * D.N)
      ↔ ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ 4 := by
  classical
  rw [Nsc_eq_sum_mass_one_nat, N_eq_sum_H, Nstar_eq_sum_H_sq, thirdMoment,
    atomCount, Finset.card_eq_sum_ones, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  constructor
  · intro heq γ hγ
    by_contra hb
    have hlt := Finset.sum_lt_sum
      (fun x (hx : x ∈ D.ordinates.toFinset) =>
        cap_four_pointwise (one_le_H_of_mem hx))
      ⟨γ, hγ, cap_four_pointwise_lt (show 5 ≤ D.H γ by omega)⟩
    omega
  · intro h
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have h1 := one_le_H_of_mem hγ
    have h4 := h γ hγ
    interval_cases hm : (D.H γ) <;> norm_num


/-! #### The cap identity at every bound — `SESSION 344`

`336` proved two cap identities, at mass `≤ 3` and mass `≤ 4`, and said in its own
entry that they were *"stated for `3` and `4` and for no general `m`"*.  This is
the general one.

The shape is Lagrange interpolation: on `{1, …, b+1}` the indicator of `m = 1` is
`∏_{j=2}^{b+1} (m − j)` divided by its value at `m = 1`, which is
`(−1)^b · b!`.  So summing that product over the atoms counts `N_sc` up to that
factor — and it needs no expansion into moments to state.

**Kill condition, filed first:** *if the general form needs the product expanded
into moments to be worth stating, I ship the product form and say plainly that the
expansion is not proved.*  It did not fire in the sense that the product form is a
complete statement, and it **did** fire in the sense the condition anticipated:
the expansion into `momentK 0 … momentK b` is real content and is not in this
section — **`345` proved it**, by a coefficient recursion rather than the
elementary symmetric polynomials named here, in `capWitness_eq_sum_moments` and
`Nsc_from_moments` further down.  What is below is the product identity.

`336`'s two rows are the `b = 2` and `b = 3` cases.  Both were checked against it
in scratch: `∑ (H−2)(H−3) = 2·N_sc` expands to
`Riemann.Blindness.two_mul_Nsc_eq_iff`'s equality and
`∑ (H−2)(H−3)(H−4) = −6·N_sc` to
`Riemann.Blindness.nine_mul_Nstar_add_atomCount_eq_iff`'s.  Neither is restated
here, because a second proof of a shipped conclusion is what `duplication_floor`
exists to stop (`256`). -/

/-- The falling product `∏_{j=2}^{b+1} (H γ − j)`, summed over the atoms.  Written
over `Finset.range b` with the shift `i ↦ i + 2` so that nothing subtracts in `ℕ`. -/
noncomputable def capWitness (D : ZeroData) (b : ℕ) : ℤ :=
  ∑ γ ∈ D.ordinates.toFinset, ∏ i ∈ Finset.range b, ((D.H γ : ℤ) - (i + 2))

/-- The pointwise interpolation: on a mass in `[1, b+1]` the product is
`(−1)^b · b!` at mass one and `0` at every other admissible mass, because the
factor at `j = m` vanishes. -/
lemma cap_pointwise {m b : ℕ} (h1 : 1 ≤ m) (hb : m ≤ b + 1) :
    ∏ i ∈ Finset.range b, ((m : ℤ) - (i + 2))
      = if m = 1 then (-1) ^ b * (Nat.factorial b : ℤ) else 0 := by
  by_cases hm : m = 1
  · subst hm
    rw [if_pos rfl]
    have key : ∏ i ∈ Finset.range b, (((1 : ℕ) : ℤ) - (i + 2))
        = ∏ i ∈ Finset.range b, (-((i : ℤ) + 1)) :=
      Finset.prod_congr rfl fun i _ => by push_cast; ring
    rw [key, Finset.prod_neg, Finset.card_range]
    congr 1
    have hfac : ((Nat.factorial b : ℕ) : ℤ) = ∏ i ∈ Finset.range b, ((i : ℤ) + 1) := by
      rw [Nat.factorial_eq_prod_range_add_one]
      push_cast
      rfl
    exact hfac.symm
  · rw [if_neg hm]
    refine Finset.prod_eq_zero (i := m - 2) ?_ ?_
    · rw [Finset.mem_range]; omega
    · have hc : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by
        have h2 : 2 ≤ m := by omega
        push_cast [Nat.cast_sub h2]; ring
      rw [hc]; ring

/-- **`N_sc` from the falling product, under a multiplicity cap at `b + 1`.**

`capWitness D b = (−1)^b · b! · N_sc` whenever every ordinate has mass at most
`b + 1`.  `b = 2` and `b = 3` are `336`'s two identities after expanding the
product; the general expansion is `capWitness_eq_sum_moments` (`345`). -/
theorem capWitness_eq (D : ZeroData) {b : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ b + 1) :
    capWitness D b = (-1) ^ b * (Nat.factorial b : ℤ) * (D.Nsc : ℤ) := by
  classical
  have hNsc : (D.Nsc : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then (1 : ℤ) else 0) := by
    have hn := Nsc_eq_sum_mass_one_nat D
    rw [hn]
    push_cast
    exact Finset.sum_congr rfl fun γ _ => by by_cases hg : D.H γ = 1 <;> simp [hg]
  rw [capWitness, hNsc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [cap_pointwise (one_le_H_of_mem hγ) (h γ hγ)]
  by_cases hg : D.H γ = 1 <;> simp [hg]

/-- `capWitness` through the profile, the same one-liner as `momentK_from_profile`
— which is what makes it computable on a `chain`. -/
lemma capWitness_from_profile (D : ZeroData) (b : ℕ) :
    capWitness D b
      = ((profile D).map fun q => ∏ i ∈ Finset.range b, ((q.1 : ℤ) - (i + 2))).sum := by
  classical
  rw [capWitness, profile, Multiset.map_map]
  rfl

/-- **The cap is doing work: one atom above it breaks the identity.**  At `b = 2`
the identity reads `capWitness D 2 = 2·N_sc`; a single pure on-line atom of mass
four has `capWitness = 2` and `N_sc = 0`.

This is a strictness witness, not a converse: it shows the hypothesis of
`capWitness_eq` cannot simply be dropped, and says nothing about which
configurations above the cap happen to satisfy the identity anyway. -/
theorem capWitness_needs_the_cap {a : ℝ} (ha : a ≠ 1/2) :
    capWitness (chain a [((4 : ℕ), (0 : ℕ))]) 2 = 2
      ∧ (chain a [((4 : ℕ), (0 : ℕ))]).Nsc = 0 := by
  classical
  have hne : ∀ p ∈ [((4 : ℕ), (0 : ℕ))], p.1 + 2 * p.2 ≠ 0 := by
    intro p hp; simp at hp; subst hp; norm_num
  refine ⟨?_, pure_chain_Nsc ha 4 (by norm_num)⟩
  rw [capWitness_from_profile, chain_profile ha _ hne]
  simp [Finset.prod_range_succ]


/-! #### The expansion `344` left open — `SESSION 345`

`344` proved `capWitness_eq` and said the expansion of its falling product into
`momentK 0 … momentK b` was not proved, naming elementary symmetric polynomials as
what it would need.  It does not need them.  The coefficients satisfy a two-term
recursion in `b`, and an induction on `b` gives the polynomial identity directly.

**Kill condition, filed first:** *if the induction on the coefficient shift does
not go through cheaply, I ship the sum-swap bridge alone and say the
polynomial-existence half is open.*  It did not fire, and what made it go through
is `capCoeff_eq_zero_of_gt`: the reindexing step reassembles the previous
polynomial only after the phantom top coefficient is killed, so the vanishing
lemma is load-bearing rather than decorative.

**What is proved and what is not.**  The coefficients are *characterised by the
recursion*; the identification of `capCoeff b k` with a signed elementary symmetric
function of `{2, …, b+1}` is **not** proved here and is not needed for anything
below.  `capCoeff` is computable, so its values are `decide`-checkable —
`capCoeff 2` is `(6, −5, 1)` and `capCoeff 3` is `(−24, 26, −9, 1)`, which are
`336`'s two shipped constants; both checked in scratch and not restated here
(`256`). -/

/-- The coefficients of `∏_{j=2}^{b+1}(x − j)` in `x`, by recursion on `b`:
multiplying by `(x − (b+2))` shifts the previous coefficients up one and subtracts
`(b+2)` times them. -/
def capCoeff : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | b + 1, 0 => -((b : ℤ) + 2) * capCoeff b 0
  | b + 1, k + 1 => capCoeff b k - ((b : ℤ) + 2) * capCoeff b (k + 1)

/-- Above the degree there is nothing.  Load-bearing in `capCoeff_prod`: the
induction step reassembles the previous polynomial only once the phantom
coefficient at `k = b + 1` is known to vanish. -/
lemma capCoeff_eq_zero_of_gt : ∀ b k : ℕ, b < k → capCoeff b k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | b + 1, 0, h => absurd h (by omega)
  | b + 1, k + 1, h => by
      rw [capCoeff]
      rw [capCoeff_eq_zero_of_gt b k (by omega),
        capCoeff_eq_zero_of_gt b (k + 1) (by omega)]
      ring

/-- **The falling product is a polynomial with those coefficients.**  Induction on
`b`; the step is one reindex of the sum and the vanishing lemma. -/
lemma capCoeff_prod (b : ℕ) (x : ℤ) :
    ∏ i ∈ Finset.range b, (x - ((i : ℤ) + 2))
      = ∑ k ∈ Finset.range (b + 1), capCoeff b k * x ^ k := by
  induction b with
  | zero => simp [capCoeff]
  | succ b ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Finset.sum_range_succ' (fun k => capCoeff (b + 1) k * x ^ k) (b + 1)]
      have hzero : capCoeff b (b + 1) = 0 :=
        capCoeff_eq_zero_of_gt b (b + 1) (by omega)
      have hshift : ∑ j ∈ Finset.range (b + 1), capCoeff b (j + 1) * x ^ (j + 1)
          = ∑ j ∈ Finset.range b, capCoeff b (j + 1) * x ^ (j + 1) := by
        rw [Finset.sum_range_succ, hzero]
        ring
      have hre : ∑ k ∈ Finset.range (b + 1), capCoeff b k * x ^ k
          = (∑ j ∈ Finset.range b, capCoeff b (j + 1) * x ^ (j + 1))
            + capCoeff b 0 * x ^ 0 :=
        Finset.sum_range_succ' (fun k => capCoeff b k * x ^ k) b
      simp only [capCoeff]
      set A := ∑ k ∈ Finset.range (b + 1), capCoeff b k * x ^ k with hA
      set B := ∑ k ∈ Finset.range (b + 1), capCoeff b k * x ^ (k + 1) with hB
      set C := ∑ k ∈ Finset.range (b + 1), capCoeff b (k + 1) * x ^ (k + 1) with hC
      set D := ∑ j ∈ Finset.range b, capCoeff b (j + 1) * x ^ (j + 1) with hD
      have hAx : A * x = B := by
        rw [hA, hB, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
      have hsplit : ∑ k ∈ Finset.range (b + 1),
            (capCoeff b k - ((b : ℤ) + 2) * capCoeff b (k + 1)) * x ^ (k + 1)
          = B - ((b : ℤ) + 2) * C := by
        rw [hB, hC, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit]
      have hCD : C = D := hshift
      have hAD : A = D + capCoeff b 0 * x ^ 0 := hre
      have hexp : A * (x - ((b : ℤ) + 2)) = A * x - ((b : ℤ) + 2) * A := by ring
      rw [hexp, hAx, hAD, hCD]
      ring

/-- `momentK` in `ℤ`, as a sum over the atoms. -/
lemma momentK_cast (D : ZeroData) (k : ℕ) :
    ((momentK D k : ℕ) : ℤ) = ∑ γ ∈ D.ordinates.toFinset, ((D.H γ : ℤ)) ^ k := by
  rw [momentK]; push_cast; rfl

/-- **`capWitness` in the moments, with no hypothesis at all.**  The cap is needed
only to identify the left side with `N_sc`; the expansion itself is a sum swap. -/
theorem capWitness_eq_sum_moments (D : ZeroData) (b : ℕ) :
    capWitness D b
      = ∑ k ∈ Finset.range (b + 1), capCoeff b k * ((momentK D k : ℕ) : ℤ) := by
  classical
  rw [capWitness, Finset.sum_congr rfl fun γ _ => capCoeff_prod b ((D.H γ : ℤ)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [momentK_cast, Finset.mul_sum]

/-- **`N_sc` as a `ℤ`-combination of the first `b + 1` moments, under a cap at
`b + 1`.**  This is what `344` left open, and `336`'s two identities are `b = 2`
and `b = 3` of it. -/
theorem Nsc_from_moments (D : ZeroData) {b : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ b + 1) :
    (-1) ^ b * (Nat.factorial b : ℤ) * (D.Nsc : ℤ)
      = ∑ k ∈ Finset.range (b + 1), capCoeff b k * ((momentK D k : ℕ) : ℤ) :=
  (capWitness_eq D h).symm.trans (capWitness_eq_sum_moments D b)

/-- **Under a cap, the moments up to the cap determine `N_sc`.**

`335` filed the uncapped question — whether the whole moment sequence determines
`N_sc` — as open, and `Riemann.Blindness.single_momentK_not_determine_Nsc` showed
that no single moment suffices, at any `k`.  This is the capped answer: at a cap of `b + 1`, agreement on
`momentK k` for `k ≤ b` forces equal `N_sc`.  The **uncapped** question is
untouched by this. -/
theorem Nsc_determined_by_moments_of_cap {D D' : ZeroData} {b : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ b + 1)
    (h' : ∀ γ ∈ D'.ordinates.toFinset, D'.H γ ≤ b + 1)
    (hm : ∀ k, k ≤ b → momentK D k = momentK D' k) :
    D.Nsc = D'.Nsc := by
  have hsum : ∑ k ∈ Finset.range (b + 1), capCoeff b k * ((momentK D k : ℕ) : ℤ)
      = ∑ k ∈ Finset.range (b + 1), capCoeff b k * ((momentK D' k : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun k hk => by
      rw [hm k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
  have key : ((-1 : ℤ) ^ b * (Nat.factorial b : ℤ)) * (D.Nsc : ℤ)
      = ((-1 : ℤ) ^ b * (Nat.factorial b : ℤ)) * (D'.Nsc : ℤ) := by
    rw [Nsc_from_moments D h, Nsc_from_moments D' h', hsum]
  have hne : ((-1 : ℤ) ^ b * (Nat.factorial b : ℤ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero b)
  exact_mod_cast mul_left_cancel₀ hne key


/-! #### The moment sequence and the ledger's own row — `SESSION 347`

`346` proved the whole moment sequence determines `N_sc`.  `335` proved no function
of the sequence computes `NscStd`, in the `¬∃ F` form.  Those are different
currencies: one is determinacy, the other is non-computability, and `¬∃ F` follows
from a separating pair rather than exhibiting one.

Below is the pair, which puts both sides of the comparison into determinacy form.

**Kill condition, filed first:** *if a separating pair for `NscStd` in this currency
is already on disk, the deliverable is the pointer.*  Searched
`statement_index --find 'not_determined_by_all_moments|momentK_determined|not_determined_by'`
and read all seven rows: the `_not_determined_by_ledger` family separates
quantities from the **five ledger counts**, which is a different hypothesis, and
none of them is about the moment sequence.  It did not fire.

**The witness is `X`'s founding example.**  `haunted_indistinguishable_from_triple`
has said since the `170`s that a haunted ordinate and a pure triple share their
ordinates; `momentK_eq_count_sum` turns that into identical moment sequences at
every `k`.  So the configuration pair that motivated the blindness
programme is one the moment family does not separate, which is what
`Riemann.Blindness.NscStd_not_determined_by_all_moments` below records. -/

/-- **The moment sequence does not determine `NscStd`.**  A haunted ordinate
(`configAt 0 1 1 a`) and a pure on-line triple (`configAt 0 3 0 a`) have equal
`momentK` at every `k`, and `NscStd` equal to `1` and `0`.

Contrast `Riemann.Optimal.Nsc_determined_by_all_moments`, which says the same
sequence *does* determine `N_sc` — and the difference between the two rows is
`hauntedCount`, which is `1` on the left configuration and `0` on the right. -/
theorem NscStd_not_determined_by_all_moments {a : ℝ} (ha : a ≠ 1/2) :
    (∀ k, momentK (configAt 0 1 1 a) k = momentK (configAt 0 3 0 a) k)
      ∧ (configAt 0 1 1 a).NscStd = 1 ∧ (configAt 0 3 0 a).NscStd = 0 := by
  classical
  refine ⟨fun k => ?_, (haunted_atom_counts ha).1, ?_⟩
  · rw [momentK_eq_count_sum, momentK_eq_count_sum,
      haunted_indistinguishable_from_triple (a := a)]
  · rw [← config_eq_configAt, config_NscStd 3 0 ha]
    norm_num

/-- **`346` checked against the pair that breaks `NscStd`.**
`Riemann.Optimal.Nsc_determined_by_all_moments` requires the two `N_sc` values to
agree here, since the moment sequences agree.  They do: both are `0`.

This is a test of that theorem rather than a new fact about the configurations — had
the values differed, `346` would have been refuted rather than illustrated. -/
theorem Nsc_agrees_on_the_moment_blind_pair {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 1 a).Nsc = 0 ∧ (configAt 0 3 0 a).Nsc = 0 := by
  classical
  refine ⟨(haunted_atom_counts ha).2.1, ?_⟩
  have hp := configAt_profile (γ := (0:ℝ)) ha (k := 3) (j := 0) (by norm_num)
  norm_num at hp
  rw [Nsc_from_onProfile, onProfile_eq_profile_map, hp]
  norm_num


/-! #### The recovery `347` left unproved — `SESSION 348`

`347`'s might-mean was weakened at the last moment because it assumed a converse:
that equal moment sequences force equal mass data.  That converse is the classical
Newton recovery, and it is proved below — for the **mass counts**, which is the part
the moment family can reach.

Three pieces of reusable machinery, then the theorem.

**Kill condition, filed first:** *if the general expansion over an arbitrary finset
does not go through this cycle, I ship the pointwise interpolation and state the
determinacy as blocked on the expansion.*  It did not fire.  `345`'s reindexing
argument generalises once the coefficient function carries its own vanishing
condition inside the existential — the obstruction `345` met as
`capCoeff_eq_zero_of_gt`, in a form that travels.

**What this does *not* say.**  Equal moments do not force equal ordinates: heights
are invisible to every count in this file (`ledger_relabel_invariant`).  What is
recovered is the multiset of masses, one count at a time. -/

/-- **Any product of monic linear factors is a polynomial**, with coefficients
vanishing above the degree.  Existence only — no formula, and none needed: the
determinacy argument uses the coefficients only through a sum swap.

The vanishing clause is carried *inside* the existential deliberately.  Without it
the induction step cannot reassemble the previous polynomial — the same obstruction
`345` met as `capCoeff_eq_zero_of_gt`. -/
lemma exists_poly_of_prod (c : ℕ → ℤ) : ∀ s : Finset ℕ,
    ∃ (n : ℕ) (a : ℕ → ℤ), (∀ k, n ≤ k → a k = 0) ∧
      ∀ x : ℤ, ∏ i ∈ s, (x - c i) = ∑ k ∈ Finset.range n, a k * x ^ k := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, fun k => if k = 0 then 1 else 0, ?_, ?_⟩
      · intro k hk
        dsimp only
        rw [if_neg (by omega)]
      · intro x; simp
  | insert j t hj ih =>
      obtain ⟨n, a, hvan, hpoly⟩ := ih
      refine ⟨n + 1, fun k => (if k = 0 then 0 else a (k - 1)) - c j * a k, ?_, ?_⟩
      · intro k hk
        dsimp only
        rw [if_neg (by omega), hvan (k - 1) (by omega), hvan k (by omega)]
        ring
      · intro x
        rw [Finset.prod_insert hj, hpoly x]
        have hA : ∑ k ∈ Finset.range (n + 1),
              ((if k = 0 then 0 else a (k - 1)) - c j * a k) * x ^ k
            = (∑ k ∈ Finset.range (n + 1), (if k = 0 then 0 else a (k - 1)) * x ^ k)
              - ∑ k ∈ Finset.range (n + 1), (c j * a k) * x ^ k := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hA]
        have h1 : ∑ k ∈ Finset.range (n + 1), (if k = 0 then 0 else a (k - 1)) * x ^ k
            = ∑ i ∈ Finset.range n, a i * x ^ (i + 1) := by
          rw [Finset.sum_range_succ' (fun k => (if k = 0 then 0 else a (k - 1)) * x ^ k) n]
          simp
        have h2 : ∑ k ∈ Finset.range (n + 1), (c j * a k) * x ^ k
            = c j * ∑ k ∈ Finset.range n, a k * x ^ k := by
          rw [Finset.sum_range_succ, hvan n le_rfl, Finset.mul_sum]
          simp only [mul_zero, zero_mul, add_zero]
          exact Finset.sum_congr rfl fun k _ => by ring
        have h3 : ∑ i ∈ Finset.range n, a i * x ^ (i + 1)
            = (∑ k ∈ Finset.range n, a k * x ^ k) * x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
        rw [h1, h2, h3]
        ring

/-- How many ordinates carry mass exactly `j`.  `massCount_one` below identifies
`massCount D 1` with `N_sc`. -/
noncomputable def massCount (D : ZeroData) (j : ℕ) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => D.H γ = j).card

/-- `massCount` at `1` is `N_sc`. -/
lemma massCount_one (D : ZeroData) : massCount D 1 = D.Nsc := by
  classical
  rw [massCount, Nsc_eq_sum_mass_one_nat, ← Finset.sum_filter]
  simp

/-- **The bridge, for any `ℕ`-valued weight on the atoms.**  `SESSION 349`
generalised this from the `H`-only form below, because the on-line count needs the
same argument and copying it would have been a second proof of one sum swap. -/
lemma sum_prod_eq_sum_weight_moments (D : ZeroData) (w : ℝ → ℕ)
    (s : Finset ℕ) (c : ℕ → ℤ) {n : ℕ} {a : ℕ → ℤ}
    (hpoly : ∀ x : ℤ, ∏ i ∈ s, (x - c i) = ∑ k ∈ Finset.range n, a k * x ^ k) :
    ∑ γ ∈ D.ordinates.toFinset, ∏ i ∈ s, ((w γ : ℤ) - c i)
      = ∑ k ∈ Finset.range n,
          a k * ∑ γ ∈ D.ordinates.toFinset, ((w γ : ℤ)) ^ k := by
  classical
  rw [Finset.sum_congr rfl fun γ _ => hpoly ((w γ : ℤ)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

/-- **Any such product, summed over the atoms, is a `ℤ`-combination of moments.**
The abstract form of `capWitness_eq_sum_moments`: the coefficients are whatever the
expansion supplies, and the proof is one sum swap. -/
lemma sum_prod_eq_sum_moments (D : ZeroData) (s : Finset ℕ) (c : ℕ → ℤ)
    {n : ℕ} {a : ℕ → ℤ}
    (hpoly : ∀ x : ℤ, ∏ i ∈ s, (x - c i) = ∑ k ∈ Finset.range n, a k * x ^ k) :
    ∑ γ ∈ D.ordinates.toFinset, ∏ i ∈ s, ((D.H γ : ℤ) - c i)
      = ∑ k ∈ Finset.range n, a k * ((momentK D k : ℕ) : ℤ) := by
  rw [sum_prod_eq_sum_weight_moments D (fun γ => D.H γ) s c hpoly]
  exact Finset.sum_congr rfl fun k _ => by rw [momentK_cast]

/-- The interpolation at a general node: erasing `j` from `{1, …, B}` gives a product
that vanishes at every other admissible mass. -/
lemma node_prod_pointwise {m j B : ℕ} (h1 : 1 ≤ m) (hB : m ≤ B) :
    ∏ i ∈ (Finset.Icc 1 B).erase j, ((m : ℤ) - (i : ℤ))
      = if m = j then ∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ)) else 0 := by
  classical
  by_cases hm : m = j
  · rw [if_pos hm, hm]
  · rw [if_neg hm]
    refine Finset.prod_eq_zero (i := m) ?_ (by ring)
    exact Finset.mem_erase.2 ⟨hm, Finset.mem_Icc.2 ⟨h1, hB⟩⟩

/-- …and the normalising constant is nonzero, because every erased factor is. -/
lemma node_const_ne_zero {j B : ℕ} :
    ∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ)) ≠ 0 := by
  classical
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.1 hi).1
  intro hz
  exact hij (by exact_mod_cast (sub_eq_zero.1 hz).symm)

/-- **The node sum counts one mass.**  Under a cap at `B`, the erased product summed
over the atoms is the normalising constant times `massCount D j`. -/
theorem node_sum_eq (D : ZeroData) {j B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ B) :
    ∑ γ ∈ D.ordinates.toFinset, ∏ i ∈ (Finset.Icc 1 B).erase j,
        ((D.H γ : ℤ) - (i : ℤ))
      = (∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ)))
        * (massCount D j : ℤ) := by
  classical
  have hstep : ∀ γ ∈ D.ordinates.toFinset,
      ∏ i ∈ (Finset.Icc 1 B).erase j, ((D.H γ : ℤ) - (i : ℤ))
        = if D.H γ = j then ∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ))
          else 0 :=
    fun γ hγ => node_prod_pointwise (one_le_H_of_mem hγ) (h γ hγ)
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, massCount]
  ring

/-- **Under a common cap, the moments determine every mass count.**  Newton's
recovery in this vocabulary.  The coefficients come from `exists_poly_of_prod` and
are used only through a sum swap, so no formula for them appears in the proof. -/
theorem massCount_determined_of_cap {D D' : ZeroData} {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ B)
    (h' : ∀ γ ∈ D'.ordinates.toFinset, D'.H γ ≤ B)
    (hm : ∀ k, momentK D k = momentK D' k) (j : ℕ) :
    massCount D j = massCount D' j := by
  classical
  obtain ⟨n, a, hvan, hpoly⟩ :=
    exists_poly_of_prod (fun i => (i : ℤ)) ((Finset.Icc 1 B).erase j)
  have e1 := node_sum_eq D (j := j) h
  have e2 := node_sum_eq D' (j := j) h'
  have b1 := sum_prod_eq_sum_moments D ((Finset.Icc 1 B).erase j)
    (fun i => (i : ℤ)) hpoly
  have b2 := sum_prod_eq_sum_moments D' ((Finset.Icc 1 B).erase j)
    (fun i => (i : ℤ)) hpoly
  have hsum : ∑ k ∈ Finset.range n, a k * ((momentK D k : ℕ) : ℤ)
      = ∑ k ∈ Finset.range n, a k * ((momentK D' k : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun k _ => by rw [hm k]
  have key : (∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ)))
        * (massCount D j : ℤ)
      = (∏ i ∈ (Finset.Icc 1 B).erase j, ((j : ℤ) - (i : ℤ)))
        * (massCount D' j : ℤ) := by
    rw [← e1, ← e2, b1, b2, hsum]
  exact_mod_cast mul_left_cancel₀ node_const_ne_zero key


/-! #### What would suffice: the on-line moments — `SESSION 349`

`348` closed the moment arc with a boundary: the moment sequence in `H` pins every
mass count and cannot reach `NscStd` (`347`'s pair).  That says what is missing
negatively.  This says it positively — **the same machinery, run on `onAt` instead of
`H`, determines `NscStd`.**

So what a theory would need is not more moments of the multiplicity but the first few
moments of the *on-line* count.  That is not a route: `onAt` is not a `μ_T`
functional, which is what `X` has said since the beginning.  What it does is name the
missing datum exactly, in the same currency the negative result is stated in.

**Kill condition, filed first:** *if `NscStd` is not already the count of ordinates
with `onAt = 1` on disk, I report the reduction and stop rather than proving a new
characterisation.*  It did not fire — `NscStd_eq_onAt_one` has been on disk since the
fiber work.

The node set here is `range (B+1)` rather than `348`'s `Icc 1 B`, because `onAt` can
be `0`: an ordinate carrying only off-line zeros contributes nothing on the line. -/

/-- How many ordinates have on-line count exactly `n`. -/
noncomputable def onCount (D : ZeroData) (n : ℕ) : ℕ :=
  (D.ordinates.toFinset.filter fun γ => onAt D γ = n).card

/-- The `p`-th moment of the on-line count. -/
noncomputable def onMoment (D : ZeroData) (p : ℕ) : ℕ :=
  ∑ γ ∈ D.ordinates.toFinset, onAt D γ ^ p

/-- `onMoment` in `ℤ`. -/
lemma onMoment_cast (D : ZeroData) (p : ℕ) :
    ((onMoment D p : ℕ) : ℤ)
      = ∑ γ ∈ D.ordinates.toFinset, ((onAt D γ : ℤ)) ^ p := by
  rw [onMoment]; push_cast; rfl

/-- `348`'s node interpolation over `{0, …, B}`, which is the range `onAt` lives in. -/
lemma node_prod_pointwise_range {m n B : ℕ} (hB : m ≤ B) :
    ∏ i ∈ (Finset.range (B + 1)).erase n, ((m : ℤ) - (i : ℤ))
      = if m = n then
          ∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)) else 0 := by
  classical
  by_cases hm : m = n
  · rw [if_pos hm, hm]
  · rw [if_neg hm]
    refine Finset.prod_eq_zero (i := m) ?_ (by ring)
    exact Finset.mem_erase.2 ⟨hm, Finset.mem_range.2 (by omega)⟩

/-- …with a nonzero normalising constant, for the same reason. -/
lemma node_const_range_ne_zero {n B : ℕ} :
    ∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)) ≠ 0 := by
  classical
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hin : i ≠ n := (Finset.mem_erase.1 hi).1
  intro hz
  exact hin (by exact_mod_cast (sub_eq_zero.1 hz).symm)

/-- The node sum counts one on-line value. -/
theorem on_node_sum_eq (D : ZeroData) {n B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ≤ B) :
    ∑ γ ∈ D.ordinates.toFinset,
        ∏ i ∈ (Finset.range (B + 1)).erase n, ((onAt D γ : ℤ) - (i : ℤ))
      = (∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)))
        * (onCount D n : ℤ) := by
  classical
  have hstep : ∀ γ ∈ D.ordinates.toFinset,
      ∏ i ∈ (Finset.range (B + 1)).erase n, ((onAt D γ : ℤ) - (i : ℤ))
        = if onAt D γ = n then
            ∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)) else 0 :=
    fun γ hγ => node_prod_pointwise_range (h γ hγ)
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, onCount]
  ring

/-- **Under a common cap, the on-line moments determine every on-line count.**
`348`'s argument with `onAt` in place of `H`, through the weighted bridge. -/
theorem onCount_determined_of_cap {D D' : ZeroData} {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ≤ B)
    (h' : ∀ γ ∈ D'.ordinates.toFinset, onAt D' γ ≤ B)
    (hm : ∀ p, onMoment D p = onMoment D' p) (n : ℕ) :
    onCount D n = onCount D' n := by
  classical
  obtain ⟨m, a, hvan, hpoly⟩ :=
    exists_poly_of_prod (fun i => (i : ℤ)) ((Finset.range (B + 1)).erase n)
  have e1 := on_node_sum_eq D (n := n) h
  have e2 := on_node_sum_eq D' (n := n) h'
  have b1 := sum_prod_eq_sum_weight_moments D (fun γ => onAt D γ)
    ((Finset.range (B + 1)).erase n) (fun i => (i : ℤ)) hpoly
  have b2 := sum_prod_eq_sum_weight_moments D' (fun γ => onAt D' γ)
    ((Finset.range (B + 1)).erase n) (fun i => (i : ℤ)) hpoly
  have hsum : ∑ k ∈ Finset.range m,
        a k * ∑ γ ∈ D.ordinates.toFinset, ((onAt D γ : ℤ)) ^ k
      = ∑ k ∈ Finset.range m,
        a k * ∑ γ ∈ D'.ordinates.toFinset, ((onAt D' γ : ℤ)) ^ k :=
    Finset.sum_congr rfl fun k _ => by
      rw [← onMoment_cast, ← onMoment_cast, hm k]
  have key : (∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)))
        * (onCount D n : ℤ)
      = (∏ i ∈ (Finset.range (B + 1)).erase n, ((n : ℤ) - (i : ℤ)))
        * (onCount D' n : ℤ) := by
    rw [← e1, ← e2, b1, b2, hsum]
  exact_mod_cast mul_left_cancel₀ node_const_range_ne_zero key

/-- The ledger's reported row is the `onAt = 1` count. -/
lemma NscStd_eq_onCount_one (D : ZeroData) : D.NscStd = onCount D 1 := by
  rw [onCount, NscStd_eq_onAt_one]


/-! #### The two families and the two rows — `SESSION 350`

`348`: the `H`-moments pin every mass count, and `347`'s pair shows they do not reach
`NscStd`.  `349`: the `onAt`-moments reach `NscStd`.  The question this leaves is
whether the on-line family reaches the *other* ledger row, and it does not.

**Each family sees one of the two rows and misses the other**, and the two witnesses
are the two smallest interesting configurations: `347` used a haunted ordinate against
a pure triple, and this uses a haunted ordinate against a *simple* one.

**Kill condition, filed first:** *if the on-moment values on these two single-atom
configurations are not computable from lemmas on disk, I report the reduction and stop
rather than building configuration infrastructure.*  It did not fire —
`configAt_profile` and `onProfile_eq_profile_map` give both, once `onMoment` is
expressed through the profile.

**This also pays a debt from `349`.**  That cycle's docstring asserted that the
on-line moments do not determine `N`, with no witness.  The same pair witnesses it:
`N` is `1` and `3`. -/

/-- `onMoment` through the profile — the analogue of `momentK_from_profile`, and what
makes it computable on the small configurations. -/
lemma onMoment_from_onProfile (D : ZeroData) (p : ℕ) :
    onMoment D p = ((onProfile D).map fun q => q.1 ^ p).sum := by
  classical
  rw [onMoment, onProfile, Multiset.map_map]
  rfl

/-- **The on-line moments do not determine `N_sc`, nor `N`.**  A simple on-line atom
and a haunted ordinate both have on-line count `1` at their one ordinate, so every
`onMoment` agrees; `N_sc` is `1` and `0`, and `N` is `1` and `3`.

With `Riemann.Optimal.NscStd_determined_by_on_moments` this is the mirror of `347`:
the `H`-family determines `N_sc` and not `NscStd`, the `onAt`-family determines
`NscStd` and not `N_sc`.  Note both configurations have `NscStd = 1`, which `349`
requires of any pair with equal on-moments. -/
theorem Nsc_not_determined_by_on_moments {a : ℝ} (ha : a ≠ 1/2) :
    (∀ p, onMoment (configAt 0 1 0 a) p = onMoment (configAt 0 1 1 a) p)
      ∧ (configAt 0 1 0 a).Nsc = 1 ∧ (configAt 0 1 1 a).Nsc = 0
      ∧ (configAt 0 1 0 a).N = 1 ∧ (configAt 0 1 1 a).N = 3 := by
  classical
  refine ⟨fun p => ?_, (simple_atom_counts ha).2.1, (haunted_atom_counts ha).2.1,
    (simple_atom_counts ha).2.2, (haunted_atom_counts ha).2.2⟩
  have h0 := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 0) (by norm_num)
  have h1 := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by norm_num)
  norm_num at h0 h1
  rw [onMoment_from_onProfile, onMoment_from_onProfile,
    onProfile_eq_profile_map, onProfile_eq_profile_map, h0, h1]
  simp


/-! #### The two families together — `SESSION 351`

`350` closed the arc with each family seeing one ledger row.  The obvious next
question is what they see *jointly*, and the answer is both halves of a pair:
**together they determine the whole ledger, and still not the profile.**

The reason the ledger falls is that each of its five rows is a functional of one
marginal or of the two marginals' sums — `N` and `N⊛` are the `H`-moments at `1` and
`2`, `N_sc` is `346`, `NscStd` is `349`, and `N_off` is the difference `N − Σ onAt`,
which is the identity below.

**Kill condition, filed first:** *if computing the on-moments on a two-atom
configuration needs new infrastructure, I report the reduction and state the profile
question as open.*  It did not fire: `twoAtom_profile` and `onMoment_from_onProfile`
give it. -/

/-- `N_off` as a sum over the atoms.  `Basic.Noff_eq_sum` is the `ℤ`-valued sum over
`Z`; this is the `ℕ`-valued sum over ordinates, which is what the moment identities
want. -/
lemma Noff_eq_sum_offAt (D : ZeroData) :
    D.Noff = ∑ γ ∈ D.ordinates.toFinset, offAt D γ := by
  classical
  rw [Noff_from_profile, profile, Multiset.map_map]
  rfl

/-- **`N_off + Σ onAt = N`.**  The bridge that puts `N_off` inside the joint reach of
the two families: `N` is an `H`-moment and `Σ onAt` is an on-moment. -/
lemma Noff_add_onMoment_one (D : ZeroData) : D.Noff + onMoment D 1 = D.N := by
  classical
  rw [Noff_eq_sum_offAt, onMoment, N_eq_sum_H, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have h := H_eq_onAt_add_offAt D γ
  rw [pow_one]
  omega

/-- **Both families together still do not determine the profile.**

Two two-atom configurations with `(mass, off-line mass)` profiles `{(3,2),(5,2)}` and
`{(3,0),(5,4)}`: the mass multiset is `{3,5}` on both sides, so every `H`-moment
agrees, and the on-line counts are `{1,3}` on both sides, so every on-moment agrees.
The profiles differ.

So the two marginals do not pin the joint — and by
`Riemann.Optimal.ledger_determined_by_both_moment_families` every ledger row
nonetheless agrees on this pair, which is what makes it a statement about the profile
rather than about the ledger. -/
theorem profile_not_determined_by_both_families {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (∀ k, momentK (twoAtom γ a 1 1 3 1) k = momentK (twoAtom γ a 3 0 1 2) k)
      ∧ (∀ p, onMoment (twoAtom γ a 1 1 3 1) p = onMoment (twoAtom γ a 3 0 1 2) p)
      ∧ profile (twoAtom γ a 1 1 3 1) ≠ profile (twoAtom γ a 3 0 1 2) := by
  classical
  have pA := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 3) (j₂ := 1)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 1) (j₂ := 2)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨fun k => ?_, fun p => ?_, ?_⟩
  · rw [momentK_from_profile, momentK_from_profile, pA, pB]
    simp
  · rw [onMoment_from_onProfile, onMoment_from_onProfile,
      onProfile_eq_profile_map, onProfile_eq_profile_map, pA, pB]
    simp
    ring
  · rw [pA, pB]
    decide


/-! #### Two marginalisations of one object, and only one of them keeps the row —
`SESSION 353`

`351` showed the pair *(mass marginal, on-line marginal)* determines every ledger row.
The profile is written in a different pair of coordinates — *(mass, off-line mass)* —
and the obvious question is whether **its own** marginals do the same.  They do not.

**The reason is short and already on disk.**  `NscStd` is a functional of the on-line
marginal alone (`349`), so the first pair carries it for free.  Recovering the on-line
count from the second pair needs `on = mass − off` *per ordinate*, which is the joint
and not the marginals.

**Kill condition, filed first:** *if a not-sufficient theorem for the profile's
marginal pair is already on disk, the deliverable is the pointer.*  Searched
`statement_index --find 'both_marginals|marginals_not|…'` and read the neighbours:
`mass_only_not_sufficient` and `off_only_not_sufficient` each drop **one** marginal
and are about `Noff` and `N`; neither is about the pair, and neither is about `NscStd`.
It did not fire. -/

/-- **The profile's own two marginals do not determine `NscStd`.**

Two two-atom configurations with profiles `{(3,0),(5,2)}` and `{(3,2),(5,0)}` — the same
masses `{3,5}` and the same off-line masses `{0,2}`, paired the other way round.  The
on-line counts are `{3,3}` against `{1,5}`, so `NscStd` is `0` against `1`.

Contrast `Riemann.Optimal.ledger_determined_by_both_moment_families`: swapping the
off-line marginal for the on-line one makes the same pair of marginals sufficient for
every row. -/
theorem NscStd_not_determined_by_profile_marginals {γ a : ℝ} (hγ : γ ≠ 0)
    (ha : a ≠ 1/2) :
    (profile (twoAtom γ a 3 0 3 1)).map Prod.fst
        = (profile (twoAtom γ a 1 1 5 0)).map Prod.fst
      ∧ (profile (twoAtom γ a 3 0 3 1)).map Prod.snd
        = (profile (twoAtom γ a 1 1 5 0)).map Prod.snd
      ∧ (twoAtom γ a 3 0 3 1).NscStd = 0
      ∧ (twoAtom γ a 1 1 5 0).NscStd = 1 := by
  classical
  have pA := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 3) (j₂ := 1)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 5) (j₂ := 0)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pA, pB]; decide
  · rw [pA, pB]; decide
  · rw [NscStd_from_onProfile, onProfile_eq_profile_map, pA]; decide
  · rw [NscStd_from_onProfile, onProfile_eq_profile_map, pB]; decide

/-- **On that witness the other four rows agree.**  `N`, `N⊛`, `N_sc` and `N_off` are
all equal across the pair, so the row the profile's marginals lose there is the reported
one, which is what `Riemann.Blindness.NscStd_not_determined_by_profile_marginals`
exhibits.

This is a fact about this witness, not a general claim: it says the pair is a clean
separator, not that `NscStd` is the only row any such pair could separate. -/
theorem marginal_pair_separates_only_NscStd {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 3 0 3 1).N = (twoAtom γ a 1 1 5 0).N
      ∧ (twoAtom γ a 3 0 3 1).Nstar = (twoAtom γ a 1 1 5 0).Nstar
      ∧ (twoAtom γ a 3 0 3 1).Nsc = (twoAtom γ a 1 1 5 0).Nsc
      ∧ (twoAtom γ a 3 0 3 1).Noff = (twoAtom γ a 1 1 5 0).Noff := by
  classical
  have pA := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 3) (j₂ := 1)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 5) (j₂ := 0)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [N_from_profile, N_from_profile, pA, pB]; decide
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · rw [Nsc_from_onProfile, Nsc_from_onProfile, onProfile_eq_profile_map,
      onProfile_eq_profile_map, pA, pB]; decide
  · rw [Noff_from_profile, Noff_from_profile, pA, pB]; decide


/-! #### The third pairing, and the survey closes — `SESSION 354`

The profile's two coordinates are mass and off-line mass, and `on = mass − off`, so
there are three ways to keep two of the three and forget the pairing.  `351` and `353`
did two of them; this does the third, and the three together are the whole list.

| kept | determines | misses |
|---|---|---|
| mass, on | all five rows (`351`) | — |
| mass, off | four (`353`) | `NscStd` |
| on, off | three (below) | `N⊛`, `N_sc` |

**Kill condition, filed first:** *if any row I expect the `(on, off)` pair to keep needs
the joint after all, I report which and leave the row's cell empty rather than filling
it by assumption.*  It did not fire: `N` is the sum of the two marginals, `N_off` the
sum of one, and `NscStd` a count in the other. -/

/-- Profile entries have off-line mass at most total mass — the pointwise fact the
marginal identities need. -/
lemma profile_snd_le_fst (D : ZeroData) {q : ℕ × ℕ} (hq : q ∈ profile D) :
    q.2 ≤ q.1 := by
  classical
  rw [profile, Multiset.mem_map] at hq
  obtain ⟨γ, -, rfl⟩ := hq
  have h := H_eq_onAt_add_offAt D γ
  simp only
  omega

/-- `NscStd` is a count in the on-line marginal. -/
lemma NscStd_from_on_marginal (D : ZeroData) :
    D.NscStd = ((onProfile D).map Prod.fst).count 1 := by
  classical
  rw [NscStd_from_onProfile, Multiset.count_map]
  simp [eq_comm]

/-- `N_off` is the sum of the off-line marginal. -/
lemma Noff_from_on_marginal (D : ZeroData) :
    D.Noff = ((onProfile D).map Prod.snd).sum := by
  classical
  rw [Noff_from_profile, onProfile_eq_profile_map, Multiset.map_map]
  rfl

/-- `N` is the sum of both marginals — `mass = on + off` summed, which needs
`profile_snd_le_fst` because the subtraction is in `ℕ`. -/
lemma N_from_on_marginals (D : ZeroData) :
    D.N = ((onProfile D).map Prod.fst).sum + ((onProfile D).map Prod.snd).sum := by
  classical
  rw [N_from_profile, onProfile_eq_profile_map, Multiset.map_map, Multiset.map_map,
    ← Multiset.sum_map_add]
  refine congrArg _ (Multiset.map_congr rfl fun q hq => ?_)
  have h := profile_snd_le_fst D hq
  simp only [Function.comp_apply]
  omega

/-- **The `(on, off)` pairing keeps three rows.**  Each is a functional of one marginal
or of the two sums, so forgetting the pairing costs nothing for these. -/
theorem ledger_partly_determined_by_on_off_marginals {D D' : ZeroData}
    (hon : (onProfile D).map Prod.fst = (onProfile D').map Prod.fst)
    (hoff : (onProfile D).map Prod.snd = (onProfile D').map Prod.snd) :
    D.N = D'.N ∧ D.Noff = D'.Noff ∧ D.NscStd = D'.NscStd := by
  refine ⟨?_, ?_, ?_⟩
  · rw [N_from_on_marginals, N_from_on_marginals, hon, hoff]
  · rw [Noff_from_on_marginal, Noff_from_on_marginal, hoff]
  · rw [NscStd_from_on_marginal, NscStd_from_on_marginal, hon]

/-- **…and loses the other two.**  Two configurations with on-line marginal `{1,3}` and
off-line marginal `{0,2}`, paired the two ways: `N⊛` is `26` against `18` and `N_sc` is
`1` against `0`.

Both quantities need the mass, and mass is `on + off` *per ordinate* — which is the
pairing this coarsening throws away. -/
theorem Nstar_Nsc_not_determined_by_on_off_marginals {γ a : ℝ} (hγ : γ ≠ 0)
    (ha : a ≠ 1/2) :
    (onProfile (twoAtom γ a 1 0 3 1)).map Prod.fst
        = (onProfile (twoAtom γ a 1 1 3 0)).map Prod.fst
      ∧ (onProfile (twoAtom γ a 1 0 3 1)).map Prod.snd
        = (onProfile (twoAtom γ a 1 1 3 0)).map Prod.snd
      ∧ (twoAtom γ a 1 0 3 1).Nstar = 26 ∧ (twoAtom γ a 1 1 3 0).Nstar = 18
      ∧ (twoAtom γ a 1 0 3 1).Nsc = 1 ∧ (twoAtom γ a 1 1 3 0).Nsc = 0 := by
  classical
  have pA := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 0) (k₂ := 3) (j₂ := 1)
    (by norm_num) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 1) (j₁ := 1) (k₂ := 3) (j₂ := 0)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [onProfile_eq_profile_map, onProfile_eq_profile_map, pA, pB]; decide
  · rw [onProfile_eq_profile_map, onProfile_eq_profile_map, pA, pB]; decide
  · rw [Nstar_from_profile, pA]; decide
  · rw [Nstar_from_profile, pB]; decide
  · rw [Nsc_from_onProfile, onProfile_eq_profile_map, pA]; decide
  · rw [Nsc_from_onProfile, onProfile_eq_profile_map, pB]; decide


/-! #### What the paper says its results are not, formalised — `SESSION 358`

`356` read `arXiv:2608.13637` §1.4: *"The theorems are lower bounds only: the remaining
third of the zeros are not shown to be off the line, merely not reached by the
certificate.  The inputs are insensitive to `o(N)` off-line zeros and hold for
Davenport–Heilbronn and Epstein zeta functions, for which the analogue of RH is false."*

The middle clause has a formal shape in this vocabulary, and it is sharper than
`o(N)`: **superposing a configuration with no on-line zeros leaves `NscStd`
unchanged — at any size, not merely `o(N)`.**  What makes the paper say `o(N)` is
that `N` itself grows, so the *proportion* moves by `o(1)`; the count does not move
at all.

**Kill condition, filed first:** *if a superposition-perturbation lemma for `NscStd`
is already on disk, the deliverable is the pointer; and if `superpose` needs a
disjointness hypothesis that makes the statement vacuous where it is wanted, I say so
rather than adding hypotheses until it works.*  It did not fire — `H_superpose`,
`offAt_superpose` and `add_ordinates` are unconditional, and the fourteen `superpose`
rows in the index carry nothing about `NscStd`.

**And the companion is the project's own distinction.**  `N_sc` is *not* insensitive:
the same superposition drops it from `1` to `0`, because a mass-one ordinate that
acquires an off-line pair has `H = 3`.  So the two ledger rows differ exactly in their
response to added off-line zeros — which is `hauntedCount`, and which is why the
project reports both. -/

lemma onAt_superpose (D D' : ZeroData) (γ : ℝ) :
    onAt (superpose D D') γ = onAt D γ + onAt D' γ := by
  have h1 := H_eq_onAt_add_offAt D γ
  have h2 := H_eq_onAt_add_offAt D' γ
  have h3 := H_eq_onAt_add_offAt (superpose D D') γ
  have h4 := H_superpose D D' γ
  have h5 := offAt_superpose D D' γ
  omega

lemma onAt_eq_zero_of_not_mem (D : ZeroData) {γ : ℝ} (h : γ ∉ D.ordinates) :
    onAt D γ = 0 := by
  classical
  have hH : D.H γ = 0 := by
    rw [D.H_eq_count γ, Multiset.count_eq_zero]
    exact h
  have := H_eq_onAt_add_offAt D γ
  omega

theorem NscStd_insensitive_to_offLine (D E : ZeroData) (hE : ∀ γ, onAt E γ = 0) :
    (superpose D E).NscStd = D.NscStd := by
  classical
  rw [NscStd_eq_onAt_one, NscStd_eq_onAt_one]
  have hon : ∀ γ, onAt (superpose D E) γ = onAt D γ := by
    intro γ; rw [onAt_superpose, hE γ, Nat.add_zero]
  refine Finset.card_bij (fun γ _ => γ) ?_ (fun _ _ _ _ h => h) ?_
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    rw [hon γ] at hγ
    refine Finset.mem_filter.2 ⟨?_, hγ.2⟩
    rw [Multiset.mem_toFinset]
    by_contra hnot
    rw [onAt_eq_zero_of_not_mem D hnot] at hγ
    exact absurd hγ.2 (by norm_num)
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    refine ⟨γ, Finset.mem_filter.2 ⟨?_, by rw [hon γ]; exact hγ.2⟩, rfl⟩
    rw [Multiset.mem_toFinset, add_ordinates]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_toFinset.1 hγ.1))

lemma onAt_eq_zero_of_offLine (E : ZeroData) (h : ∀ p ∈ E.Z, p.1 ≠ 1/2) (γ : ℝ) :
    onAt E γ = 0 := by
  classical
  rw [onAt, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro p hp hc
  exact h p hp hc.2

lemma offLine_pair_no_online {a : ℝ} (ha : a ≠ 1/2) :
    ∀ p ∈ (configAt 0 0 1 a).Z, p.1 ≠ 1/2 := by
  have ha' : (1 - a : ℝ) ≠ 1/2 := fun h => ha (by linarith [h])
  intro p hp
  have : p ∈ Multiset.replicate 0 ((1/2 : ℝ), (0:ℝ))
      + (Multiset.replicate 1 (a, (0:ℝ)) + Multiset.replicate 1 ((1 - a : ℝ), (0:ℝ))) := hp
  simp only [Multiset.replicate_zero, zero_add, Multiset.replicate_one,
    Multiset.mem_add, Multiset.mem_singleton] at this
  rcases this with h | h <;> subst h
  · exact ha
  · exact ha'

theorem Nsc_sensitive_to_offLine {a : ℝ} (ha : a ≠ 1/2) :
    superpose (configAt 0 1 0 a) (configAt 0 0 1 a) = configAt 0 1 1 a
      ∧ (configAt 0 1 0 a).NscStd = 1 ∧ (configAt 0 1 1 a).NscStd = 1
      ∧ (configAt 0 1 0 a).Nsc = 1 ∧ (configAt 0 1 1 a).Nsc = 0 := by
  refine ⟨rfl, (simple_atom_counts ha).1, (haunted_atom_counts ha).1,
    (simple_atom_counts ha).2.1, (haunted_atom_counts ha).2.1⟩

theorem NscStd_insensitive_offLine_witness {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 1 a).NscStd = (configAt 0 1 0 a).NscStd := by
  have h := NscStd_insensitive_to_offLine (configAt 0 1 0 a) (configAt 0 0 1 a)
    (onAt_eq_zero_of_offLine _ (offLine_pair_no_online ha))
  rwa [(rfl : superpose (configAt 0 1 0 a) (configAt 0 0 1 a) = configAt 0 1 1 a)] at h


/-! #### `361`'s analogy, made precise and then refuted in its naive form —
`SESSION 363`

`361` recorded a resemblance and asked a later cycle to make it precise or refute it.
`arXiv:2608.13637` §7.2 defines a *bandwidth-one certificate* as depending on a
configuration *"only through its first two trace moments against test functions of
Fourier support in `[−1,1]` and the partition into on-line points and off-line pairs"*,
and this project's ledger is a functional of the profile.

**The naive reading is that "two trace moments" means two numbers.** Its combinatorial
shadow on a `ZeroData` is `N = Σ mass`, `N⊛ = Σ mass²`, the off-line total `N_off`, and
the on-line total `Σ onAt` — and by `Noff_add_onMoment_one` the fourth is determined by
the first and third, so it is three numbers.

**That reading is refuted below:** those numbers do not determine `NscStd`, so a
certificate depending only on them could not be one at all. **The paper's class is
therefore strictly richer than the shadow** — its moments are a family indexed by test
functions, not a fixed tuple — which is what the analogy got wrong.

**Kill condition, filed first:** *if the four numbers differ on `353`'s pair, I need a
different witness and I say so.* It did not fire: `353`'s
`marginal_pair_separates_only_NscStd` already gives `N`, `N⊛` and `N_off` equal there, and
the on-line total follows from `351`'s identity.

**What this does not do.** It says nothing about the paper's certificates, whose data is
richer than these three numbers; it only removes one reading of the resemblance. The
`≈0.682` ceiling is over the paper's class and is untouched. -/

/-- **Three global numbers do not determine `NscStd`.**  On `353`'s pair — profiles
`{(3,0),(5,2)}` and `{(3,2),(5,0)}` — the totals `N`, `N⊛`, `N_off` and `Σ onAt` all
agree while `NscStd` is `0` against `1`.

Composed from `353`'s two theorems and `351`'s `Noff_add_onMoment_one`; nothing new is
computed. -/
theorem NscStd_not_determined_by_two_moments_and_split {γ a : ℝ} (hγ : γ ≠ 0)
    (ha : a ≠ 1/2) :
    (twoAtom γ a 3 0 3 1).N = (twoAtom γ a 1 1 5 0).N
      ∧ (twoAtom γ a 3 0 3 1).Nstar = (twoAtom γ a 1 1 5 0).Nstar
      ∧ (twoAtom γ a 3 0 3 1).Noff = (twoAtom γ a 1 1 5 0).Noff
      ∧ onMoment (twoAtom γ a 3 0 3 1) 1 = onMoment (twoAtom γ a 1 1 5 0) 1
      ∧ (twoAtom γ a 3 0 3 1).NscStd = 0
      ∧ (twoAtom γ a 1 1 5 0).NscStd = 1 := by
  obtain ⟨hN, hStar, -, hOff⟩ := marginal_pair_separates_only_NscStd hγ ha
  obtain ⟨-, -, hS0, hS1⟩ := NscStd_not_determined_by_profile_marginals hγ ha
  refine ⟨hN, hStar, hOff, ?_, hS0, hS1⟩
  have e1 := Noff_add_onMoment_one (twoAtom γ a 3 0 3 1)
  have e2 := Noff_add_onMoment_one (twoAtom γ a 1 1 5 0)
  omega


/-! #### The on-line side of the chain — `SESSION 365`

`349` proved the on-line moments determine every on-line count under a cap and
instantiated it only at `n = 1`, for `NscStd`.  `365` takes the general form uncapped
and spends it on the chain's middle term.

`N_sc ≤ NscStd ≤ oddAtoms ≤ onLineOrdinates ≤ atomCount` — `348` gave the `H`-moments
the two outer terms via the mass counts, and `349` gave the on-moments `NscStd`.
`oddAtoms` is a count of on-line values with a parity condition, so it should fall to
the on-moments too, and the bridge is a fiberwise partition of the ordinates by `onAt`.

**Kill condition, filed first:** *if the fiberwise partition does not go through
cheaply, I ship the uncapped `onCount` determinacy alone and state the chain corollary
as not done.*  It did not fire.

**`onLineOrdinates` is not done.**  The same argument with the predicate `n ≠ 0` in
place of `Odd n` would give it; this cycle did not write it, and the chain's fourth
term is therefore still unaddressed by the on-moments.

**`366`: written.**  `onLineOrdinates_eq_sum_onCount` and
`Riemann.Optimal.onLineOrdinates_determined_by_on_moments`, by exactly that
substitution. -/

/-- **`oddAtoms` as a sum of on-line counts.**  Partition the ordinates by the value of
`onAt`, which lies in `[0, B]` under the cap, and keep the odd fibres. -/
lemma oddAtoms_eq_sum_onCount (D : ZeroData) {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ≤ B) :
    oddAtoms D = ∑ n ∈ Finset.range (B + 1), if Odd n then onCount D n else 0 := by
  classical
  have hmaps : ∀ γ ∈ D.ordinates.toFinset.filter (fun γ => ¬ Even (onAt D γ)),
      onAt D γ ∈ Finset.range (B + 1) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_range.2 (by have := h γ hγ.1; omega)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [oddAtoms_eq_odd_onAt, hfib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : Odd n
  · rw [if_pos hn, onCount]
    congr 1
    ext γ
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · intro hx; exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      rw [hx.2]
      exact Nat.not_even_iff_odd.2 hn
  · rw [if_neg hn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro γ hγ h2
    rw [Finset.mem_filter] at hγ
    exact hn (Nat.not_even_iff_odd.1 (h2 ▸ hγ.2))



/-! #### The chain's fourth term, and what the on-line family reaches — `SESSION 366`

`365` shipped `oddAtoms` and named `onLineOrdinates` as not done: *"the same argument
with `n ≠ 0` in place of `Odd n` would give it"*.  It does, and it completes the
picture — with `atomCount` falling out of the definition rather than the argument.

**Kill condition, filed first:** *if `atomCount = onMoment 0` is not immediate from the
definitions, I ship the `onLineOrdinates` half and state the `atomCount` half
separately.*  It did not fire: the zeroth moment of any weight counts the atoms. -/

/-- **`atomCount` is the on-line family's zeroth moment.**  `onAt γ ^ 0 = 1` at every
ordinate, so the sum counts them. -/
lemma atomCount_eq_onMoment_zero (D : ZeroData) : atomCount D = onMoment D 0 := by
  classical
  rw [onMoment, atomCount]
  simp

/-- **`onLineOrdinates` as a sum of on-line counts.**  `365`'s partition with the
non-zero fibres in place of the odd ones. -/
lemma onLineOrdinates_eq_sum_onCount (D : ZeroData) {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ≤ B) :
    onLineOrdinates D
      = ∑ n ∈ Finset.range (B + 1), if n ≠ 0 then onCount D n else 0 := by
  classical
  have hmaps : ∀ γ ∈ D.ordinates.toFinset.filter (fun γ => onAt D γ ≠ 0),
      onAt D γ ∈ Finset.range (B + 1) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_range.2 (by have := h γ hγ.1; omega)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [onLineOrdinates, onOrd_toFinset, hfib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn
    rw [if_neg (by simp), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro γ hγ h2
    rw [Finset.mem_filter] at hγ
    exact hγ.2 h2
  · rw [if_pos hn, onCount]
    congr 1
    ext γ
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · intro hx; exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      rw [hx.2]; exact hn


/-! #### `oddAtoms` is a mass functional, and the chain's split is not a cut —
`SESSION 367`

`366` closed on the chain splitting between the two moment families, with the boundary
at the project's two reported rows. **That picture is wrong, and this section is the
correction.**

`even_offAt` says every ordinate's off-line mass is even, so `H = onAt + offAt` makes
`H` and `onAt` share their parity. Hence `oddAtoms` — defined by the parity of `onAt` —
counts the ordinates of **odd mass**, and is therefore a functional of the mass counts
as well as of the on-line ones.

**So the `H`-family's reach along `N_sc ≤ NscStd ≤ oddAtoms ≤ onLineOrdinates ≤ atomCount`
is not an interval.** It has `N_sc` (`348`), misses `NscStd` (`347`), has `oddAtoms`
(below), misses `onLineOrdinates` (below), and has `atomCount` (`momentK 0`). It
alternates.

**Kill condition, filed first:** *if the parity step needs more than `even_offAt`, I
report what it needs rather than adding hypotheses.*  It did not fire. -/

/-- **`oddAtoms` counts the odd-mass ordinates.**  `even_offAt` makes `H` and `onAt`
share their parity, so the two filters coincide. -/
lemma oddAtoms_eq_odd_H (D : ZeroData) :
    oddAtoms D = (D.ordinates.toFinset.filter fun γ => ¬ Even (D.H γ)).card := by
  classical
  rw [oddAtoms_eq_odd_onAt]
  congr 1
  refine Finset.filter_congr fun γ _ => ?_
  obtain ⟨k, hk⟩ := even_offAt D γ
  have h := H_eq_onAt_add_offAt D γ
  rw [Nat.even_iff, Nat.even_iff]
  constructor
  · intro h1; omega
  · intro h1; omega

/-- …hence a sum of mass counts, by `365`'s partition run on `H`. -/
lemma oddAtoms_eq_sum_massCount (D : ZeroData) {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ B) :
    oddAtoms D = ∑ n ∈ Finset.range (B + 1), if Odd n then massCount D n else 0 := by
  classical
  have hmaps : ∀ γ ∈ D.ordinates.toFinset.filter (fun γ => ¬ Even (D.H γ)),
      D.H γ ∈ Finset.range (B + 1) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_range.2 (by have := h γ hγ.1; omega)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [oddAtoms_eq_odd_H, hfib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : Odd n
  · rw [if_pos hn, massCount]
    congr 1
    ext γ
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · intro hx; exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      rw [hx.2]
      exact Nat.not_even_iff_odd.2 hn
  · rw [if_neg hn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro γ hγ h2
    rw [Finset.mem_filter] at hγ
    exact hn (Nat.not_even_iff_odd.1 (h2 ▸ hγ.2))

/-- **The `H`-family misses `onLineOrdinates`, which is what makes its reach
alternate.**  A pure on-line pair and a single off-line pair both have mass multiset
`{2}`, so every `momentK` agrees; `onLineOrdinates` is `1` against `0`.

This is `mass_only_not_sufficient`'s configuration pair used for a different count. -/
theorem onLineOrdinates_not_determined_by_all_moments {a : ℝ} (ha : a ≠ 1/2) :
    (∀ k, momentK (configAt 0 2 0 a) k = momentK (configAt 0 0 1 a) k)
      ∧ onLineOrdinates (configAt 0 2 0 a) = 1
      ∧ onLineOrdinates (configAt 0 0 1 a) = 0 := by
  classical
  have p1 := configAt_profile (γ := (0:ℝ)) ha (k := 2) (j := 0) (by norm_num)
  have p2 := configAt_profile (γ := (0:ℝ)) ha (k := 0) (j := 1) (by norm_num)
  norm_num at p1 p2
  refine ⟨fun k => ?_, ?_, ?_⟩
  · rw [momentK_from_profile, momentK_from_profile, p1, p2]; simp
  · have hA := onLineOrdinates_add_offLineOnly (configAt 0 2 0 a)
    have h1 : atomCount (configAt 0 2 0 a) = 1 := by
      rw [atomCount_eq_card_profile, p1]; decide
    have h2 : offLineOnly (configAt 0 2 0 a) = 0 := by
      rw [offLineOnly_from_profile, p1]; decide
    omega
  · have hA := onLineOrdinates_add_offLineOnly (configAt 0 0 1 a)
    have h1 : atomCount (configAt 0 0 1 a) = 1 := by
      rw [atomCount_eq_card_profile, p2]; decide
    have h2 : offLineOnly (configAt 0 0 1 a) = 1 := by
      rw [offLineOnly_from_profile, p2]; decide
    omega


/-- **`momentK` is a weighted sum of the mass counts.**  `SESSION 368`.

Partition the ordinates by their multiplicity: the fibre over `n` has
`massCount D n` elements and each contributes `n ^ k`.  `oddAtoms_eq_sum_massCount`
is the same partition with a `0/1` weight; this is the general weight, and it is
what makes `Riemann.Optimal.moment_blind_iff_massCount` an equivalence rather
than a one-way implication.

The cap `B` is discharged at `max D.N D'.N` wherever this is used. -/
lemma momentK_eq_sum_massCount (D : ZeroData) (k : ℕ) {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, D.H γ ≤ B) :
    momentK D k = ∑ n ∈ Finset.range (B + 1), massCount D n * n ^ k := by
  classical
  have hmaps : ∀ γ ∈ D.ordinates.toFinset, D.H γ ∈ Finset.range (B + 1) :=
    fun γ hγ => Finset.mem_range.2 (by have := h γ hγ; omega)
  rw [momentK, ← Finset.sum_fiberwise_of_maps_to' hmaps (fun n => n ^ k)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [massCount, Finset.sum_const, smul_eq_mul]

/-- **`onMoment` is a weighted sum of the on-line counts.**  `SESSION 368`.

The on-line twin of `momentK_eq_sum_massCount`, and the reason
`Riemann.Optimal.on_moment_blind_iff_onCount` is an equivalence too.  Note that
no term is excluded: `onCount D 0` may be positive, and `0 ^ 0 = 1` is exactly
what makes `atomCount_eq_onMoment_zero` come out right. -/
lemma onMoment_eq_sum_onCount (D : ZeroData) (p : ℕ) {B : ℕ}
    (h : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ≤ B) :
    onMoment D p = ∑ n ∈ Finset.range (B + 1), onCount D n * n ^ p := by
  classical
  have hmaps : ∀ γ ∈ D.ordinates.toFinset, onAt D γ ∈ Finset.range (B + 1) :=
    fun γ hγ => Finset.mem_range.2 (by have := h γ hγ; omega)
  rw [onMoment, ← Finset.sum_fiberwise_of_maps_to' hmaps (fun n => n ^ p)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [onCount, Finset.sum_const, smul_eq_mul]


/-- **The ledger is a functional of five named scalars.**  `SESSION 369`.

`350`'s `Riemann.Optimal.ledger_determined_by_both_moment_families` asks for two
whole infinite families.  It does not need them: each row is one identity in one
scalar — `momentK 1` is `N` (`momentK_one`), `momentK 2` is `Nstar`
(`momentK_two`), `massCount 1` is `Nsc` (`massCount_one`), `onCount 1` is
`NscStd` (`NscStd_eq_onCount_one`), and `Noff` is `N` minus `onMoment 1`
(`Noff_add_onMoment_one`).

That the profile is *not* a minimal sufficient statistic for the ledger has been
on disk since `075`/`077` as `Fiber.profile_not_minimal`, a pair of configurations with
distinct profiles and one ledger.  What is new here is the positive direction: a
named coarse statistic, universally quantified, rather than a witness that some
coarsening exists.

**Settled at `370`:** every one of the five is necessary, so no proper subset of
the five determines the ledger — `onCount_one_cannot_be_dropped` (`369`),
`momentK_one_cannot_be_dropped`, `momentK_two_cannot_be_dropped`,
`massCount_one_cannot_be_dropped` and `Noff_not_determined_by_ledger`.  That is
minimality of this set under inclusion; it does *not* say five is the smallest
possible count.

**`372`:** and the smallest-count question has no content unrestricted — one
number does it, by `Fiber.ledgerCode_eq_iff`.  The clause below about "some
different set of four" is answered, and downward: a set of *one* exists outside
the named class.  A minimality claim needs a class, and by
`Fiber.ledgerCode_eq_iff` this one's class is these five. -/
theorem ledger_determined_by_five_scalars {D D' : ZeroData}
    (hN : momentK D 1 = momentK D' 1)
    (hstar : momentK D 2 = momentK D' 2)
    (hsc : massCount D 1 = massCount D' 1)
    (hon1 : onMoment D 1 = onMoment D' 1)
    (honc : onCount D 1 = onCount D' 1) :
    D.N = D'.N ∧ D.Nstar = D'.Nstar ∧ D.Nsc = D'.Nsc
      ∧ D.NscStd = D'.NscStd ∧ D.Noff = D'.Noff := by
  have hn : D.N = D'.N := by rw [← momentK_one D, ← momentK_one D', hN]
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · rw [← momentK_two D, ← momentK_two D', hstar]
  · rw [← massCount_one D, ← massCount_one D', hsc]
  · rw [NscStd_eq_onCount_one D, NscStd_eq_onCount_one D', honc]
  · have e1 := Noff_add_onMoment_one D
    have e2 := Noff_add_onMoment_one D'
    omega

/-- **`Blindness.onCount_one_cannot_be_dropped`: `onCount 1` cannot be dropped
from the five.**  `SESSION 369`.

`363`'s pair has equal mass multisets — both profiles carry masses `3` and `5` —
so by `Riemann.Optimal.moment_blind_iff_massCount` every `massCount` agrees, and
with it every `momentK`; that equality is proved here directly from
`momentK_from_profile` and `twoAtom_profile`.  `363` already gives equal
`onMoment 1`.  Yet `NscStd` is `0` against `1`, so the whole `H`-family plus
`onMoment 1` leaves the ledger split.

This is necessity for one of the five scalars, not minimality of the set. -/
theorem onCount_one_cannot_be_dropped {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (∀ k, momentK (twoAtom γ a 3 0 3 1) k = momentK (twoAtom γ a 1 1 5 0) k)
      ∧ onMoment (twoAtom γ a 3 0 3 1) 1 = onMoment (twoAtom γ a 1 1 5 0) 1
      ∧ (twoAtom γ a 3 0 3 1).NscStd = 0
      ∧ (twoAtom γ a 1 1 5 0).NscStd = 1 := by
  obtain ⟨-, -, -, hon1, hS0, hS1⟩ :=
    NscStd_not_determined_by_two_moments_and_split hγ ha
  refine ⟨fun k => ?_, hon1, hS0, hS1⟩
  rw [momentK_from_profile, momentK_from_profile,
    twoAtom_profile hγ ha (by norm_num) (by norm_num),
    twoAtom_profile hγ ha (by norm_num) (by norm_num)]
  norm_num


/-- **The last of `369`'s five scalars that was genuinely open.**  `SESSION 370`.

`369` left necessity of four of the five scalars open.  Three of those four were
already on disk — `Nstar_not_determined_by_ledger`,
`Nsc_not_determined_by_ledger` and `Noff_not_determined_by_ledger` from the
`070`s–`080`s each give one, once `Noff_add_onMoment_one` converts an
equal-`Noff` conjunct into an equal-`onMoment 1` one.  That conversion needs `N`
to agree, which is exactly why the `N` case does not follow:
`N_not_determined_by_ledger` holds `Noff` fixed while `N` moves, so
`onMoment 1` moves with it.

This pair fixes that.  Profiles `{(5,0)}` against `{(3,0),(4,2)}`: equal `Nstar`
at `25`, equal `Nsc` and `NscStd` at `0`, equal `onMoment 1` at `5`, and `N` of
`5` against `7`. -/
theorem momentK_one_cannot_be_dropped {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (configAt 0 5 0 a).Nstar = (twoAtom γ a 3 0 2 1).Nstar
      ∧ (configAt 0 5 0 a).Nsc = (twoAtom γ a 3 0 2 1).Nsc
      ∧ (configAt 0 5 0 a).NscStd = (twoAtom γ a 3 0 2 1).NscStd
      ∧ onMoment (configAt 0 5 0 a) 1 = onMoment (twoAtom γ a 3 0 2 1) 1
      ∧ (configAt 0 5 0 a).N ≠ (twoAtom γ a 3 0 2 1).N := by
  have pA := configAt_profile (γ := (0:ℝ)) ha (k := 5) (j := 0) (by norm_num)
  have pB := twoAtom_profile hγ ha (k₁ := 3) (j₁ := 0) (k₂ := 2) (j₂ := 1)
    (by norm_num) (by norm_num)
  norm_num at pA pB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nstar_from_profile, Nstar_from_profile, pA, pB]; decide
  · have : ((configAt 0 5 0 a).Nsc : ℤ) = ((twoAtom γ a 3 0 2 1).Nsc : ℤ) := by
      rw [Nsc_from_profile, Nsc_from_profile, pA, pB]; decide
    exact_mod_cast this
  · have : ((configAt 0 5 0 a).NscStd : ℤ) = ((twoAtom γ a 3 0 2 1).NscStd : ℤ) := by
      rw [NscStd_from_profile, NscStd_from_profile, pA, pB]; decide
    exact_mod_cast this
  · rw [onMoment_from_onProfile, onMoment_from_onProfile,
      onProfile_eq_profile_map, onProfile_eq_profile_map, pA, pB]; decide
  · rw [N_from_profile, N_from_profile, pA, pB]; decide

/-- **`369`'s four-scalar hypothesis restated so the `onMoment 1` conjunct is
explicit.**  `SESSION 370`.

Nothing new is proved — `Nstar_not_determined_by_ledger` supplies four of the
five conjuncts and `Noff_add_onMoment_one` supplies the fifth.  It is recorded
separately because the five-scalar question asks about `onMoment 1`, not `Noff`,
and a reader checking minimality should not have to redo the conversion.

`onMoment 1` itself needs no restatement: `Noff_not_determined_by_ledger` is
already in the right form, since the row it moves *is* `Noff`. -/
theorem momentK_two_cannot_be_dropped {γ a : ℝ} (hγ : γ ≠ 0) (ha : a ≠ 1/2) :
    (twoAtom γ a 2 0 4 0).N = (twoAtom γ a 3 0 3 0).N
      ∧ (twoAtom γ a 2 0 4 0).Nsc = (twoAtom γ a 3 0 3 0).Nsc
      ∧ (twoAtom γ a 2 0 4 0).NscStd = (twoAtom γ a 3 0 3 0).NscStd
      ∧ onMoment (twoAtom γ a 2 0 4 0) 1 = onMoment (twoAtom γ a 3 0 3 0) 1
      ∧ (twoAtom γ a 2 0 4 0).Nstar ≠ (twoAtom γ a 3 0 3 0).Nstar := by
  obtain ⟨hN, hsc, hstd, hoff, hne⟩ := Nstar_not_determined_by_ledger hγ ha
  refine ⟨hN, hsc, hstd, ?_, hne⟩
  have e1 := Noff_add_onMoment_one (twoAtom γ a 2 0 4 0)
  have e2 := Noff_add_onMoment_one (twoAtom γ a 3 0 3 0)
  omega

/-- **The `Nsc` companion, in five-scalar form.**  `SESSION 370`.

Same conversion as `momentK_two_cannot_be_dropped`, over
`Nsc_not_determined_by_ledger`. -/
theorem massCount_one_cannot_be_dropped {γ δ a : ℝ} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hγδ : γ ≠ δ) (ha : a ≠ 1/2) :
    (threeAtom γ δ a 1 0 1 0 0 2).N = (twoAtom γ a 1 1 1 1).N
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).Nstar = (twoAtom γ a 1 1 1 1).Nstar
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).NscStd = (twoAtom γ a 1 1 1 1).NscStd
      ∧ onMoment (threeAtom γ δ a 1 0 1 0 0 2) 1 = onMoment (twoAtom γ a 1 1 1 1) 1
      ∧ (threeAtom γ δ a 1 0 1 0 0 2).Nsc ≠ (twoAtom γ a 1 1 1 1).Nsc := by
  obtain ⟨hN, hstar, hstd, hoff, hne⟩ := Nsc_not_determined_by_ledger hγ hδ hγδ ha
  refine ⟨hN, hstar, hstd, ?_, hne⟩
  have e1 := Noff_add_onMoment_one (threeAtom γ δ a 1 0 1 0 0 2)
  have e2 := Noff_add_onMoment_one (twoAtom γ a 1 1 1 1)
  omega


/-- **One natural number carries the whole ledger.**  `SESSION 372`.

`Nat.pair` is a bijection `ℕ × ℕ → ℕ`, so nesting it four times encodes the five
ledger rows in a single natural number with nothing lost. -/
noncomputable def ledgerCode (D : ZeroData) : ℕ :=
  Nat.pair (Nat.pair (Nat.pair (Nat.pair D.N D.Nstar) D.Nsc) D.NscStd) D.Noff

/-- **A minimality claim is a claim inside a declared class of statistics** — this
theorem is what makes the unrestricted version empty.  `SESSION 372`.

`369` exhibited five scalars that determine the ledger and `370` showed none of
the five can be dropped; that is minimality under inclusion *within those five*.
Over **arbitrary** `ℕ`-valued functionals the smallest sufficient set has one
element, namely `ledgerCode`, so asking for "the fewest scalars" without naming a
class is answered before it is asked.

Three classes, three answers, and no tension between them:

* unrestricted functionals collapse to one, by this theorem;
* the five named moment-and-count scalars are minimal under inclusion — see
  `Fiber.momentK_one_cannot_be_dropped` and its four companions;
* ordinate-local statistics have the profile as their floor, by
  `profile_minimal_among_local` (`077`).

`ledgerCode` is an encoding and buys no information: recovering a row from it
means running `Nat.unpair`, which is why the useful minimality questions are the
restricted ones. -/
theorem ledgerCode_eq_iff {D D' : ZeroData} :
    ledgerCode D = ledgerCode D'
      ↔ (D.N = D'.N ∧ D.Nstar = D'.Nstar ∧ D.Nsc = D'.Nsc
          ∧ D.NscStd = D'.NscStd ∧ D.Noff = D'.Noff) := by
  simp only [ledgerCode, Nat.pair_eq_pair]
  tauto


/-! #### The star route to the `Nsc` row — what a mean-square bound would buy

`SESSION 374`.  The `Nsc` row is carried by
`three_mul_NscStd_le_N_add_two_mul_Nsc`, whose ledger annotation has read *"no
star bound"* since the row opened.  `star_charges_every_class` supplies one.

**Corrected at `377`.**  `374` presented this as the star bound's first price.
It is not: `241` priced the same currency, `Transfer.proportion_of_starBound`
paying `2 − C` from `StarBound C` alone, with a ceiling table in `RULING.md`.
What `374` adds is a *second trade* in that currency — star bound **plus** the
certified `NscStd ≥ κ·N` — which pays worse below `C = 1393/1000` and better
above it (`star_currency_crossover`).  The useful range of the star currency
widens from `C < 1193/800` to `C < 793/400`; the price was not missing.
-/

/-! `275`'s `ZeroData.six_mul_NscStd_le` already carries the inequality this route
needs — `6·NscStd + N ≤ 6·Nsc + N⊛`, and its docstring already reads *"the row gap
is at most `(N⊛ − N)/6`"*.  `374` adds no bound; what was missing was the price.
`374` first wrote a second proof of it from `star_charges_every_class` and
`duplication_floor` refused the commit before the build. -/

/-- **The sensitivity: what `N⊛ ≤ c·N` buys on top of `NscStd ≥ κ·N`.**
`SESSION 374`. -/
theorem star_route_pointwise {D : ZeroData} {κ c : ℝ}
    (hstd : κ * (D.N : ℝ) ≤ (D.NscStd : ℝ))
    (hstar : (D.Nstar : ℝ) ≤ c * (D.N : ℝ)) :
    (κ - (c - 1) / 6) * (D.N : ℝ) ≤ (D.Nsc : ℝ) := by
  have h := D.six_mul_NscStd_le
  have h' : (6 : ℝ) * (D.NscStd : ℝ) + (D.N : ℝ) ≤ 6 * (D.Nsc : ℝ) + (D.Nstar : ℝ) := by
    exact_mod_cast h
  linarith

/-- **The crossover, for every `κ`.**  `SESSION 374`.

The certified route gives `(3κ − 1)/2`; the star route gives `κ − (c − 1)/6`.
The second beats the first exactly below `c = 4 − 3κ`.

This is a **different channel** from the one `171` closed.  That closure was
about *maximum* multiplicity `M` feeding `Proportion (2 − M)`; this is the mean
square, and the statement is for every `κ`. -/
theorem star_route_beats_iff {κ c : ℝ} :
    (3 * κ - 1) / 2 < κ - (c - 1) / 6 ↔ c < 4 - 3 * κ := by
  constructor <;> intro h <;> linarith

/-- **The ζ-level threshold, as an exact rational.**  `SESSION 374`.

**`383`: this was already on disk.**  `Gaps.starBound_delta_beats_baseline`
(`SESSION 304`) states `(C−1)/6 < 0.16375 ↔ C < 1.9825` — the same threshold as
a biconditional, four cycles before `374` re-derived it in rationals.

At `κ = 269/400` the crossover is `793/400`, bracketed between `1` and `2`, and
the two routes agree there at `407/800` — the value the `Nsc` row already
carries.

**The want-ad is the unconditional one only.**  Under `H ≤ 2` this route is not
the right instrument: `Nsc_eq_NscStd_of_mult_le_two` makes `hauntedCount` zero
and hands over `κ` directly, far above anything the star route yields. -/
theorem star_route_threshold_zeta :
    (4 : ℝ) - 3 * (269 / 400) = 793 / 400
      ∧ (1 : ℝ) < 793 / 400 ∧ (793 : ℝ) / 400 < 2
      ∧ (3 * (269 / 400 : ℝ) - 1) / 2 = 407 / 800 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **`ZeroData.six_mul_NscStd_le` is tight, at the minimal haunted
configuration.**  `SESSION 374`.  Both sides are `9` on the mass-`3` haunted atom, which is the
configuration `CLAIMS.md` records as extremal wherever `hauntedCount` is
charged. -/
theorem star_route_attained {a : ℝ} (ha : a ≠ 1/2) :
    (configAt 0 1 1 a).N = 3 ∧ (configAt 0 1 1 a).Nstar = 9
      ∧ (configAt 0 1 1 a).NscStd = 1 ∧ (configAt 0 1 1 a).Nsc = 0
      ∧ 6 * (configAt 0 1 1 a).NscStd + (configAt 0 1 1 a).N
          = 6 * (configAt 0 1 1 a).Nsc + (configAt 0 1 1 a).Nstar := by
  have p := configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by norm_num)
  norm_num at p
  have hN : (configAt 0 1 1 a).N = 3 := by
    rw [N_from_profile, p]; decide
  have hS : (configAt 0 1 1 a).Nstar = 9 := by
    rw [Nstar_from_profile, p]; decide
  have hStd : (configAt 0 1 1 a).NscStd = 1 := by
    have : ((configAt 0 1 1 a).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, p]; decide
    exact_mod_cast this
  have hsc : (configAt 0 1 1 a).Nsc = 0 := by
    have : ((configAt 0 1 1 a).Nsc : ℤ) = 0 := by
      rw [Nsc_from_profile, p]; decide
    exact_mod_cast this
  refine ⟨hN, hS, hStd, hsc, ?_⟩
  rw [hN, hS, hStd, hsc]


/-- **`374`'s route against `241`'s, in the same currency.**  `SESSION 377`.

`241` already priced the star bound: `Transfer.proportion_of_starBound` pays
`2 − C` from `StarBound C` **alone**, with `Transfer.one_le_of_starBound` and
`Transfer.starBound_ceiling` capping that currency at `1`.  `374`'s route spends
the same star bound *together with* the certified `NscStd ≥ κ·N`, and pays
`κ − (C − 1)/6`.

They are different trades, so they cross.  Below the crossover `241`'s route is
better; above it `374`'s is.

**`383`: this crossover was already on disk too.**
`Gaps.starBound_exchange_crossover` (`SESSION 191`) states
`0.6725 − (C−1)/6 ≤ 2 − C ↔ C ≤ 1.393`.  `377` presented itself as the cycle
that found `374`'s priority and re-derived `191`'s number while doing so. -/
theorem star_currency_crossover {κ C : ℝ} :
    2 - C < κ - (C - 1) / 6 ↔ (11 - 6 * κ) / 5 < C := by
  constructor <;> intro h <;> linarith

/-- **The ζ-level numbers for both star routes.**  `SESSION 377`.

Crossover at `1393/1000`, where both pay `607/1000`.  `241`'s route meets the
certified `Nsc` row at `C = 1193/800`; `374`'s meets it at `793/400`
(`star_route_threshold_zeta`).  So the star currency pays *something* above the
certified row for every `C < 793/400`, and which route to use switches at
`1393/1000`. -/
theorem star_currency_crossover_zeta :
    (11 - 6 * (269 / 400 : ℝ)) / 5 = 1393 / 1000
      ∧ (2 : ℝ) - 1393 / 1000 = 607 / 1000
      ∧ (269 / 400 : ℝ) - (1393 / 1000 - 1) / 6 = 607 / 1000
      ∧ (2 : ℝ) - 1193 / 800 = 407 / 800
      ∧ (1 : ℝ) < 1393 / 1000 ∧ (1393 : ℝ) / 1000 < 1193 / 800 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩


/-! #### The star bound at a ladder rung — `SESSION 382`

`ZeroData.six_mul_card_le_Nstar_sub_N` fixes the coefficient at `6`, which is the
mass-`3` haunted atom's cost.  Under `NoSmallHaunted m` a haunted ordinate carries
mass at least `m`, and the cost is `m(m−1)`.  This is the star analogue of
`Gaps.hauntedDensity_of_offLineImport_at_rung`, which does the same for the
off-line currency.
-/


theorem mass_card_le_Nstar_sub_N (D : ZeroData) (G : Finset ℝ) {m : ℕ} (hm : 1 ≤ m)
    (hG : ∀ γ ∈ G, m ≤ D.H γ) (hsub : G ⊆ D.ordinates.toFinset) :
    (m * (m - 1)) * G.card + D.N ≤ D.Nstar := by
  classical
  have hcount : ∀ γ ∈ G, m ≤ D.ordinates.count γ := by
    intro γ hγ; rw [← ZeroData.H_eq_count]; exact hG γ hγ
  have hNstar : D.Nstar = ∑ γ ∈ D.ordinates.toFinset,
      D.ordinates.count γ * D.ordinates.count γ := by
    obtain ⟨-, h2⟩ := ZeroData.N_Nstar_ordinate_functional D
    rw [h2, Finset.sum_multiset_map_count]
    simp [smul_eq_mul]
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.ordinates.count γ := by
    obtain ⟨h1, -⟩ := ZeroData.N_Nstar_ordinate_functional D
    rw [h1, ← Multiset.toFinset_sum_count_eq]
  have key : ∑ γ ∈ D.ordinates.toFinset,
      (D.ordinates.count γ + if γ ∈ G then m * (m - 1) else 0)
      ≤ ∑ γ ∈ D.ordinates.toFinset, D.ordinates.count γ * D.ordinates.count γ := by
    refine Finset.sum_le_sum fun γ _ => ?_
    by_cases hγ : γ ∈ G
    · have h3 : m ≤ D.ordinates.count γ := hcount γ hγ
      simp only [hγ, if_pos]
      have hc1 : 1 ≤ D.ordinates.count γ := le_trans hm h3
      have hmono : m * (m - 1) ≤ D.ordinates.count γ * (D.ordinates.count γ - 1) :=
        Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1)
      have hsplit : D.ordinates.count γ * (D.ordinates.count γ - 1) + D.ordinates.count γ
          = D.ordinates.count γ * D.ordinates.count γ := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc1
        rw [hk]; simp; ring
      omega
    · simp only [hγ, if_neg, add_zero, not_false_iff]
      nlinarith [Nat.zero_le (D.ordinates.count γ)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    Finset.sum_const] at key
  rw [hNstar, hN]
  simpa [smul_eq_mul, mul_comm, add_comm] using key



theorem haunted_rung_star (D : ZeroData) {m : ℕ} (hm : 1 ≤ m)
    (hmass : ∀ γ ∈ D.ordinates.toFinset.filter
        (fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1), m ≤ D.H γ) :
    (m * (m - 1)) * hauntedCount D + D.N ≤ D.Nstar := by
  classical
  have h := mass_card_le_Nstar_sub_N D _ hm hmass (Finset.filter_subset _ _)
  simpa [hauntedCount] using h

/-- **The star cost at rung `m`, and the threshold it moves.**  `SESSION 382`.

The star currency spends `(C − 1)/(m(m−1))` instead of `(C − 1)/6`, so it beats
the certified `(3κ − 1)/2` for every `C` below `1 + m(m−1)(1 − κ)/2`.  At
`m = 3` that reproduces `374`'s `793/400`; the ladder's own rungs move it far
out. -/
theorem star_rung_threshold {κ C D : ℝ} (hD : 0 < D) :
    (3 * κ - 1) / 2 < κ - (C - 1) / D ↔ 2 * (C - 1) < D * (1 - κ) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  constructor
  · intro h
    have h' : (C - 1) / D < (1 - κ) / 2 := by linarith
    rw [div_lt_div_iff₀ hD h2] at h'
    linarith
  · intro h
    have h' : (C - 1) / D < (1 - κ) / 2 := by
      rw [div_lt_div_iff₀ hD h2]; linarith
    linarith

/-- **`Blindness.star_rung_threshold` at ζ's `κ`, in exact rationals.**
`SESSION 382`.  Rungs `3`, `5`, `7`. -/
theorem star_rung_threshold_zeta :
    (1 : ℝ) + 3 * 2 * (1 - 269 / 400) / 2 = 793 / 400
      ∧ (1 : ℝ) + 5 * 4 * (1 - 269 / 400) / 2 = 1710 / 400
      ∧ (1 : ℝ) + 7 * 6 * (1 - 269 / 400) / 2 = 3151 / 400 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩


/-- **The distinct-zeros deficit at a ladder rung.**  `SESSION 384`.

`two_mul_haunted_add_atomCount_le_N` charges a haunted ordinate `2` into
`N − atomCount`, which is the mass-`3` atom's `H − 1`.  Under `NoSmallHaunted m`
it is `m − 1`.  Third of the three rung combinations, after the off-line one
(`Gaps.hauntedDensity_of_offLineImport_at_rung`) and the star one (`383`). -/
theorem haunted_rung_deficit (D : ZeroData) {m : ℕ} (hm : 1 ≤ m)
    (hmass : ∀ γ ∈ D.ordinates.toFinset.filter
        (fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1), m ≤ D.H γ) :
    (m - 1) * hauntedCount D + atomCount D ≤ D.N := by
  classical
  set G := D.ordinates.toFinset.filter
    (fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1) with hGdef
  have hsub : G ⊆ D.ordinates.toFinset := Finset.filter_subset _ _
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := N_eq_sum_H D
  have hA : atomCount D = ∑ γ ∈ D.ordinates.toFinset, 1 := by
    rw [atomCount]; simp
  have key : ∑ γ ∈ D.ordinates.toFinset, (1 + if γ ∈ G then m - 1 else 0)
      ≤ ∑ γ ∈ D.ordinates.toFinset, D.H γ := by
    refine Finset.sum_le_sum fun γ hγ => ?_
    by_cases h : γ ∈ G
    · have hmH : m ≤ D.H γ := hmass γ h
      simp only [h, if_pos]; omega
    · simp only [h, if_neg, add_zero, not_false_iff]
      exact one_le_H_of_mem hγ
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    Finset.sum_const] at key
  rw [hN, hA]
  simpa [hauntedCount, hGdef, smul_eq_mul, mul_comm, add_comm] using key

/-- **`Blindness.rung_coefficients_attained`: both rung coefficients are exact, at
every odd rung.**  `SESSION 385`.

`382`–`384` charge a haunted ordinate `m(m−1)` into `N⊛ − N` and `m − 1` into
`N − atomCount` under `NoSmallHaunted m`.  The mass-`m` haunted atom makes **both
equalities**, so neither coefficient can be improved by sharpening the same
argument.  `374`'s `star_route_attained` is the `j = 1` case.

`configAt 0 1 j a` is one on-line zero shadowed by `j` off-line pairs: mass
`m = 1 + 2j`, `onAt = 1`, so it is haunted for every `j ≥ 1`. -/
theorem rung_coefficients_attained {a : ℝ} (ha : a ≠ 1/2) {j : ℕ} (hj : 1 ≤ j) :
    let D := configAt 0 1 j a
    let m := 1 + 2 * j
    D.N = m ∧ D.Nstar = m * m ∧ atomCount D = 1 ∧ hauntedCount D = 1
      ∧ (m * (m - 1)) * hauntedCount D + D.N = D.Nstar
      ∧ (m - 1) * hauntedCount D + atomCount D = D.N := by
  classical
  intro D m
  have p : profile D = {(1 + 2 * j, 2 * j)} := by
    simpa using configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := j) (by omega)
  have hN : D.N = m := by
    show D.N = 1 + 2 * j
    rw [configAt_N]
  have hS : D.Nstar = m * m := by
    show D.Nstar = (1 + 2 * j) * (1 + 2 * j)
    rw [Nstar_from_profile, p]; simp
  have hA : atomCount D = 1 := by
    rw [atomCount, configAt_ordinates]
    rw [Multiset.toFinset_replicate]
    simp
  have hH : ∀ γ, D.H γ = if γ = 0 then 1 + 2 * j else 0 := fun γ => configAt_H 0 γ 1 j a
  have hoff : offAt D (0:ℝ) = 2 * j := offAt_configAt_self ha 0 1 j
  have hh : hauntedCount D = 1 := by
    rw [hauntedCount, configAt_ordinates, Multiset.toFinset_replicate]
    simp only [show 1 + 2 * j ≠ 0 by omega, if_neg, not_false_iff]
    rw [Finset.filter_singleton]
    rw [if_pos]
    · simp
    · refine ⟨?_, ?_⟩
      · rw [hH, if_pos rfl, hoff]; omega
      · rw [hH, if_pos rfl]; omega
  refine ⟨hN, hS, hA, hh, ?_, ?_⟩
  · rw [hh, hN, hS]
    show (1 + 2*j) * (1 + 2*j - 1) * 1 + (1+2*j) = (1+2*j) * (1+2*j)
    have hsub : 1 + 2*j - 1 = 2*j := by omega
    rw [hsub]; ring
  · rw [hh, hA, hN]; show (1 + 2*j - 1) * 1 + 1 = 1 + 2*j
    omega

/-! #### The rung, at every moment order — `SESSION 386`

`382` charged a haunted ordinate `m(m−1)` into `N⊛ − N`, which is the `k = 2`
case.  The same argument runs at every order: mass `m` costs `m^k − m` into
`momentK k − N`.  `momentK_charges_every_class` is the `k`-general statement with
the base fixed at mass `3`; this fixes the order and generalises the mass.

**And the same atom saturates all of them** (`rung_momentK_attained`), which
answers the question `385` left open: the improvement it asked for cannot come
from a higher moment.
-/

theorem pow_sub_self_mono {k : ℕ} (hk : 1 ≤ k) :
    ∀ x y : ℕ, x ≤ y → x ^ k + y ≤ y ^ k + x := by
  intro x y hxy
  induction y with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge x (n + 1) with h | h
      · have hxn : x ≤ n := by omega
        have hstep : n ^ k < (n + 1) ^ k :=
          Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)
        have := ih hxn
        omega
      · have hx : x = n + 1 := by omega
        subst hx; omega

theorem mass_card_le_momentK_sub_N (D : ZeroData) (G : Finset ℝ) {m k : ℕ} (hk : 1 ≤ k)
    (hG : ∀ γ ∈ G, m ≤ D.H γ) (hsub : G ⊆ D.ordinates.toFinset) :
    (m ^ k - m) * G.card + D.N ≤ momentK D k := by
  classical
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := N_eq_sum_H D
  have key : ∑ γ ∈ D.ordinates.toFinset, (D.H γ + if γ ∈ G then m ^ k - m else 0)
      ≤ ∑ γ ∈ D.ordinates.toFinset, D.H γ ^ k := by
    refine Finset.sum_le_sum fun γ hγ => ?_
    by_cases h : γ ∈ G
    · have hmH : m ≤ D.H γ := hG γ h
      have := pow_sub_self_mono hk m (D.H γ) hmH
      have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
      simp only [h, if_pos]; omega
    · simp only [h, if_neg, add_zero, not_false_iff]
      have h1 : 1 ≤ D.H γ := one_le_H_of_mem hγ
      exact Nat.le_self_pow (by omega) _
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    Finset.sum_const] at key
  rw [hN, momentK]
  simpa [smul_eq_mul, mul_comm, add_comm] using key

theorem haunted_rung_momentK (D : ZeroData) {m k : ℕ} (hk : 1 ≤ k)
    (hmass : ∀ γ ∈ D.ordinates.toFinset.filter
        (fun γ => D.H γ - offAt D γ = 1 ∧ D.H γ ≠ 1), m ≤ D.H γ) :
    (m ^ k - m) * hauntedCount D + D.N ≤ momentK D k := by
  classical
  have h := mass_card_le_momentK_sub_N D _ hk hmass (Finset.filter_subset _ _)
  simpa [hauntedCount] using h

theorem rung_momentK_attained {a : ℝ} (ha : a ≠ 1/2) {j : ℕ} (hj : 1 ≤ j)
    {k : ℕ} (hk : 1 ≤ k) :
    let D := configAt 0 1 j a
    let m := 1 + 2 * j
    momentK D k = m ^ k
      ∧ (m ^ k - m) * hauntedCount D + D.N = momentK D k := by
  classical
  intro D m
  have p : profile D = {(1 + 2 * j, 2 * j)} := by
    simpa using configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := j) (by omega)
  have hM : momentK D k = m ^ k := by
    show momentK D k = (1 + 2 * j) ^ k
    rw [momentK_from_profile, p]; simp
  obtain ⟨hN, -, -, hh, -, -⟩ := rung_coefficients_attained ha hj
  refine ⟨hM, ?_⟩
  rw [hh, hM, hN]
  have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
  omega

/-- **The on-line family cannot see haunting at all.**  `SESSION 387`.

`386` left three places an improved haunted bound could come from: the on-line
family, the profile's second coordinate, or outside the blindness apparatus.
**This closes the first.**

A haunted ordinate has `onAt = 1` by definition, which is exactly what a simple
zero has — so the on-line statistics cannot separate them.  `350`'s pair witnesses
it: `configAt 0 1 0 a` (mass `1`, simple) and `configAt 0 1 1 a` (mass `3`,
haunted) agree on **every** `onMoment` and on `NscStd`, while `hauntedCount` is
`0` against `1`.

So no bound of the form `hauntedCount ≤ δ·N` can be derived from on-line data,
however much of it is supplied.  The second place is not open either — the
profile's second coordinate *is* `Noff`, and
`Gaps.hauntedDensity_of_offLineImport` has been spending it since it was written. -/
theorem hauntedCount_not_determined_by_on_moments {a : ℝ} (ha : a ≠ 1/2) :
    (∀ p, onMoment (configAt 0 1 0 a) p = onMoment (configAt 0 1 1 a) p)
      ∧ (configAt 0 1 0 a).NscStd = (configAt 0 1 1 a).NscStd
      ∧ hauntedCount (configAt 0 1 0 a) = 0
      ∧ hauntedCount (configAt 0 1 1 a) = 1 := by
  classical
  obtain ⟨hm, hsc0, hsc1, -⟩ := Nsc_not_determined_by_on_moments ha
  have hstd0 : (configAt 0 1 0 a).NscStd = 1 := by
    have p0 : profile (configAt 0 1 0 a) = {(1, 0)} := by
      simpa using configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 0) (by omega)
    have : ((configAt 0 1 0 a).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, p0]; decide
    exact_mod_cast this
  have hstd1 : (configAt 0 1 1 a).NscStd = 1 := by
    have p1 : profile (configAt 0 1 1 a) = {(3, 2)} := by
      simpa using configAt_profile (γ := (0:ℝ)) ha (k := 1) (j := 1) (by omega)
    have : ((configAt 0 1 1 a).NscStd : ℤ) = 1 := by
      rw [NscStd_from_profile, p1]; decide
    exact_mod_cast this
  refine ⟨hm, by rw [hstd0, hstd1], ?_, ?_⟩
  · rw [hauntedCount_eq_NscStd_sub_Nsc, hstd0, hsc0]
  · rw [hauntedCount_eq_NscStd_sub_Nsc, hstd1, hsc1]

/-! #### The last two internal channels, both closed — `SESSION 390`

`387` concluded that every route to a better haunted bound inside the blindness
apparatus is exhausted.  Two channels had not actually been checked.

**Odd atoms.**  Every haunted ordinate has odd mass (`1 + even`), so
`hauntedCount ≤ oddAtoms`.  That looks like a fifth `HauntedDensity` supplier and
is not one: `NscStd_le_oddAtoms` puts `oddAtoms` *above* `NscStd`, which the
certified row already holds at `269/400`, so any `oddAtoms ≤ c·N` forces
`c ≥ 269/400` — four times the unconditional `δ = 131/800` the project already
spends.  The channel is circular: bounding `oddAtoms` usefully needs the `Nsc`
lower bound it would supply.

**Factorial moments.**  `factMoment k` sums `descFactorial (H γ) k`, a polynomial
in the mass, so it is a `ℤ`-linear combination of `momentK 0 … k` — and `386`'s
atom attains every one of those, hence any combination.  `factMoment_atom`
records the atom's value directly: `descFactorial m k`.
-/

theorem hauntedCount_le_oddAtoms (D : ZeroData) : hauntedCount D ≤ oddAtoms D := by
  have h1 := hauntedCount_eq_NscStd_sub_Nsc D
  have h2 := NscStd_le_oddAtoms D
  omega

theorem oddAtoms_bound_cannot_beat_baseline {c κ : ℝ} (hκ : (269 : ℝ)/400 ≤ κ)
    (hle : κ ≤ c) : (131 : ℝ)/800 < c := by
  have : (131 : ℝ)/800 < 269/400 := by norm_num
  linarith

theorem factMoment_atom (a : ℝ) (j k : ℕ) :
    factMoment (configAt 0 1 j a) k = Nat.descFactorial (1 + 2 * j) k := by
  classical
  rw [factMoment, configAt_ordinates, Multiset.toFinset_replicate]
  simp only [show 1 + 2 * j ≠ 0 by omega, if_neg, not_false_iff]
  rw [Finset.sum_singleton, configAt_H, if_pos rfl]

/-- **`Blindness.mass_cost_eq_iff`: the star rung's termwise charge closes at
mass `m` and nowhere above it.**  `SESSION 401`.

`382`'s `Blindness.mass_card_le_Nstar_sub_N` charges an ordinate of mass `≥ m`
the amount `m(m−1)` into `N⊛ − N`, and `Blindness.rung_coefficients_attained`
showed the mass-`m` haunted atom makes that an equality.  The statement below
adds the converse termwise: for `m ≤ c`, `c + m(m−1) = c²` holds precisely when
`c = m`, so an ordinate strictly heavier than the rung pays strictly more —
`Blindness.rung_coefficients_attained`'s mass is the only tight one. -/
theorem mass_cost_eq_iff {m c : ℕ} (hm : 1 ≤ m) (hc : m ≤ c) :
    c + m * (m - 1) = c * c ↔ c = m := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have had : a ≤ d := by omega
  simp only [Nat.add_sub_cancel]
  constructor
  · intro h
    have hq : a * a + a = d * d + d := by ring_nf at h ⊢; omega
    by_contra hne
    have hlt : a < d := by omega
    nlinarith [hq, hlt]
  · intro h
    have : d = a := by omega
    subst this; ring

/-- **Strict form of `Blindness.pow_sub_self_mono`.**  `SESSION 402`.

`386`'s lemma gives `x^k + y ≤ y^k + x` for `x ≤ y`.  `401` needed the strict
version and did not have it, which is why `Blindness.mass_cost_eq_iff` was
narrowed to `k = 2`.  The step that was missing is `x·P + y < y·P + x` for
`P = y^(k−1) ≥ 2` — a product of variables, which `omega` cannot see and
`nlinarith` closes once it is named. -/
theorem pow_sub_self_strict {k : ℕ} (hk : 2 ≤ k) {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x ^ k + y < y ^ k + x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hy : 2 ≤ y := by omega
  -- x^(j+2) ≤ x * y^(j+1) and y^(j+2) = y * y^(j+1)
  have h1 : x ^ (j + 2) ≤ x * y ^ (j + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left x (Nat.pow_le_pow_left (le_of_lt hxy) _)
  have h2 : y ^ (j + 2) = y * y ^ (j + 1) := by rw [pow_succ']
  have h4 : 2 ≤ y ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ y ^ 1 := Nat.pow_le_pow_left hy 1
    _ ≤ y ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : x * y ^ (j + 1) + y < y * y ^ (j + 1) + x := by
    nlinarith [hxy, h4]
  omega

/-- **`Blindness.mass_cost_eq_iff` at every order.**  `SESSION 402`.

`Blindness.mass_cost_eq_iff` (`401`) is the `k = 2` case, with the coefficient
written `m(m−1)` — the shape `Blindness.mass_card_le_Nstar_sub_N` spends.  This
is the same statement at every `k ≥ 2` with the coefficient `m^k − m`, the shape
`Blindness.mass_card_le_momentK_sub_N` spends.  Both are kept because their
consumers differ.

By `Blindness.rung_momentK_attained` together with the statement below, that
atom's mass is the unique tight one at every moment order, not only the
second. -/
theorem pow_cost_eq_iff {m c k : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) (hc : m ≤ c) :
    c + (m ^ k - m) = c ^ k ↔ c = m := by
  have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
  constructor
  · intro h
    by_contra hne
    have := pow_sub_self_strict hk hm (lt_of_le_of_ne hc (Ne.symm hne))
    omega
  · intro h; subst h; omega

/-- **`c = c^k` only at `c = 1`**, for `k ≥ 2` — the non-`G` half of the
characterisation.  `SESSION 404`. -/
theorem self_eq_pow_iff {c k : ℕ} (hc : 1 ≤ c) (hk : 2 ≤ k) : c = c ^ k ↔ c = 1 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 1 < c := by omega
    have := pow_sub_self_strict hk (le_refl 1) h2
    simp only [one_pow] at this
    omega
  · intro h; subst h; simp

/-- **When the rung bound is an equality — the global characterisation.**
`SESSION 404`.

`401` and `402` settled this termwise: an ordinate pays exactly `m^k − m` only at
mass `m`.  Summing, `Blindness.mass_card_le_momentK_sub_N` is an **equality**
exactly when every ordinate in `G` has mass `m` and every ordinate outside it is
simple.

Specialise at `G` = the haunted filter, whose card is `hauntedCount` by
definition, to read it as: the rung bound closes iff every haunted ordinate has
mass exactly `m` and nothing else carries multiplicity — which is the
configuration `Blindness.rung_coefficients_attained` exhibits. -/
theorem mass_card_eq_momentK_iff (D : ZeroData) (G : Finset ℝ) {m k : ℕ}
    (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hG : ∀ γ ∈ G, m ≤ D.H γ) (hsub : G ⊆ D.ordinates.toFinset) :
    (m ^ k - m) * G.card + D.N = momentK D k
      ↔ (∀ γ ∈ G, D.H γ = m) ∧ (∀ γ ∈ D.ordinates.toFinset, γ ∉ G → D.H γ = 1) := by
  classical
  have hN : D.N = ∑ γ ∈ D.ordinates.toFinset, D.H γ := N_eq_sum_H D
  have hterm : ∀ γ ∈ D.ordinates.toFinset,
      D.H γ + (if γ ∈ G then m ^ k - m else 0) ≤ D.H γ ^ k := by
    intro γ hγ
    by_cases h : γ ∈ G
    · have hmH : m ≤ D.H γ := hG γ h
      have := pow_sub_self_mono (by omega : 1 ≤ k) m (D.H γ) hmH
      have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
      simp only [h, if_pos]; omega
    · simp only [h, if_neg, add_zero, not_false_iff]
      exact Nat.le_self_pow (by omega) _
  have hsum : (m ^ k - m) * G.card + D.N
      = ∑ γ ∈ D.ordinates.toFinset, (D.H γ + if γ ∈ G then m ^ k - m else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
      Finset.sum_const, hN]
    simp [smul_eq_mul, mul_comm, add_comm]
  rw [hsum, momentK, Finset.sum_eq_sum_iff_of_le hterm]
  constructor
  · intro h
    refine ⟨fun γ hγ => ?_, fun γ hγ hnot => ?_⟩
    · have hs := h γ (hsub hγ)
      simp only [hγ, if_pos] at hs
      have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
      exact (pow_cost_eq_iff hm hk (hG γ hγ)).1 (by omega)
    · have hs := h γ hγ
      simp only [hnot, if_neg, add_zero, not_false_iff] at hs
      exact (self_eq_pow_iff (one_le_H_of_mem hγ) hk).1 hs
  · rintro ⟨h1, h2⟩ γ hγ
    by_cases h : γ ∈ G
    · have hEq := h1 γ h
      simp only [h, if_pos, hEq]
      have hmk : m ≤ m ^ k := Nat.le_self_pow (by omega) m
      omega
    · have hEq := h2 γ hγ h
      simp only [h, if_neg, add_zero, not_false_iff, hEq]
      simp

end Blindness
end Riemann
