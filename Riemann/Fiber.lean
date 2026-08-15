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
theorem NscStd_determined {D D' : ZeroData} (hord : D.ordinates = D'.ordinates)
    (hoff : ∀ γ, offAt D γ = offAt D' γ) : D.NscStd = D'.NscStd := by
  classical
  have hon : onOrd D = onOrd D' := by
    refine Multiset.ext.2 fun γ => ?_
    rw [count_onOrd, count_onOrd]
    exact onAt_determined hord hoff γ
  rw [NscStd_eq_onOrd_functional, NscStd_eq_onOrd_functional, hon]

end Blindness
end Riemann
