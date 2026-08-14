/-
# Rung 0, certified: no gain past the known range

The census's `#10` (`ISSUES.md` #25) records that extending a certificate's
support past the range where `F` is *known* buys nothing, and is in fact
harmful.  The ladder audit (`FAILURES.md`, W34d) found that this rung — the one
the ladder brief listed as **owned** — existed here only as prose.  This file
pays that debt.

**What is actually true, and it is elementary.**  Suppose a linear functional
`∑ K i · F i` is to be bounded below, where `F` is *pinned* on a known set and
only *nonnegative* outside it.  Then:

* if `K` is negative anywhere outside the known set, the adversary sends that
  coordinate to `+∞` and the program is **unbounded below** — the certificate
  proves nothing;
* if `K` is nonnegative outside, the adversary sets those coordinates to `0`,
  and the value is **exactly** `∑_{known} K · F₀`.

Either way the value depends only on `K` restricted to the known set.  **So a
multiplier supported beyond the known range attains exactly what its restriction
attains, and nothing more.**  That is the capacity statement, and the class it
is a capacity for is `{F pinned on `known`, F ≥ 0 outside}` — which is
`{F on [0,1], F ≥ 0}` in the pair-correlation instance.

**Kill condition, stated before the file was written:** *if the statement could
not be made without assuming the LP duality it is meant to establish, it dies
and the debt is permanent.*  It did not fire — and the reason is worth
recording: **no duality theorem is used here at all.**  The register's certified
reason says "Lemma 1 + LP duality"; the capacity half needs neither.  It is an
infimum computed directly, by exhibiting the adversary's move.

Nothing in this file mentions `ζ`, `F`, or pair correlation.  That is the point:
a capacity claim about a convex program is not a theorem about the zeros, which
is exactly why it was reachable without any arithmetic input.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

namespace Riemann
namespace Capacity

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The admissible set: `F` is **pinned** to `F₀` on `known`, and merely
**nonnegative** outside it.  This is all the certificate class is entitled to
assume — the known range plus positivity. -/
def Admissible (known : Finset ι) (F₀ F : ι → ℝ) : Prop :=
  (∀ i ∈ known, F i = F₀ i) ∧ (∀ i ∉ known, 0 ≤ F i)

/-- The adversary's cheapest move: keep the pinned values, and put nothing at
all outside. -/
noncomputable def zeroOutside (known : Finset ι) (F₀ : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ known then F₀ i else 0

lemma admissible_zeroOutside (known : Finset ι) (F₀ : ι → ℝ) :
    Admissible known F₀ (zeroOutside known F₀) := by
  constructor
  · intro i hi; simp [zeroOutside, hi]
  · intro i hi; simp [zeroOutside, hi]

lemma sum_zeroOutside (S known : Finset ι) (hsub : known ⊆ S) (K F₀ : ι → ℝ) :
    ∑ i ∈ S, K i * zeroOutside known F₀ i = ∑ i ∈ known, K i * F₀ i := by
  classical
  rw [← Finset.sum_sdiff hsub]
  have h1 : ∑ i ∈ S \ known, K i * zeroOutside known F₀ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ∉ known := (Finset.mem_sdiff.1 hi).2
    simp [zeroOutside, this]
  have h2 : ∑ i ∈ known, K i * zeroOutside known F₀ i = ∑ i ∈ known, K i * F₀ i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [zeroOutside, hi]
  rw [h1, h2, zero_add]

/-! ### The two halves of the capacity statement -/

/-- **A nonnegative multiplier outside the known range buys nothing.**  Every
admissible `F` gives at least the pinned value, and `zeroOutside` attains it —
so the infimum is exactly `∑_{known} K · F₀`, a quantity that does not see `K`
outside `known` at all. -/
theorem pinned_value_is_floor (S known : Finset ι) (hsub : known ⊆ S)
    (K F₀ F : ι → ℝ) (hK : ∀ i ∈ S, i ∉ known → 0 ≤ K i)
    (hF : Admissible known F₀ F) :
    ∑ i ∈ known, K i * F₀ i ≤ ∑ i ∈ S, K i * F i := by
  classical
  rw [← Finset.sum_sdiff hsub]
  have hout : 0 ≤ ∑ i ∈ S \ known, K i * F i := by
    refine Finset.sum_nonneg fun i hi => ?_
    obtain ⟨hiS, hik⟩ := Finset.mem_sdiff.1 hi
    exact mul_nonneg (hK i hiS hik) (hF.2 i hik)
  have hin : ∑ i ∈ known, K i * F i = ∑ i ∈ known, K i * F₀ i :=
    Finset.sum_congr rfl fun i hi => by rw [hF.1 i hi]
  rw [hin]
  linarith

/-- …and the floor is attained. -/
theorem pinned_value_attained (S known : Finset ι) (hsub : known ⊆ S)
    (K F₀ : ι → ℝ) :
    ∃ F, Admissible known F₀ F ∧ ∑ i ∈ S, K i * F i = ∑ i ∈ known, K i * F₀ i :=
  ⟨zeroOutside known F₀, admissible_zeroOutside known F₀,
    sum_zeroOutside S known hsub K F₀⟩

/-- **A negative multiplier outside the known range is fatal.**  If `K` dips
below zero anywhere the class does not pin `F`, the program is unbounded below:
for *every* target `B` there is an admissible `F` undercutting it.  The
certificate then proves nothing at all — which is the precise sense in which
extending support is not merely useless but *harmful*. -/
theorem unbounded_below_of_neg_outside (S known : Finset ι) (hsub : known ⊆ S)
    (K F₀ : ι → ℝ) {u : ι} (huS : u ∈ S) (huk : u ∉ known) (hKu : K u < 0)
    (B : ℝ) : ∃ F, Admissible known F₀ F ∧ ∑ i ∈ S, K i * F i < B := by
  classical
  set P : ℝ := ∑ i ∈ known, K i * F₀ i with hP
  have hneg : 0 < -K u := by linarith
  set s : ℝ := (P - B + 1) / (-K u) with hs
  set t : ℝ := max 0 s with hti
  have htnn : 0 ≤ t := le_max_left _ _
  have hts : s ≤ t := le_max_right _ _
  refine ⟨fun i => if i ∈ known then F₀ i else if i = u then t else 0, ⟨?_, ?_⟩, ?_⟩
  · intro i hi; simp [hi]
  · intro i hi
    by_cases h : i = u
    · simp only [if_neg hi, if_pos h]; exact htnn
    · simp [hi, h]
  · have hmem : u ∈ S \ known := Finset.mem_sdiff.2 ⟨huS, huk⟩
    rw [← Finset.sum_sdiff hsub]
    have hout : ∑ i ∈ S \ known,
        K i * (if i ∈ known then F₀ i else if i = u then t else 0) = K u * t := by
      refine Finset.sum_eq_single_of_mem u hmem (fun b hb hne => ?_) |>.trans ?_
      · have hbk : b ∉ known := (Finset.mem_sdiff.1 hb).2
        simp [hbk, hne]
      · simp [huk]
    have hin : ∑ i ∈ known,
        K i * (if i ∈ known then F₀ i else if i = u then t else 0) = P := by
      rw [hP]
      exact Finset.sum_congr rfl fun i hi => by simp [hi]
    rw [hout, hin]
    have hle : K u * t ≤ K u * s := by
      have := mul_le_mul_of_nonpos_left hts (le_of_lt hKu)
      linarith [this]
    have hcancel : s * (-K u) = P - B + 1 :=
      div_mul_cancel₀ (P - B + 1) (ne_of_gt hneg)
    have hval : K u * s = B - P - 1 := by nlinarith [hcancel]
    linarith [hle, hval.le, hval.ge]


/-! ### The capacity statement itself

The two halves combine into the sentence the census entry wanted: **the value a
certificate can guarantee is exactly the pinned sum**, so it depends only on the
multiplier's restriction to the known range. -/

/-- **The program's guaranteed value is the pinned sum.**  `IsGreatest` says
both halves at once: the pinned sum is a valid guarantee, and no larger number
is. -/
theorem value_eq_pinned (S known : Finset ι) (hsub : known ⊆ S) (K F₀ : ι → ℝ)
    (hK : ∀ i ∈ S, i ∉ known → 0 ≤ K i) :
    IsGreatest {v : ℝ | ∀ F, Admissible known F₀ F → v ≤ ∑ i ∈ S, K i * F i}
      (∑ i ∈ known, K i * F₀ i) := by
  constructor
  · intro F hF
    exact pinned_value_is_floor S known hsub K F₀ F hK hF
  · rintro v hv
    obtain ⟨F, hFadm, hFval⟩ := pinned_value_attained S known hsub K F₀
    have := hv F hFadm
    rwa [hFval] at this

/-- **No gain past the known range.**  Two multipliers agreeing on `known`, both
admissible outside it, guarantee *exactly the same value* — however wildly they
differ beyond the range where `F` is pinned.

This is `FAILURES.md` `#10` / `ISSUES.md` `#25`, certified: extending a
certificate's support past the known range buys nothing.  Combined with
`unbounded_below_of_neg_outside`, the full statement is that the extension is
either worthless (`K ≥ 0` outside) or fatal (`K < 0` somewhere outside) — never
profitable. -/
theorem no_gain_past_known (S known : Finset ι) (hsub : known ⊆ S)
    (K K' F₀ : ι → ℝ) (hagree : ∀ i ∈ known, K i = K' i)
    (hK : ∀ i ∈ S, i ∉ known → 0 ≤ K i)
    (hK' : ∀ i ∈ S, i ∉ known → 0 ≤ K' i) :
    IsGreatest {v : ℝ | ∀ F, Admissible known F₀ F → v ≤ ∑ i ∈ S, K i * F i}
        (∑ i ∈ known, K i * F₀ i) ∧
      IsGreatest {v : ℝ | ∀ F, Admissible known F₀ F → v ≤ ∑ i ∈ S, K' i * F i}
        (∑ i ∈ known, K i * F₀ i) := by
  refine ⟨value_eq_pinned S known hsub K F₀ hK, ?_⟩
  have hsum : ∑ i ∈ known, K' i * F₀ i = ∑ i ∈ known, K i * F₀ i :=
    Finset.sum_congr rfl fun i hi => by rw [hagree i hi]
  have := value_eq_pinned S known hsub K' F₀ hK'
  rwa [hsum] at this

end Capacity
end Riemann
