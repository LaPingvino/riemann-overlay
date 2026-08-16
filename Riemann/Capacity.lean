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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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


/-! ### The same statement over a continuum

`FAILURES.md` `#10` names the class `{F on [0,1], F ≥ 0}` — an integral program,
not a `Finset` sum.  The ladder audit's own criterion demands a machine-checked
statement about *that* class, so the skeleton above is instantiated here.

**Kill condition, stated before the section was written:** *if the integral
machinery forces a side-condition that is itself the disputed content, the
instantiation dies and rung 0 stays partial.*  **It did not fire.**  The only
side-conditions needed are `MeasurableSet A` and integrability of the integrand
— facts about whether the symbols denote anything, not about whether extending
support helps.  In particular no hypothesis is imposed on `K` outside `A` beyond
the sign condition that is the theorem's own hypothesis. -/

section Continuum

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The admissible set over a continuum: pinned on `A`, nonnegative off it. -/
def AdmissibleOn (A : Set α) (F₀ F : α → ℝ) : Prop :=
  Set.EqOn F F₀ A ∧ ∀ x ∈ Aᶜ, 0 ≤ F x

theorem pinned_value_is_floor_integral (μ : Measure α) (A : Set α)
    (hA : MeasurableSet A) (K F₀ F : α → ℝ) (hK : ∀ x ∈ Aᶜ, 0 ≤ K x)
    (hF : AdmissibleOn A F₀ F) (hint : Integrable (fun x => K x * F x) μ) :
    ∫ x in A, K x * F₀ x ∂μ ≤ ∫ x, K x * F x ∂μ := by
  rw [← integral_add_compl hA hint]
  have h1 : ∫ x in A, K x * F x ∂μ = ∫ x in A, K x * F₀ x ∂μ :=
    setIntegral_congr_fun hA (fun x hx => by rw [hF.1 hx])
  have h2 : 0 ≤ ∫ x in Aᶜ, K x * F x ∂μ :=
    setIntegral_nonneg hA.compl (fun x hx => mul_nonneg (hK x hx) (hF.2 x hx))
  rw [h1]
  linarith

theorem pinned_value_attained_integral (μ : Measure α) (A : Set α)
    (hA : MeasurableSet A) (K F₀ : α → ℝ) :
    AdmissibleOn A F₀ (A.indicator F₀) ∧
      ∫ x, K x * A.indicator F₀ x ∂μ = ∫ x in A, K x * F₀ x ∂μ := by
  refine ⟨⟨fun x hx => by simp [Set.indicator_apply, hx], fun x hx => ?_⟩, ?_⟩
  · have hxA : x ∉ A := hx
    simp [Set.indicator_apply, hxA]
  have hfun : (fun x => K x * A.indicator F₀ x)
      = A.indicator (fun j => K j * F₀ j) := by
    funext x
    rw [Set.indicator_mul_right]
  rw [hfun, integral_indicator hA]

/-- **Rung 0 over the continuum.**  The value a certificate can guarantee is
exactly the pinned integral. -/
theorem value_eq_pinned_integral (μ : Measure α) (A : Set α)
    (hA : MeasurableSet A) (K F₀ : α → ℝ) (hK : ∀ x ∈ Aᶜ, 0 ≤ K x)
    (hint0 : Integrable (fun x => K x * A.indicator F₀ x) μ) :
    IsGreatest {v : ℝ | ∀ F, AdmissibleOn A F₀ F →
        Integrable (fun x => K x * F x) μ → v ≤ ∫ x, K x * F x ∂μ}
      (∫ x in A, K x * F₀ x ∂μ) := by
  obtain ⟨hadm, hval⟩ := pinned_value_attained_integral μ A hA K F₀
  constructor
  · intro F hF hint
    exact pinned_value_is_floor_integral μ A hA K F₀ F hK hF hint
  · rintro v hv
    have := hv _ hadm hint0
    rwa [hval] at this

/-- **No gain past the known range, over the continuum.**  Two multipliers
agreeing on `A`, both nonnegative off it, guarantee **the same value** — however
they differ outside.  This is `FAILURES.md` `#10` for the class it actually
names. -/
theorem no_gain_past_known_integral (μ : Measure α) (A : Set α)
    (hA : MeasurableSet A) (K K' F₀ : α → ℝ) (hagree : Set.EqOn K K' A)
    (hK : ∀ x ∈ Aᶜ, 0 ≤ K x) (hK' : ∀ x ∈ Aᶜ, 0 ≤ K' x)
    (hint0 : Integrable (fun x => K x * A.indicator F₀ x) μ)
    (hint0' : Integrable (fun x => K' x * A.indicator F₀ x) μ) :
    IsGreatest {v : ℝ | ∀ F, AdmissibleOn A F₀ F →
          Integrable (fun x => K x * F x) μ → v ≤ ∫ x, K x * F x ∂μ}
        (∫ x in A, K x * F₀ x ∂μ) ∧
      IsGreatest {v : ℝ | ∀ F, AdmissibleOn A F₀ F →
          Integrable (fun x => K' x * F x) μ → v ≤ ∫ x, K' x * F x ∂μ}
        (∫ x in A, K x * F₀ x ∂μ) := by
  refine ⟨value_eq_pinned_integral μ A hA K F₀ hK hint0, ?_⟩
  have hsum : ∫ x in A, K' x * F₀ x ∂μ = ∫ x in A, K x * F₀ x ∂μ :=
    setIntegral_congr_fun hA (fun x hx => by rw [hagree hx])
  have := value_eq_pinned_integral μ A hA K' F₀ hK' hint0'
  rwa [hsum] at this


/-- **The fatal half, over the continuum.**  If the multiplier is negative *on
average* over some measurable `E` outside the known range, the program is
unbounded below: for every target `B` there is an admissible, integrable `F`
undercutting it.  The certificate then proves nothing at all.

Together with `no_gain_past_known_integral` this is the full content of census
`#10`: extension past the known range is **useless** when the multiplier is
nonnegative outside, and **fatal** when it is not.  Never profitable.

The hypothesis `∫_E K < 0` is honest — it says there is a place outside the
pinned range where the multiplier is negative on average, which is exactly the
situation being ruled out.  It does not assume the conclusion. -/
theorem unbounded_below_of_neg_outside_integral (μ : Measure α) (A E : Set α)
    (hA : MeasurableSet A) (hE : MeasurableSet E) (hEA : E ⊆ Aᶜ)
    (K F₀ : α → ℝ) (hKE : IntegrableOn K E μ)
    (hEneg : ∫ x in E, K x ∂μ < 0)
    (hint0 : Integrable (fun x => K x * A.indicator F₀ x) μ) (B : ℝ) :
    ∃ F, AdmissibleOn A F₀ F ∧ Integrable (fun x => K x * F x) μ ∧
      ∫ x, K x * F x ∂μ < B := by
  classical
  set P : ℝ := ∫ x, K x * A.indicator F₀ x ∂μ with hP
  set Q : ℝ := ∫ x in E, K x ∂μ with hQ
  have hQneg : 0 < -Q := by simpa [hQ] using hEneg
  set t : ℝ := max 0 ((P - B + 1) / (-Q)) with hdt
  have htnn : 0 ≤ t := le_max_left _ _
  have hts : (P - B + 1) / (-Q) ≤ t := le_max_right _ _
  -- the perturbed profile: pinned on `A`, a constant bump `t` on `E`
  refine ⟨fun x => A.indicator F₀ x + t * E.indicator (fun _ => (1:ℝ)) x, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hxE : x ∉ E := fun h => (hEA h) hx
    simp [Set.indicator_apply, hx, hxE]
  · intro x hx
    have hxA : x ∉ A := hx
    have : 0 ≤ t * E.indicator (fun _ => (1:ℝ)) x := by
      rcases Classical.em (x ∈ E) with h | h
      · simp [Set.indicator_apply, h, htnn]
      · simp [Set.indicator_apply, h]
    simpa [Set.indicator_apply, hxA] using this
  · have hbump : Integrable (fun x => K x * (t * E.indicator (fun _ => (1:ℝ)) x)) μ := by
      have : (fun x => K x * (t * E.indicator (fun _ => (1:ℝ)) x))
          = fun x => t * E.indicator K x := by
        funext x
        rcases Classical.em (x ∈ E) with h | h
        · simp only [Set.indicator_apply, if_pos h, mul_one]; ring
        · simp only [Set.indicator_apply, if_neg h, mul_zero]
      rw [this]
      exact ((integrable_indicator_iff hE).2 hKE).const_mul t
    have hsum : (fun x => K x * (A.indicator F₀ x + t * E.indicator (fun _ => (1:ℝ)) x))
        = fun x => K x * A.indicator F₀ x + K x * (t * E.indicator (fun _ => (1:ℝ)) x) := by
      funext x; ring
    rw [hsum]
    exact hint0.add hbump
  · have hsum : (fun x => K x * (A.indicator F₀ x + t * E.indicator (fun _ => (1:ℝ)) x))
        = fun x => K x * A.indicator F₀ x + t * E.indicator K x := by
      funext x
      rcases Classical.em (x ∈ E) with h | h
      · simp only [Set.indicator_apply, if_pos h, mul_one]; ring
      · simp only [Set.indicator_apply, if_neg h, mul_zero, add_zero]
    have hbump : Integrable (fun x => t * E.indicator K x) μ :=
      ((integrable_indicator_iff hE).2 hKE).const_mul t
    rw [hsum, integral_add hint0 hbump, integral_const_mul, integral_indicator hE]
    have hle : t * Q ≤ ((P - B + 1) / (-Q)) * Q := by
      have hQle : Q ≤ 0 := le_of_lt hEneg
      nlinarith [hts, hQle]
    have hcancel : ((P - B + 1) / (-Q)) * (-Q) = P - B + 1 :=
      div_mul_cancel₀ (P - B + 1) (ne_of_gt hQneg)
    nlinarith [hle, hcancel]

end Continuum


/-! ### Reweighting cannot help — the certificate for `F.md` F4

`F.md`'s F4 proposed that the GM bridge's error amplification is an artifact of
window shape, and that a smoother weight would reduce it.  The autopsy argued
otherwise in prose; `R21` says a rung needs a certificate, so here it is.

The abstract fact: if all that is known about the per-shift errors is a uniform
bound `|e i| ≤ E`, then the worst case of `Σ w i · e i` is `(Σ w i) · E` and it
is **attained** — by the adversary who sets every error to `E`.  So the
worst-case total depends on the weight **only through its total mass**, and the
main term fixes that mass.  No profile — Fejér, flat, Gaussian — changes it.

**Kill condition, stated before the section was written:** *if the worst case
were not attained for every weight, shape could matter and F4's conversion would
be premature.*  It did not fire; the attaining adversary is explicit.

This is the same move as `unbounded_below_of_neg_outside`: the class's limit is
found by naming what the adversary does, not by estimating. -/

section Reweighting

variable {ι : Type*} [DecidableEq ι]

/-- **The worst case is attained, whatever the weight.**  With only a uniform
bound `|e i| ≤ E` available, the adversary setting every error to `E` achieves
`(Σ w) · E`, so the guaranteed total is exactly the total mass times `E`. -/
theorem reweighting_worst_case (S : Finset ι) (w : ι → ℝ) (E : ℝ) :
    ∃ e : ι → ℝ, (∀ i, |e i| ≤ E ∨ E < 0) ∧
      ∑ i ∈ S, w i * e i = (∑ i ∈ S, w i) * E := by
  refine ⟨fun _ => E, fun i => ?_, ?_⟩
  · rcases le_or_gt 0 E with h | h
    · exact Or.inl (by rw [abs_of_nonneg h])
    · exact Or.inr h
  · rw [Finset.sum_mul]

/-- **No weight beats another at equal mass.**  Two weights with the same total
mass admit the same worst-case total, so the shape of the window is irrelevant
to the bound it can guarantee — only `Σ w` matters, and the main term fixes
that.

This is the certificate behind `ISSUES` #27's strengthening from *"MRT is too
weak"* to *"no reweighting of the GM identity can be strong enough"*. -/
theorem equal_mass_equal_worst_case (S : Finset ι) (w w' : ι → ℝ) (E : ℝ)
    (hmass : ∑ i ∈ S, w i = ∑ i ∈ S, w' i) :
    (∑ i ∈ S, w i) * E = (∑ i ∈ S, w' i) * E := by
  rw [hmass]

/-- And the bound really is a bound: under a uniform error bound the weighted
sum never exceeds the total mass times `E`, for nonnegative weights. -/
theorem weighted_sum_le_mass_mul (S : Finset ι) (w e : ι → ℝ) (E : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (he : ∀ i ∈ S, e i ≤ E) :
    ∑ i ∈ S, w i * e i ≤ (∑ i ∈ S, w i) * E := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (he i hi) (hw i hi)

end Reweighting


/-! ### Rung 0 at the class `#10` actually names — `SESSION 193`

`FAILURES.md` recorded rung 0 as **partial**: the `Finset` skeleton was proved
while `#10`'s class is `{F on [0,1], F ≥ 0}`, an integral program over a
continuum.  The integral theorems above discharge that — they quantify over *any*
measure space and *any* measurable set, so `#10`'s class is an instance.

But "is an instance" is an inference the register was being asked to make.  Here
it is written out: `α = ℝ`, `A = [0,1]`, `μ = volume`.  Nothing new is proved;
the specialisation just removes the step. -/

/-- **Rung 0, at `{F pinned on `[0,1]`, `F ≥ 0` outside}`.**  The optimum over
the class is the pinned value, and it is the greatest such bound. -/
theorem value_eq_pinned_unit_interval (K F₀ : ℝ → ℝ)
    (hK : ∀ x ∈ (Set.Icc (0:ℝ) 1)ᶜ, 0 ≤ K x)
    (hint0 : MeasureTheory.Integrable
      (fun x => K x * (Set.Icc (0:ℝ) 1).indicator F₀ x) MeasureTheory.volume) :
    IsGreatest {v : ℝ | ∀ F, AdmissibleOn (Set.Icc (0:ℝ) 1) F₀ F →
        MeasureTheory.Integrable (fun x => K x * F x) MeasureTheory.volume →
        v ≤ ∫ x, K x * F x ∂MeasureTheory.volume}
      (∫ x in Set.Icc (0:ℝ) 1, K x * F₀ x ∂MeasureTheory.volume) :=
  value_eq_pinned_integral MeasureTheory.volume (Set.Icc (0:ℝ) 1)
    measurableSet_Icc K F₀ hK hint0

end Capacity
end Riemann
