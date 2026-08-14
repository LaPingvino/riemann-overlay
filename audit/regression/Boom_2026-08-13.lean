import Riemann
open Filter
namespace Riemann
-- Is `farmer_ki` (quantified over an arbitrary `closePairs`) refutable?
theorem density_trivial (F : Family) : DensityNearLine F (fun _ => 1) := by
  intro δ hδ
  filter_upwards with T
  have : ((Multiset.card ((F.D T).Z.filter fun p => δ / Real.log T ≤ |p.1 - 1/2|) : ℕ) : ℝ)
      ≤ ((Multiset.card (F.D T).Z : ℕ) : ℝ) := by
    exact_mod_cast Multiset.card_le_card (Multiset.filter_le _ _)
  simpa [Family.Nz, ZeroData.N] using this

theorem boom : False := by
  obtain ⟨lam, hlam, c₁, hc₁, hcp⟩ :=
    farmer_ki (fun _ _ => 0) zetaFamily zetaFamily (fun _ => 1) (density_trivial _)
  have h := hcp.2 (c₁/2) (by linarith)
  have hne := zetaFamily.nonempty
  have : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [h, hne] with T hT hpos
    have h1 : (1:ℝ) ≤ zetaFamily.Nz T := by
      unfold Family.Nz; exact_mod_cast hpos
    nlinarith [mul_le_mul_of_nonneg_left h1 hc₁.le]
  exact this.exists.elim fun _ h => h
end Riemann
