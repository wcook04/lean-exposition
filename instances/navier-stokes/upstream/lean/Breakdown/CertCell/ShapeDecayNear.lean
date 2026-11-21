import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

theorem IsKeyFieldSmooth.bounded_on_ball {f : Space → Fin 3 → ℂ} (hf : IsKeyFieldSmooth f) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R →
      ‖f y‖ ≤ C ∧ ‖fderiv ℝ f y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C := by
  intro R
  have hK : IsCompact (Metric.closedBall (0 : Space) R) := isCompact_closedBall 0 R
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hf.smooth.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn
    (hf.smooth.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨L, hL⟩ := hf.gradient_slope_bound (R + 1)
  refine ⟨max (max C₀ C₁) L, fun y hy => ?_⟩
  have hyK : y ∈ Metric.closedBall (0 : Space) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy
  have hnhds : Metric.closedBall (0 : Space) (R + 1) ∈ nhds y := by
    refine Metric.closedBall_mem_nhds_of_mem ?_
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (hC₀ y hyK).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hC₁ y hyK).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (norm_fderiv_le_of_lipschitzOn ℝ hnhds hL).trans (le_max_right _ _)

end GivenShape

end CertCell

end Breakdown
