import Breakdown.Uniqueness.FundSolPointwiseAux4

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

theorem integrable_kernelSecondDeriv_mul {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {x₀ : Space} (h0 : f x₀ = 0) (i j : Fin 3) :
    Integrable (fun y => kernelSecondDeriv i j (x₀ - y) * f y) :=
  Internal.integrable_kernelSecondDeriv_mul_aux hf hc h0 i j

theorem secondPartial_potential_eq_integral {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {x₀ : Space} (h0 : f x₀ = 0) (i j : Fin 3) :
    secondPartial (potential f) i j x₀ = ∫ y, kernelSecondDeriv i j (x₀ - y) * f y := by
  obtain ⟨L, hL, hfL⟩ := Internal.exists_slope_bound hf hc h0
  obtain ⟨M, hM⟩ := Internal.exists_secondPartial_bound hf hc i j
  obtain ⟨c₁, hc₁⟩ := Internal.exists_abs_potential_mollifier_le
  obtain ⟨c₂, hc₂⟩ := Internal.exists_abs_secondPartial_potential_mollifier_le
  refine Internal.eq_of_abs_sub_le
    (P := M * (4 * π)⁻¹ * (3 / 2 * volume.real (Metric.ball (0 : Space) 1)) +
      M * c₁ * volume.real (Metric.ball (0 : Space) 1))
    (Q := L * c₂ * volume.real (Metric.ball (0 : Space) 1) * 8 +
      L * (3 * volume.real (Metric.ball (0 : Space) 1) * 2)) fun ρ hρ => ?_
  have hK := contDiff_potential (contDiff_mollifier ρ) (Internal.hasCompactSupport_mollifier hρ)
  have hA : secondPartial (potential f) i j x₀ =
      ∫ y, secondPartial f i j y * kernel (x₀ - y) := by
    rw [secondPartial_potential hf hc, Internal.potential_apply]
  have e₁ := Internal.near_estimate hf hc hK.continuous hρ
    (fun z hz => potential_mollifier_eq_kernel hρ hz) (hc₁ ρ hρ) i j hM x₀
  have e₂ := Internal.far_estimate hf hc (Internal.continuous_secondPartial hK j i) h0 hρ hL hfL
    i j (fun z hz => by
      rw [Internal.secondPartial_potential_mollifier_far hρ hz, Internal.kernelSecondDeriv_symm])
    (fun z hz => hc₂ ρ hρ z hz j i)
  rw [Internal.integral_secondPartial_mul hf hc hK x₀ i j] at e₁
  rw [hA]
  refine (abs_sub_le _ _ _).trans ((add_le_add e₁ e₂).trans (le_of_eq ?_))
  field_simp
  ring

end Breakdown.FundSol
