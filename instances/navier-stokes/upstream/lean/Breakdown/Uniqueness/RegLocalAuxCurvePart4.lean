import Breakdown.Uniqueness.RegLocalAuxSymm

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem rpow_two_eq (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

private theorem aesm_comp_sub {q : Space → ℂ} (hq : AEStronglyMeasurable q volume) (ξ : Space) :
    AEStronglyMeasurable (fun η => q (ξ - η)) volume :=
  hq.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)

private theorem lintegral_mul_comp_sub_le {p q : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) (ξ : Space) :
    ∫⁻ η, ‖p η‖ₑ * ‖q (ξ - η)‖ₑ ≤
      (∫⁻ η, ‖p η‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ η, ‖q η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hp.enorm
    (aesm_comp_sub hq ξ).enorm
  simp only [Pi.mul_apply, rpow_two_eq] at h2
  have e : ∫⁻ η, ‖q (ξ - η)‖ₑ ^ 2 = ∫⁻ η, ‖q η‖ₑ ^ 2 :=
    lintegral_sub_left_eq_self (fun η => ‖q η‖ₑ ^ 2) ξ
  rw [e] at h2
  exact h2

theorem enorm_convC_le {p q : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) (ξ : Space) :
    ‖convC p q ξ‖ₑ ≤ (∫⁻ η, ‖p η‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ η, ‖q η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have h1 : ‖convC p q ξ‖ₑ ≤ ∫⁻ η, ‖p η‖ₑ * ‖q (ξ - η)‖ₑ := by
    unfold convC
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext η
    rw [enorm_mul]
  exact h1.trans (lintegral_mul_comp_sub_le hp hq ξ)

theorem integrable_convC_integrand {p q : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) (hp2 : ∫⁻ η, ‖p η‖ₑ ^ 2 ≠ ⊤) (hq2 : ∫⁻ η, ‖q η‖ₑ ^ 2 ≠ ⊤)
    (ξ : Space) : Integrable (fun η => p η * q (ξ - η)) volume := by
  refine ⟨hp.mul (aesm_comp_sub hq ξ), ?_⟩
  show ∫⁻ η, ‖p η * q (ξ - η)‖ₑ < ⊤
  simp only [enorm_mul]
  refine lt_of_le_of_lt (lintegral_mul_comp_sub_le hp hq ξ) ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hp2)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hq2)

theorem convC_sub_left {p p' q : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hp' : AEStronglyMeasurable p' volume) (hq : AEStronglyMeasurable q volume)
    (hp2 : ∫⁻ η, ‖p η‖ₑ ^ 2 ≠ ⊤) (hp2' : ∫⁻ η, ‖p' η‖ₑ ^ 2 ≠ ⊤) (hq2 : ∫⁻ η, ‖q η‖ₑ ^ 2 ≠ ⊤)
    (ξ : Space) : convC p q ξ - convC p' q ξ = convC (fun η => p η - p' η) q ξ := by
  unfold convC
  rw [← integral_sub (integrable_convC_integrand hp hq hp2 hq2 ξ)
    (integrable_convC_integrand hp' hq hp2' hq2 ξ)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [sub_mul]

theorem convC_sub_right {p q q' : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) (hq' : AEStronglyMeasurable q' volume)
    (hp2 : ∫⁻ η, ‖p η‖ₑ ^ 2 ≠ ⊤) (hq2 : ∫⁻ η, ‖q η‖ₑ ^ 2 ≠ ⊤) (hq2' : ∫⁻ η, ‖q' η‖ₑ ^ 2 ≠ ⊤)
    (ξ : Space) : convC p q ξ - convC p q' ξ = convC p (fun η => q η - q' η) ξ := by
  unfold convC
  rw [← integral_sub (integrable_convC_integrand hp hq hp2 hq2 ξ)
    (integrable_convC_integrand hp hq' hp2 hq2' ξ)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [mul_sub]

end Breakdown.SmoothFlow
