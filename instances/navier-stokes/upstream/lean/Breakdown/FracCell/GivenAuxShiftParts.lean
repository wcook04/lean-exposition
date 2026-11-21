import Breakdown.FracCell.GivenAuxDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert SteadyCert

theorem weighted_pair_integrable (U : Space → Space) (hU : ContDiff ℝ 1 U) (C : ℝ)
    (hb : ∀ y, ‖U y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖fderiv ℝ U y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ))
    (ζ : Space → Space) (hζ : MemLp ζ 2 volume) :
    Integrable (fun y => ‖U y‖ ^ 2 * ‖ζ y‖ ^ 2) ∧
      Integrable (fun y => ‖y‖ ^ 2 * ‖fderiv ℝ U y‖ ^ 2 * ‖ζ y‖ ^ 2) := by
  have hC : 0 ≤ C := by
    have h0 := (hb 0).1
    have hpos : 0 < (1 + ‖(0 : Space)‖)⁻¹ := by positivity
    by_contra hneg
    have : C * (1 + ‖(0 : Space)‖)⁻¹ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    linarith [norm_nonneg (U 0)]
  have hζ2 : Integrable (fun y => ‖ζ y‖ ^ 2) := by
    simpa using hζ.integrable_norm_pow (p := 2) (by norm_num)
  have hUc : Continuous U := hU.continuous
  have hDc : Continuous (fun y => fderiv ℝ U y) := hU.continuous_fderiv (by norm_num)
  have hζm : AEStronglyMeasurable ζ volume := hζ.1
  constructor
  · refine (hζ2.const_mul (C ^ 2)).mono' ?_ ?_
    · exact ((hUc.norm.pow 2).aestronglyMeasurable).mul (hζm.norm.pow 2)
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have h1 : ‖U y‖ ≤ C := by
        have hinv : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
        calc ‖U y‖ ≤ C * (1 + ‖y‖)⁻¹ := (hb y).1
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hinv hC
          _ = C := mul_one C
      have h2 : ‖U y‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · refine (hζ2.const_mul (C ^ 2)).mono' ?_ ?_
    · exact (((continuous_norm.pow 2).mul (hDc.norm.pow 2)).aestronglyMeasurable).mul (hζm.norm.pow 2)
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have hr : 0 ≤ ‖y‖ := norm_nonneg y
      have hpos : 0 < 1 + ‖y‖ := by linarith
      have hrp : (1 + ‖y‖) ^ (-2 : ℝ) = ((1 + ‖y‖) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hpos.le]
        norm_cast
      have h1 : ‖y‖ * ‖fderiv ℝ U y‖ ≤ C := by
        have hk : ‖y‖ * ((1 + ‖y‖) ^ 2)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (by positivity)]
          nlinarith
        calc ‖y‖ * ‖fderiv ℝ U y‖ ≤ ‖y‖ * (C * (1 + ‖y‖) ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_left (hb y).2 hr
          _ = C * (‖y‖ * ((1 + ‖y‖) ^ 2)⁻¹) := by rw [hrp]; ring
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hk hC
          _ = C := mul_one C
      have h2 : (‖y‖ * ‖fderiv ℝ U y‖) ^ 2 ≤ C ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg _)) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖y‖ ^ 2 * ‖fderiv ℝ U y‖ ^ 2 * ‖ζ y‖ ^ 2 = (‖y‖ * ‖fderiv ℝ U y‖) ^ 2 * ‖ζ y‖ ^ 2 := by ring
        _ ≤ C ^ 2 * ‖ζ y‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)

end FracInternal

end Breakdown
