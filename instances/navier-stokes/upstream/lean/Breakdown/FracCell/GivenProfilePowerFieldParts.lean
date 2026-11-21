import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenProfileBoundsFieldParts
import Breakdown.FracCell.GivenProfilePowerFieldJumps

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePowerParts

open CellCert.GivenFields SteadyCert

private theorem rpow_neg_three_eq {a : ℝ} (ha : 0 < a) : a ^ (-(3 : ℝ)) = (a ^ 3)⁻¹ := by
  rw [Real.rpow_neg ha.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem second_decay {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ C : ℝ, ∀ y : Space, ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  obtain ⟨R, C, hfar⟩ := FracCellInternal.fieldOf_far_bounds P hP D hD |β|
  set R1 : ℝ := max R 1 with hR1
  have hR1one : 1 ≤ R1 := le_max_right _ _
  obtain ⟨K, hK⟩ := _root_.Breakdown.FracInternal.fieldOf_fderiv_slopeOn hP hD β (R1 + 1)
  refine ⟨8 * |C| + (K : ℝ) * (1 + R1) ^ 3, fun y => ?_⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  rw [rpow_neg_three_eq hpos]
  have hinv0 : 0 ≤ ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
  by_cases hy : R1 ≤ ‖y‖
  · have hyR : R ≤ ‖y‖ := le_trans (le_max_left _ _) hy
    have hy1 : 1 ≤ ‖y‖ := le_trans hR1one hy
    have hypos : 0 < ‖y‖ := by linarith
    obtain ⟨-, -, hslope⟩ := hfar β le_rfl y hyR
    have hb := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hslope
    rw [Real.coe_toNNReal', rpow_neg_three_eq hypos] at hb
    have h1 : max (C * (‖y‖ ^ 3)⁻¹) 0 ≤ |C| * (‖y‖ ^ 3)⁻¹ := by
      have : 0 ≤ (‖y‖ ^ 3)⁻¹ := by positivity
      refine max_le ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self C) this
    have h2 : (‖y‖ ^ 3)⁻¹ = 8 * ((2 * ‖y‖) ^ 3)⁻¹ := by
      field_simp
      ring
    have h3 : ((2 * ‖y‖) ^ 3)⁻¹ ≤ ((1 + ‖y‖) ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) 3)
    have h4 : 0 ≤ (K : ℝ) * (1 + R1) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
    calc ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ |C| * (‖y‖ ^ 3)⁻¹ := hb.trans h1
      _ = 8 * |C| * ((2 * ‖y‖) ^ 3)⁻¹ := by rw [h2]; ring
      _ ≤ 8 * |C| * ((1 + ‖y‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (8 * |C| + (K : ℝ) * (1 + R1) ^ 3) * ((1 + ‖y‖) ^ 3)⁻¹ := by nlinarith
  · replace hy : ‖y‖ < R1 := not_le.1 hy
    have hnhds : Metric.closedBall (0 : Space) (R1 + 1) ∈ nhds y := by
      refine Metric.closedBall_mem_nhds_of_mem ?_
      rw [mem_ball_zero_iff]
      linarith
    have hb := norm_fderiv_le_of_lipschitzOn ℝ hnhds hK
    have hratio : 1 ≤ (1 + R1) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (one_le_div (by positivity)).2 (pow_le_pow_left₀ hpos.le (by linarith) 3)
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    have h5 : 0 ≤ 8 * |C| * ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
    calc ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ (K : ℝ) := hb
      _ = (K : ℝ) * 1 := by ring
      _ ≤ (K : ℝ) * ((1 + R1) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hratio hK0
      _ ≤ (8 * |C| + (K : ℝ) * (1 + R1) ^ 3) * ((1 + ‖y‖) ^ 3)⁻¹ := by nlinarith

theorem fieldOf_contDiff {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) : ContDiff ℝ 1 (fieldOf P D β) := by
  exact _root_.Breakdown.FracInternal.fieldOf_contDiff hP hD β

theorem fieldOf_second_parts {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ H : Space → (Space →L[ℝ] Space →L[ℝ] Space),
      IsWeakSecondDerivOf (fun y => fderiv ℝ (fieldOf P D β) y) H ∧ AEStronglyMeasurable H volume ∧
        (∃ C : ℝ, ∀ y : Space, ‖H y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))) ∧
          ∃ K : ℝ, ∀ h : Space, ‖h‖ ≤ 1 →
            ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖ ≤ K * ‖h‖ := by
  obtain ⟨hw, hm⟩ := weakSecond_of_slopeOn
    (_root_.Breakdown.FracInternal.fieldOf_fderiv_slopeOn hP hD β)
  exact ⟨fderiv ℝ (fderiv ℝ (fieldOf P D β)), hw, hm, second_decay hP hD β,
    ProfilePowerJumps.fieldOf_second_weighted_modulus hP hD β⟩

end ProfilePowerParts

end FracInternal

end Breakdown
