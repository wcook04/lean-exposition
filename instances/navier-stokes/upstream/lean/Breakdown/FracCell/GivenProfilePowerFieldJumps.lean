import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenProfileBoundsFieldParts
import Breakdown.FracCell.GivenProfilePowerFieldJumpsCover

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePowerJumps

open CellCert.GivenFields SteadyCert

private theorem rpow_neg_three_eq {a : ℝ} (ha : 0 < a) : a ^ (-(3 : ℝ)) = (a ^ 3)⁻¹ := by
  rw [Real.rpow_neg ha.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem weight_nonneg (y : Space) : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) :=
  Real.rpow_nonneg (by positivity) _

private theorem weight_le_one (y : Space) : (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ 1 := by
  rw [rpow_neg_three_eq (by positivity : (0 : ℝ) < 1 + ‖y‖)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg y]))

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

private theorem modulus_of_cover {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {M : ℝ}
    (hM : ∀ y, ‖H y‖ ≤ M)
    (hcov : ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∃ (B : Set Space) (g : Space → ℝ),
      MeasurableSet B ∧ IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) B ∧
      (∫ y in B, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ C * ‖h‖ ∧
      (∀ y, 0 ≤ g y) ∧ Integrable (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ)) * g y) ∧
      (∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * g y) ≤ C ∧
      ∀ y ∉ B, ‖H (y + h) - H y‖ ≤ ‖h‖ * g y) :
    ∃ K : ℝ, ∀ h : Space, ‖h‖ ≤ 1 →
      ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖ ≤ K * ‖h‖ := by
  obtain ⟨C, hC⟩ := hcov
  refine ⟨2 * |M| * C + C, fun h hh => ?_⟩
  obtain ⟨B, g, hB, hBi, hBint, hg0, hgi, hgint, hoff⟩ := hC h hh
  set w : Space → ℝ := fun y => (1 + ‖y‖) ^ (-(3 : ℝ)) with hw
  have hu : Integrable (fun y => 2 * |M| * B.indicator w y + ‖h‖ * (w y * g y)) :=
    ((hBi.integrable_indicator hB).const_mul _).add (hgi.const_mul _)
  have hdiff : ∀ y, ‖H (y + h) - H y‖ ≤ 2 * |M| := fun y =>
    (norm_sub_le _ _).trans (by linarith [hM (y + h), hM y, le_abs_self M])
  have hle : ∀ y, w y * ‖H (y + h) - H y‖ ≤ 2 * |M| * B.indicator w y + ‖h‖ * (w y * g y) := by
    intro y
    have hwy : 0 ≤ w y := weight_nonneg y
    have hgy : 0 ≤ ‖h‖ * (w y * g y) := mul_nonneg (norm_nonneg _) (mul_nonneg hwy (hg0 y))
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB]
      have := mul_le_mul_of_nonneg_left (hdiff y) hwy
      nlinarith
    · rw [Set.indicator_of_notMem hyB]
      have := mul_le_mul_of_nonneg_left (hoff y hyB) hwy
      nlinarith
  calc ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖
      ≤ ∫ y, (2 * |M| * B.indicator w y + ‖h‖ * (w y * g y)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
          mul_nonneg (weight_nonneg y) (norm_nonneg _)) hu (Filter.Eventually.of_forall hle)
    _ = 2 * |M| * (∫ y in B, w y) + ‖h‖ * ∫ y, w y * g y := by
        rw [integral_add ((hBi.integrable_indicator hB).const_mul _) (hgi.const_mul _),
          integral_const_mul, integral_const_mul, integral_indicator hB]
    _ ≤ 2 * |M| * (C * ‖h‖) + ‖h‖ * C := by
        gcongr
    _ = (2 * |M| * C + C) * ‖h‖ := by ring

theorem fieldOf_second_weighted_modulus {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ K : ℝ, ∀ h : Space, ‖h‖ ≤ 1 →
      ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) *
        ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) (y + h) - fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ K * ‖h‖ := by
  obtain ⟨C₀, hC₀⟩ := second_decay hP hD β
  refine modulus_of_cover (M := |C₀|) (fun y => (hC₀ y).trans ?_)
    (ProfilePowerJumpsCover.fieldOf_second_jump_cover hP hD β)
  calc C₀ * (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ |C₀| * (1 + ‖y‖) ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (weight_nonneg y)
    _ ≤ |C₀| * 1 := mul_le_mul_of_nonneg_left (weight_le_one y) (abs_nonneg _)
    _ = |C₀| := mul_one _

end ProfilePowerJumps

end FracInternal

end Breakdown
