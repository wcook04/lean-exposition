import Breakdown.Frac.StOperator

open MeasureTheory Real Set

noncomputable section

namespace Breakdown

namespace FracInternal

def radialBound (α : ℝ) (y : ℝ) : ℝ :=
  if y < 1 then y ^ (1 - 2 * α) else y ^ (-1 - 2 * α)

theorem radialBound_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    Integrable (fun z : Space => radialBound α ‖z‖) := by
  refine (integrable_fun_norm_addHaar (volume : Measure Space) (f := radialBound α)).mpr ?_
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (3 - 2 * α)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [radialBound, if_pos hy.2]
    rw [show (3 - 2 * α) = ((2 : ℕ) : ℝ) + (1 - 2 * α) by push_cast; ring, rpow_add hy.1,
      rpow_natCast]
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (1 - 2 * α)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy1 : (1 : ℝ) < y := hy
    simp only [radialBound, if_neg (not_lt.mpr hy1.le)]
    rw [show (1 - 2 * α) = ((2 : ℕ) : ℝ) + (-1 - 2 * α) by push_cast; ring,
      rpow_add (by linarith), rpow_natCast]

theorem coord_continuous : Continuous fun z : Space => z 0 := by
  fun_prop

theorem integrand_nonneg (α : ℝ) (z : Space) :
    0 ≤ ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2) :=
  mul_nonneg (rpow_nonneg (norm_nonneg _) _)
    (by linarith [one_sub_sq_div_two_le_cos (x := z 0)])

theorem integrand_le {α : ℝ} (hα1 : 1 < α) (z : Space) :
    ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2) ≤ radialBound α ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · have e2 : (0 : ℝ) ^ (1 - 2 * α) = 0 := zero_rpow (by linarith)
    simp [radialBound, e2]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have ht : |z 0| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z 0
    have hp : 0 < ‖z‖ ^ (-(3 + 2 * α)) := rpow_pos_of_pos hr _
    by_cases h1 : ‖z‖ < 1
    · simp only [radialBound, if_pos h1]
      have hb := (abs_le.mp (cos_bound (x := z 0) (by linarith))).2
      have h4a : |z 0| ^ 4 ≤ ‖z‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) ht 4
      have h4 : Real.cos (z 0) - 1 + (z 0) ^ 2 / 2 ≤ ‖z‖ ^ 4 := by
        nlinarith [pow_nonneg (abs_nonneg (z 0)) 4]
      calc _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 4 := mul_le_mul_of_nonneg_left h4 hp.le
        _ = ‖z‖ ^ (1 - 2 * α) := by
          rw [← rpow_natCast, ← rpow_add hr]
          congr 1
          push_cast
          ring
    · simp only [radialBound, if_neg h1]
      have h2a : |z 0| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ht 2
      rw [sq_abs] at h2a
      have h2 : Real.cos (z 0) - 1 + (z 0) ^ 2 / 2 ≤ ‖z‖ ^ 2 := by
        nlinarith [cos_le_one (z 0)]
      calc _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hp.le
        _ = ‖z‖ ^ (-1 - 2 * α) := by
          rw [← rpow_natCast, ← rpow_add hr]
          congr 1
          push_cast
          ring

theorem integrand_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2)) := by
  have hmeas : AEStronglyMeasurable
      (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2)) volume := by
    apply Measurable.aestronglyMeasurable
    have hc : Continuous fun z : Space => Real.cos (z 0) - 1 + (z 0) ^ 2 / 2 := by
      have := coord_continuous
      fun_prop
    exact (measurable_norm.pow_const _).mul hc.measurable
  refine (radialBound_integrable hα1 hα2).mono' hmeas (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg α z)]
  exact integrand_le hα1 z

end FracInternal

open FracInternal in
theorem normalizer : NormalizerStatement := by
  intro α hα1 hα2
  have hint := integrand_integrable hα1 hα2
  refine ⟨hint, ?_⟩
  unfold fractionalNormalizer
  rw [integral_pos_iff_support_of_nonneg (fun z => integrand_nonneg α z) hint]
  have hopen : IsOpen {z : Space | 0 < z 0} := isOpen_lt continuous_const coord_continuous
  have hne : ({z : Space | 0 < z 0}).Nonempty := ⟨EuclideanSpace.single 0 1, by simp⟩
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
  intro z hz
  have hz0 : z 0 ≠ 0 := ne_of_gt hz
  have hzne : z ≠ 0 := fun h => hz0 (by simp [h])
  have hlt := one_sub_sq_div_two_lt_cos hz0
  exact (mul_pos (rpow_pos_of_pos (norm_pos_iff.mpr hzne) _) (by linarith)).ne'

end Breakdown
