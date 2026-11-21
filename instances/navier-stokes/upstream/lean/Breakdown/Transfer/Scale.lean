import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem scaled_kernel_eq {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : MildFramework X) (u : ℝ → X) (μ t s : ℝ) (hμ : 0 < μ) (hs : s < t) :
    μ • F.D μ (F.K (μ * t - μ * s) (u (μ * s)) (u (μ * s))) =
      F.K (t - s) (F.D μ (u (μ * s))) (F.D μ (u (μ * s))) := by
  rw [← mul_sub]
  exact F.D_K μ (t - s) hμ (sub_pos.mpr hs) _ _

theorem scale_of (h1 : VarConstIntegralStatement) : ScaleStatement := by
  intro X _ _ _ F u μ T hμ hT hu
  obtain ⟨hcont, hmild⟩ := hu
  have hmaps : MapsTo (fun s => μ * s) (Icc 0 T) (Icc 0 (μ * T)) := fun s hs =>
    ⟨mul_nonneg hμ.le hs.1, mul_le_mul_of_nonneg_left hs.2 hμ.le⟩
  have hvc : ContinuousOn (fun s => F.D μ (u (μ * s))) (Icc 0 T) :=
    (F.D μ).continuous.comp_continuousOn
      (hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hvc
  have hint := (h1 X F.toHeatBilinear (fun s => F.D μ (u (μ * s)))
    (fun s => F.D μ (u (μ * s))) 0 T M M hT hvc hvc hM hM).1
  refine ⟨hvc, fun t ht => ⟨hint t ht, ?_⟩⟩
  obtain ⟨hi, he⟩ := hmild (μ * t) (hmaps ht)
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (f := fun r => F.D μ (F.K (μ * t - r) (u r) (u r))) (a := 0) (b := t) μ
  rw [mul_zero] at hsub
  simp only [mul_zero, sub_zero]
  rw [he, map_add, sub_zero, ← (F.D μ).intervalIntegral_comp_comm hi, ← hsub,
    ← intervalIntegral.integral_smul]
  congr 1
  · exact DFunLike.congr_fun (F.D_G μ t hμ ht.1) (u 0)
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst hs
    rw [Set.uIoc_of_le ht.1] at hs
    exact scaled_kernel_eq F u μ t s hμ (lt_of_le_of_ne hs.2 hst)

end Breakdown
