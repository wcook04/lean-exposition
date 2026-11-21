import Breakdown.Uniqueness.RegEmbed

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem coe_heatX_ae (hH : HeatSemigroup) (hR : FieldOpRealized) (t : ℝ) (x : X) :
    ((heatX t x : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((heatFactor t ξ : ℝ) : ℂ) • ((x : X) : Space → CSpace) ξ := by
  have hc : Continuous fun ξ : Space => heatFactor t ξ := by
    unfold heatFactor
    fun_prop
  have hreal := hR (ContinuousLinearEquiv.refl ℝ Space)
    (fun ξ => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) 1
    (hc.smul continuous_const).aestronglyMeasurable (fun ξ => by
      refine (norm_smul_le _ _).trans ?_
      have h1 : ‖heatFactor t ξ‖ ≤ 1 := by
        rw [Real.norm_eq_abs, heatFactor, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_one_iff.2 ?_
        have : 0 ≤ 4 * π ^ 2 * max t 0 * ‖ξ‖ ^ 2 := by positivity
        linarith
      calc ‖heatFactor t ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
            mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  have e := hH.2.2.2.2.2 t x
  have h2 := hreal (x : L2C)
  rw [e]
  filter_upwards [h2] with ξ hξ
  rw [Complex.coe_smul]
  exact hξ

end Breakdown.SmoothFlow
