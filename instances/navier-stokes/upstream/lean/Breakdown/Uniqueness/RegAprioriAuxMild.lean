import Breakdown.Uniqueness.RegAprioriAuxMildPart2
import Breakdown.Uniqueness.RegAprioriAuxMildPart3
import Breakdown.Uniqueness.RegAprioriAuxMildPart4

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem lintegral_weighted_const_mul_sq (w k : Space → ℝ≥0∞) (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    (∫⁻ ξ, w ξ * (A * k ξ) ^ 2) ^ (1 / 2 : ℝ) = A * (∫⁻ ξ, w ξ * k ξ ^ 2) ^ (1 / 2 : ℝ) := by
  have e : ∀ ξ, w ξ * (A * k ξ) ^ 2 = A ^ 2 * (w ξ * k ξ ^ 2) := fun ξ => by ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hA),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem hsNormSq_sqrt_mild_le (m : ℕ) (hm : 3 ≤ m) : ∃ C : ℝ,
    ∀ (T : ℝ) (F : ℝ → Space → CSpace), IsHsCurve m F 0 T → IsVarConstSymbol F 0 T →
      (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → ∀ t ∈ Icc 0 T,
      hsNormSq m (F t) ^ (1 / 2 : ℝ) ≤ hsNormSq m (F 0) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal C * ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) *
          freqL1Norm (F s) * hsNormSq m (F s) ^ (1 / 2 : ℝ) := by
  obtain ⟨c, hc0, hc⟩ := enorm_mild_le m hm
  obtain ⟨CY, hCY0, hY⟩ := convEnormSum_weighted_le m
  refine ⟨c * CY, fun T F hF hD hS t ht => ?_⟩
  have hpt := hc T F t hF hD hS ht
  have hw : Measurable fun ξ : Space => ENNReal.ofReal (hsWeight m ξ) := by
    unfold hsWeight
    fun_prop
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have ha : AEMeasurable (fun ξ => ‖F 0 ξ‖ₑ) volume := (hF.1 0 h0).1.enorm
  have hk := aemeasurable_convEnormSum_curve hm hF ht
  have hg : AEMeasurable (Function.uncurry fun s ξ =>
      ENNReal.ofReal (c * (t - s) ^ (-(1 / 2 : ℝ))) * convEnormSum (F s) ξ)
      ((volume.restrict (Ioo 0 t)).prod volume) := by
    refine AEMeasurable.mul ?_ hk
    refine Measurable.aemeasurable ?_
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.sub measurable_fst).pow_const _)
  have h1 : hsNormSq m (F t) ≤ ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) *
      (‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
        ENNReal.ofReal (c * (t - s) ^ (-(1 / 2 : ℝ))) * convEnormSum (F s) ξ) ^ 2 := by
    refine lintegral_mono fun ξ => ?_
    gcongr
    exact hpt ξ
  refine (ENNReal.rpow_le_rpow h1 (by norm_num)).trans ?_
  refine (lintegral_weighted_add_lintegral_sq_le hw ha hg).trans ?_
  refine add_le_add le_rfl ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  rw [lintegral_weighted_const_mul_sq _ _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (c * (t - s) ^ (-(1 / 2 : ℝ))) *
        (ENNReal.ofReal CY * freqL1Norm (F s) * hsNormSq m (F s) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact hY (F s) (hF.1 s hsT).1
    _ = _ := by
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0]
        ring

end Breakdown.SmoothFlow
