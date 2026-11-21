import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hsWeight_measurable (m : ℕ) : Measurable (hsWeight m) := by
  unfold hsWeight
  fun_prop

private theorem hsWeight_pos (m : ℕ) (ξ : Space) : 0 < hsWeight m ξ := by
  unfold hsWeight
  positivity

private theorem hsIntegrand_aemeasurable (m : ℕ) {f : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (fun ξ => ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) volume :=
  (ENNReal.measurable_ofReal.comp (hsWeight_measurable m)).aemeasurable.mul (hf.enorm.pow_const 2)

private theorem enorm_add_sq_le (x y : CSpace) : ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _)]
  have key : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have := norm_add_le x y
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]
  calc ENNReal.ofReal (‖x + y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = 2 * ENNReal.ofReal (‖x‖ ^ 2) + 2 * ENNReal.ofReal (‖y‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

theorem hsNormSq_add_le (m : ℕ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  unfold hsNormSq
  calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, (2 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * ‖f ξ‖ₑ ^ 2 + 2 * ‖g ξ‖ₑ ^ 2) := by
              gcongr
              exact enorm_add_sq_le (f ξ) (g ξ)
          _ = _ := by ring
    _ = 2 * (∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) +
          2 * (∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2) := by
        rw [lintegral_add_left' ((hsIntegrand_aemeasurable m hf).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

theorem ae_eq_zero_of_hsNormSq_eq_zero (m : ℕ) {f : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (h : hsNormSq m f = 0) : f =ᵐ[volume] 0 := by
  unfold hsNormSq at h
  rw [lintegral_eq_zero_iff' (hsIntegrand_aemeasurable m hf)] at h
  filter_upwards [h] with ξ hξ
  have hw : ENNReal.ofReal (hsWeight m ξ) ≠ 0 := by
    simpa using hsWeight_pos m ξ
  simp only [Pi.zero_apply, mul_eq_zero, hw, false_or, pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hξ
  simpa using hξ

end Breakdown.SmoothFlow
