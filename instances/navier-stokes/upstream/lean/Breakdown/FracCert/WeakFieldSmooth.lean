import Breakdown.FracCert.StWeakRegular
import Breakdown.Uniqueness.RegPhysAuxDeriv

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem moment_integrable {f : Space → CSpace} (hf : HasAllSymbolL1Moments f) (n : ℕ) :
    Integrable (fun v : Space => ‖v‖ ^ n * ‖f v‖) := by
  have h0 : AEStronglyMeasurable (fun v : Space => ‖f v‖) volume := by
    simpa using (hf 0).aestronglyMeasurable
  refine (hf n).mono' ((continuous_norm.pow n).aestronglyMeasurable.mul h0) ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  linarith [norm_nonneg v]

private theorem inverse_transform_eq_integral (f : Space → CSpace) :
    𝓕⁻ f = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ f :=
  funext (Breakdown.SmoothFlow.Internal.freqTrInv_eq_integral f)

theorem fieldSmoothOfMoments : FieldSmoothOfMomentsStatement := by
  intro f hf _
  have hm : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ n * ‖f v‖) :=
    fun n _ => moment_integrable hf n
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ f) := by
    rw [inverse_transform_eq_integral]
    exact VectorFourier.contDiff_fourierIntegral _ hm
  have hP : physField f = fun x => realVec (𝓕⁻ f x) := rfl
  refine ⟨?_, fun j => ?_⟩
  · rw [hP]
    exact realVec.contDiff.comp hF
  · by_cases hi : Integrable f
    · refine ⟨‖realVec‖ * ∫ v, ‖VectorFourier.fourierPowSMulRight
          (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v j‖, fun y => ?_⟩
      rw [hP]
      refine (realVec.norm_iteratedFDeriv_comp_left (hF.contDiffAt) ?_).trans ?_
      · exact_mod_cast le_top
      · gcongr
        rw [inverse_transform_eq_integral, VectorFourier.iteratedFDeriv_fourierIntegral _ hm hi.1
          (by exact_mod_cast le_top)]
        exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    · have h0 : 𝓕⁻ f = 0 := by
        rw [inverse_transform_eq_integral]
        ext w : 1
        simp only [VectorFourier.fourierIntegral, Pi.zero_apply]
        exact integral_undef (fun h => hi ((Real.fourierIntegral_convergent_iff' (-innerSL ℝ) w).1 h))
      refine ⟨0, fun y => ?_⟩
      have h1 : physField f = 0 := by
        rw [hP, h0]
        ext x
        simp
      rw [h1]
      simp

end Breakdown.FracCert
