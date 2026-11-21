import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.VelocityScale

theorem test_scale {a b : ℝ} (hb : b ≠ 0) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (fun y => a • φ (b • y)) := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨?_, ?_, fun y => ?_⟩
  · exact (hs.comp (contDiff_const_smul _)).const_smul _
  · exact (hc.comp_smul hb).comp_left (g := fun v : Space => a • v) (smul_zero _)
  · have hA : HasFDerivAt (fun y : Space => b • y)
        (b • ContinuousLinearMap.id ℝ Space) y := (hasFDerivAt_id (𝕜 := ℝ) y).const_smul b
    have hfd : HasFDerivAt (fun y => a • φ (b • y))
        (a • (fderiv ℝ φ (b • y)).comp (b • ContinuousLinearMap.id ℝ Space)) y :=
      (((hs.differentiable (by simp) _).hasFDerivAt.comp y hA).const_smul a)
    unfold divergenceAt
    rw [hfd.fderiv]
    have h0 := hd (b • y)
    unfold divergenceAt at h0
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, h0]
    ring

end FracInternal.VelocityScale

open Internal.VelocityRotate FracInternal.VelocityScale in
theorem fracVelocityDilate (α : ℝ) (_hα : 0 < α) (_h1 : FracDilationAlgebra α)
    (h2 : FracEmbedDilate α) (_h3 : DecayFieldScale α) : FracVelocityDilate α := by
  intro μ hμ x
  have hb : μ ^ (1 / (2 * α)) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  have hD : MeasurePreserving (fun y : Space => μ ^ (1 / (2 * α)) • y) volume
      (ENNReal.ofReal |((μ ^ (1 / (2 * α))) ^ Module.finrank ℝ Space)⁻¹| • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume hb⟩
  have key := eq_of_test testDense_holds.2 testSpan_holds (fracDilX α μ).continuous
    (compOp hD ENNReal.ofReal_ne_top (μ ^ (1 - 1 / (2 * α)) • ContinuousLinearMap.id ℝ Space))
    (fun φ hφ => by
      have ht : IsTestField (scaleField α μ φ) := test_scale hb hφ
      rw [h2 μ φ hμ (decay_of_test hφ), velocity_spec velocity_holds _ ht,
        velocity_spec velocity_holds _ hφ, compOp_toLp hD _ _ (memLp_test hφ)]
      rfl) x
  rw [key]
  exact compOp_ae hD _ _ (velocity x)

end Breakdown.Freq
