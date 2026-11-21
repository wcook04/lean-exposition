import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveAbsorb

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

open Internal.Absorb

theorem aemeasurable_weights {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => m.eps ι z.2) volume ∧
      AEMeasurable (fun z : ℝ × Space => m.epsGrad ι z.2) volume ∧
      AEMeasurable (fun z : ℝ × Space => m.dop P ι z.2) volume ∧
      AEMeasurable (fun z : ℝ × Space => m.rate (m.classOf ι) z.2) volume := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
    exact (hK.continuous.abs.measurable.comp measurable_snd).aemeasurable
  · exact ((measurable_fderiv ℝ (m.epsW (m.classOf ι))).norm.comp measurable_snd).aemeasurable
  · have hr := hm.rate_measurable (m.classOf ι)
    unfold ModeWeights.dop shiftedFrequency
    fun_prop
  · exact ((hm.rate_measurable (m.classOf ι)).comp measurable_snd).aemeasurable

theorem contDiff_two_of_smooth {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) :=
  contDiff_infty.mp hv.smooth 2

theorem aemeasurable_modeEpsPos {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeEpsPos m P (gradField v) ι z.1 z.2) slabMeasure := by
  obtain ⟨ye, -, yd, -⟩ := aemeasurable_weights hS.admissible ι
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (cont_gradField (contDiff_two_of_smooth hS.smooth)).continuous.aestronglyMeasurable
  have a3 := aem_vortAmp' hG ι
  have hd := continuous_abs.measurable.comp_aemeasurable yd
  unfold modeEpsPos
  exact ((ye.mul hd).mul (a3.pow_const 2)).mono_ac ac_slab

theorem aemeasurable_modeEpsRest {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2) slabMeasure := by
  obtain ⟨ye, yeg, -, yr⟩ := aemeasurable_weights hS.admissible ι
  have hvc := contDiff_two_of_smooth hS.smooth
  have hW := hS.flow_smooth
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hv0 : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hvc.continuous.aestronglyMeasurable
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (cont_gradField hvc).continuous.aestronglyMeasurable
  have hH : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume :=
    (cont_secondDerivField hvc).aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (cont_gradField hW).continuous.aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField W z.1 z.2) volume :=
    (cont_secondDerivField hW).aestronglyMeasurable
  have a1 := aem_velAmp' hv0
  have a2 := aem_gradAmp' hG
  have a3 := aem_vortAmp' hG
  have a5 := aem_vortGradAmp' hH
  have b1 := aem_velAmp' hWc.aestronglyMeasurable
  have b2 := aem_gradAmp' hgW
  have b3 := aem_vortAmp' hgW
  have b4 := aem_vortGradAmp' hhW
  have hcoord := ModeL2Internal.continuous_coord
  have hmf := measurable_meanField hWc
  have yrel : AEMeasurable (fun z : ℝ × Space => ‖relativeVelocity W (m.rate (m.classOf ι)) z.2‖) volume := by
    have hrc := hS.admissible.rate_measurable (m.classOf ι)
    have h0 := (hcoord 0).measurable
    have h1 := (hcoord 1).measurable
    have hrel : Measurable (relativeVelocity W (m.rate (m.classOf ι))) := by
      unfold relativeVelocity
      fun_prop
    exact (hrel.norm.comp measurable_snd).aemeasurable
  have hcv : Continuous curlVec := by
    unfold curlVec
    fun_prop
  have yc : AEMeasurable (fun z : ℝ × Space => ‖curlVec (fderiv ℝ (meanField W) z.2)‖) volume :=
    ((hcv.measurable.comp (measurable_fderiv ℝ (meanField W))).norm.comp measurable_snd).aemeasurable
  have ycg : AEMeasurable (fun z : ℝ × Space =>
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2‖) volume :=
    ((measurable_fderiv ℝ _).norm.comp measurable_snd).aemeasurable
  have hra := abs_aem yr
  have hS4 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      (velAmp W α z.1 z.2 * vortGradAmp (secondDerivField v) (ι - α) z.1 z.2
        + gradAmp (gradField W) α z.1 z.2 * vortAmp (gradField v) (ι - α) z.1 z.2
        + vortGradAmp (secondDerivField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2
        + vortAmp (gradField W) α z.1 z.2 * gradAmp (gradField v) (ι - α) z.1 z.2)) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ =>
      ((((b1 α).mul (a5 _)).add ((b2 α).mul (a3 _))).add ((b4 α).mul (a1 _))).add ((b3 α).mul (a2 _))
  unfold modeEpsRest
  exact ((((((((ye.mul yrel).add yeg).mul (a5 ι)).mul (a3 ι)).neg.sub
      ((ye.mul ((aemeasurable_const.mul yc).add hra)).mul ((a3 ι).pow_const 2))).sub
      (((ye.mul ycg).mul (a1 ι)).mul (a3 ι))).sub (((ye.mul yc).mul (a2 ι)).mul (a3 ι))).sub
      ((ye.mul (a3 ι)).mul hS4)).mono_ac ac_slab

end SmoothEpsInternal

end Coercive

end Breakdown
