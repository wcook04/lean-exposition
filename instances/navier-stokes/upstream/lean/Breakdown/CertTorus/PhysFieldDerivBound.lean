import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal FourierTransform Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal

theorem volume_ac_weightL1Measure (k : ℕ) : (volume : Measure Space) ≪ weightL1Measure k := by
  refine withDensity_absolutelyContinuous' ?_ ?_
  · fun_prop
  · exact Eventually.of_forall fun ξ => by
      have : 0 < (1 + ‖ξ‖) ^ k := by positivity
      simpa using this

theorem lintegral_weightL1Measure (k : ℕ) (f : Space → CSpace) :
    ∫⁻ ξ, ‖f ξ‖ₑ ∂weightL1Measure k = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable volume (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _

theorem lintegral_weighted_norm (k : ℕ) (f : Space → CSpace) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k * ‖f ξ‖) = ∫⁻ ξ, ‖f ξ‖ₑ ∂weightL1Measure k := by
  rw [lintegral_weightL1Measure]
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]

theorem integrable_weighted {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ k * ‖f ξ‖) volume := by
  have hm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weightL1Measure k)
  refine ⟨(Continuous.aestronglyMeasurable (by fun_prop)).mul hm.norm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => by positivity),
    lintegral_weighted_norm, ← eLpNorm_one_eq_lintegral_enorm]
  exact hf.2

theorem integral_weighted_eq_norm {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    ∫ ξ, (1 + ‖ξ‖) ^ k * ‖f ξ‖ = ‖toWeightL1 k f‖ := by
  have ht : toWeightL1 k f = hf.toLp f := by
    unfold toWeightL1
    rw [dif_pos hf]
  rw [ht, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm, ← lintegral_weighted_norm,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ξ => by positivity)
      ((integrable_weighted hf).aestronglyMeasurable)]

theorem physField_eq_realVec_comp (f : Space → CSpace) :
    physField f = realVec ∘ 𝓕 (fun v => f (-v)) := by
  funext y
  simp only [physField, Function.comp_apply]
  rw [fourierInv_eq_fourier_comp_neg]

theorem norm_iteratedFDeriv_fourier_le {j : ℕ} {g : Space → CSpace}
    (hg : AEStronglyMeasurable g volume) (hI : Integrable (fun v => (1 + ‖v‖) ^ j * ‖g v‖) volume)
    (y : Space) :
    ‖iteratedFDeriv ℝ j (𝓕 g) y‖ ≤ (2 * π) ^ j * ∫ v, (1 + ‖v‖) ^ j * ‖g v‖ := by
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (j : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ n * ‖g v‖) volume := by
    intro n hn
    have hnj : n ≤ j := by exact_mod_cast hn
    refine hI.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hg.norm)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    calc ‖v‖ ^ n ≤ (1 + ‖v‖) ^ n := by gcongr; linarith
      _ ≤ (1 + ‖v‖) ^ j := pow_le_pow_right₀ (by linarith [norm_nonneg v]) hnj
  rw [Real.iteratedFDeriv_fourier hint hg le_rfl, Real.fourier_eq]
  calc ‖∫ v, 𝐞 (-inner ℝ v y) • VectorFourier.fourierPowSMulRight (innerSL ℝ) g v j‖
      ≤ ∫ v, ‖𝐞 (-inner ℝ v y) • VectorFourier.fourierPowSMulRight (innerSL ℝ) g v j‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) g v j‖ := by
        simp_rw [Circle.norm_smul]
    _ ≤ ∫ v, (2 * π) ^ j * ((1 + ‖v‖) ^ j * ‖g v‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (hI.const_mul _) (Eventually.of_forall fun v => ?_)
        refine (VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) g v j).trans ?_
        have h1 : ‖innerSL ℝ (E := Space)‖ ≤ 1 := norm_innerSL_le _
        have h2 : ‖v‖ ^ j ≤ (1 + ‖v‖) ^ j := by gcongr; linarith
        calc (2 * π * ‖innerSL ℝ (E := Space)‖) ^ j * ‖v‖ ^ j * ‖g v‖
            ≤ (2 * π * 1) ^ j * (1 + ‖v‖) ^ j * ‖g v‖ := by gcongr
          _ = (2 * π) ^ j * ((1 + ‖v‖) ^ j * ‖g v‖) := by ring
    _ = (2 * π) ^ j * ∫ v, (1 + ‖v‖) ^ j * ‖g v‖ := integral_const_mul _ _

end Internal

open Internal in
theorem physFieldDerivBound_holds : PhysFieldDerivBound := by
  intro j
  refine ⟨‖realVec‖ * (2 * π) ^ j, fun f hf y => ?_⟩
  have hfm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weightL1Measure j)
  have hneg : MeasurePreserving (fun v : Space => -v) volume volume :=
    Measure.measurePreserving_neg volume
  have hgm : AEStronglyMeasurable (fun v => f (-v)) volume := hfm.comp_measurePreserving hneg
  have hfI := integrable_weighted hf
  have hgI : Integrable (fun v : Space => (1 + ‖v‖) ^ j * ‖f (-v)‖) volume := by
    have := hneg.integrable_comp_of_integrable hfI
    simpa [Function.comp_def, norm_neg] using this
  have hgeq : ∫ v : Space, (1 + ‖v‖) ^ j * ‖f (-v)‖ = ∫ v, (1 + ‖v‖) ^ j * ‖f v‖ := by
    have := integral_neg_eq_self (fun v : Space => (1 + ‖v‖) ^ j * ‖f v‖) volume
    simpa [norm_neg] using this
  have hcd : ContDiff ℝ (j : ℕ∞) (𝓕 (fun v => f (-v))) := by
    refine Real.contDiff_fourier fun n hn => ?_
    have hnj : n ≤ j := by exact_mod_cast hn
    refine hgI.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hgm.norm)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    calc ‖v‖ ^ n ≤ (1 + ‖v‖) ^ n := by gcongr; linarith
      _ ≤ (1 + ‖v‖) ^ j := pow_le_pow_right₀ (by linarith [norm_nonneg v]) hnj
  rw [physField_eq_realVec_comp]
  calc ‖iteratedFDeriv ℝ j (realVec ∘ 𝓕 (fun v => f (-v))) y‖
      ≤ ‖realVec‖ * ‖iteratedFDeriv ℝ j (𝓕 (fun v => f (-v))) y‖ :=
        realVec.norm_iteratedFDeriv_comp_left hcd.contDiffAt (by exact_mod_cast le_rfl)
    _ ≤ ‖realVec‖ * ((2 * π) ^ j * ∫ v, (1 + ‖v‖) ^ j * ‖f (-v)‖) := by
        gcongr
        exact norm_iteratedFDeriv_fourier_le hgm hgI y
    _ = ‖realVec‖ * (2 * π) ^ j * ‖toWeightL1 j f‖ := by
        rw [hgeq, integral_weighted_eq_norm hf]
        ring

end Breakdown.FarField
