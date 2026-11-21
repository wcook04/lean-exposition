import Breakdown.Cert.CoerciveSmoothEpsModeBounds

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

open Internal.Absorb

theorem epsGradTerm_le {C : Type} (m : ModeWeights C) {epsGradSup : ℝ}
    (hle : ∀ c y, ‖fderiv ℝ (m.epsW c) y‖ ≤ epsGradSup) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    epsGradTerm m v ι σ y ≤
      epsGradSup * (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) + cnormSq (modeGrad ι (gradField v) σ y)) := by
  have ha : vortGradAmp (secondDerivField v) ι σ y ^ 2 ≤ 2 * cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) := by
    unfold vortGradAmp
    rw [Real.sq_sqrt (cnormSq_nonneg' _)]
    exact cnormSq_curlGradOfSecondDeriv_le _
  have hb : vortAmp (gradField v) ι σ y ^ 2 ≤ 2 * cnormSq (modeGrad ι (gradField v) σ y) := by
    unfold vortAmp
    rw [Real.sq_sqrt (cnormSq_nonneg' _)]
    exact cnormSq_curlOfGrad_le _
  have a0 : 0 ≤ vortGradAmp (secondDerivField v) ι σ y := Real.sqrt_nonneg _
  have b0 : 0 ≤ vortAmp (gradField v) ι σ y := Real.sqrt_nonneg _
  have g0 : 0 ≤ m.epsGrad ι y := norm_nonneg _
  have g1 : m.epsGrad ι y ≤ epsGradSup := hle _ y
  have hab : vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y ≤
      cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) + cnormSq (modeGrad ι (gradField v) σ y) := by
    nlinarith [sq_nonneg (vortGradAmp (secondDerivField v) ι σ y - vortAmp (gradField v) ι σ y)]
  unfold epsGradTerm
  rw [mul_assoc]
  calc m.epsGrad ι y * (vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y)
      ≤ epsGradSup * (vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y) :=
        mul_le_mul_of_nonneg_right g1 (mul_nonneg a0 b0)
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (g0.trans g1)

theorem integrable_epsTerms (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds) {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => epsIntegrand m v (smoothRight P W v) ι z.1 z.2) slabMeasure ∧
      Integrable (fun z : ℝ × Space => epsIntegrand m v (negSumSecondPartialsOfField v) ι z.1 z.2) slabMeasure ∧
      Integrable (fun z : ℝ × Space => epsGradTerm m v ι z.1 z.2) slabMeasure := by
  obtain ⟨f1, f2, f3⟩ := square_gradSmoothRight hS
  obtain ⟨l1, l2, l3⟩ := square_gradSumSecondPartials hS
  refine ⟨integrable_epsIntegrand hPars hSP hS f1 f2 f3 ι, integrable_epsIntegrand hPars hSP hS l1 l2 l3 ι, ?_⟩
  have hv := hSP P v hS.smooth
  have hHf : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ :=
    (perturbationSecondDerivBoundHolds_proof _ _ _ _ _ _ hv).trans_lt hv.sumSecondPartials_finite
  have i1 := integrable_cnormSq_modeSecondDeriv hPars hv.measurable_secondDeriv hv.periodic_secondDeriv hHf ι
  have i2 := integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient hv.gradient_finite ι
  have yeg : AEMeasurable (fun z : ℝ × Space => m.epsGrad ι z.2) volume :=
    ((measurable_fderiv ℝ (m.epsW (m.classOf ι))).norm.comp measurable_snd).aemeasurable
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => epsGradTerm m v ι z.1 z.2) slabMeasure := by
    unfold epsGradTerm
    exact ((yeg.mul (aem_vortGradAmp' hv.measurable_secondDeriv ι)).mul
      (aem_vortAmp' hv.measurable_gradient ι)).aestronglyMeasurable.mono_ac ac_slab
  refine ((i1.add i2).const_mul epsGradSup).mono' hm (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (epsGradTerm_nonneg m v ι z.1 z.2)]
  exact epsGradTerm_le m hS.admissible.epsW_grad_le v ι z.1 z.2

end SmoothEpsInternal

end Coercive

end Breakdown
