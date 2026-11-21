import Breakdown.Cert.CoerciveSmoothEpsModeBounds

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

open Internal.Absorb

theorem summable_integral_cnormSq_modeGrad (hPars : ModeSquareSumHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hGp : IsTimePeriodic G)
    (hGf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) :
    Summable (fun ι => ∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slabMeasure) := by
  have e : ∀ ι, (∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slabMeasure) =
      (periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y))).toReal := fun ι =>
    (ModeL2Internal.toReal_periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y))
      (aesm_cnormSq_modeGrad hGm ι) (fun _ _ => cnormSq_nonneg' _)).symm
  simp only [e]
  refine ENNReal.summable_toReal ?_
  have hP := hPars.2.1 G hGm hGp hGf
  unfold periodLIntegral at hP ⊢
  rw [← hP]
  exact hGf.ne

theorem summable_epsModeTerm (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds) {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    Summable (epsModeTerm m v (smoothRight P W v)) := by
  obtain ⟨f1, f2, f3⟩ := square_gradSmoothRight hS
  have hv := hSP P v hS.smooth
  have s1 := summable_integral_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient hv.gradient_finite
  have s2 := summable_integral_cnormSq_modeGrad hPars f1 f2 f3
  refine Summable.of_norm_bounded (g := fun ι => epsSup * ((∫ z, cnormSq (modeGrad ι (gradField v) z.1 z.2) ∂slabMeasure)
      + ∫ z, cnormSq (modeGrad ι (gradField (smoothRight P W v)) z.1 z.2) ∂slabMeasure)) ((s1.add s2).mul_left epsSup) ?_
  intro ι
  have hI := integrable_epsIntegrand hPars hSP hS f1 f2 f3 ι
  have i1 := integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient hv.gradient_finite ι
  have i2 := integrable_cnormSq_modeGrad hPars f1 f2 f3 ι
  have eT : epsModeTerm m v (smoothRight P W v) ι = ∫ z, epsIntegrand m v (smoothRight P W v) ι z.1 z.2 ∂slabMeasure :=
    (integral_prod (fun z : ℝ × Space => epsIntegrand m v (smoothRight P W v) ι z.1 z.2) hI).symm
  rw [eT, Real.norm_eq_abs, ← integral_add i1 i2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hI.abs ((i1.add i2).const_mul epsSup) fun z => ?_)
  exact abs_epsIntegrand_le m hS.admissible.epsW_le v _ ι z.1 z.2

end SmoothEpsInternal

end Coercive

end Breakdown
