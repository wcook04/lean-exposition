import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveAbsorb
import Breakdown.Cert.CoerciveSmoothEpsRightGradient

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

open Internal.Absorb

theorem smoothRight_periodic {P : ℝ} {W v : ℝ → Space → Space} (hv : IsTimePeriodic v) (hW : IsTimePeriodic W) :
    IsTimePeriodic (smoothRight P W v) := by
  intro σ y
  have ev : v (σ + 1) = v σ := funext (hv σ)
  have eW : W (σ + 1) = W σ := funext (hW σ)
  have ed : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
    have e : (fun s => v (s + 1) y) = (fun s => v s y) := funext fun s => hv s y
    rw [← deriv_comp_add_const, e]
  unfold smoothRight secondDerivField
  rw [ed, ev, eW]

theorem negSumSecondPartialsOfField_periodic {v : ℝ → Space → Space} (hv : IsTimePeriodic v) :
    IsTimePeriodic (negSumSecondPartialsOfField v) := by
  intro σ y
  have ev : v (σ + 1) = v σ := funext (hv σ)
  unfold negSumSecondPartialsOfField secondDerivField
  rw [ev]

theorem gradField_periodic {F : ℝ → Space → Space} (hF : IsTimePeriodic F) : IsTimePeriodic (gradField F) := by
  intro σ y
  have e : F (σ + 1) = F σ := funext (hF σ)
  unfold gradField
  rw [e]

theorem deriv_eq_fderiv {v : ℝ → Space → Space} (hV : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2))
    (σ : ℝ) (y : Space) :
    deriv (fun s => v s y) σ = fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  have h2 := ((hV (σ, y)).hasFDerivAt).comp_hasDerivAt σ h1
  exact h2.deriv

theorem contDiff_secondDerivField_one {v : ℝ → Space → Space} (hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) := by
  have hg : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × Space) (x : Space) => v p.1 x) (g := fun p => p.2)
      (hV.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact ContDiff.fderiv (f := fun (p : ℝ × Space) (x : Space) => fderiv ℝ (v p.1) x) (g := fun p => p.2)
    (hg.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)

theorem contDiff_smoothRight {P : ℝ} {W v : ℝ → Space → Space}
    (hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2)) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
  have hV1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hV.of_le (by norm_num)
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) := hW.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun q : ℝ × Space => v q.1 q.2) z ((1 : ℝ), (0 : Space))) :=
    (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgv : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) := cont_gradField (hV.of_le (by norm_num))
  have hgW : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := cont_gradField hW
  have hH := contDiff_secondDerivField_one hV
  have hT : ContDiff ℝ 1 (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) := by
    unfold secondDerivTrace secondDerivField
    exact ContDiff.sum fun j _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const
  have e : (fun z : ℝ × Space => smoothRight P W v z.1 z.2) = fun z =>
      (1 / P) • fderiv ℝ (fun q : ℝ × Space => v q.1 q.2) z ((1 : ℝ), (0 : Space)) + (1 / 2 : ℝ) • v z.1 z.2
        + (1 / 2 : ℝ) • fderiv ℝ (v z.1) z.2 z.2 - secondDerivTrace (secondDerivField v z.1 z.2)
        + fderiv ℝ (v z.1) z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2) := by
    funext z
    unfold smoothRight
    rw [deriv_eq_fderiv (hV.differentiable (by norm_num)) z.1 z.2]
  rw [e]
  exact (((((hd.const_smul _).add (hV1.const_smul _)).add ((hgv.clm_apply contDiff_snd).const_smul _)).sub hT).add
    (hgv.clm_apply hW1)).add (hgW.clm_apply hV1)

theorem continuous_gradField_of {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradField F z.1 z.2) :=
  (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => F p.1 x) (g := fun p => p.2)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous

theorem periodLIntegral_gradSmoothRight_lt_top {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ :=
  Internal.SmoothRightGradient.gradField_smoothRight_sq_finite hS.smooth hS.flow_smooth hS.flow_decay

def negTraceMap : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
  -∑ j : Fin 3, (ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))

theorem negTraceMap_apply (H : Space →L[ℝ] Space →L[ℝ] Space) : negTraceMap H = -secondDerivTrace H := by
  simp [negTraceMap, secondDerivTrace]

theorem columnSq_le_three (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := fun i => by
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      calc ‖G (unitVector i)‖ ≤ ‖G‖ * ‖unitVector i‖ := G.le_opNorm _
        _ = ‖G‖ := by rw [show ‖unitVector i‖ = 1 by simp [unitVector], mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem columnSq_gradSumSecondPartials_le {f : Space → Space} (hf : ContDiff ℝ 3 f) (y : Space) :
    matSq (fderiv ℝ (fun x => -secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ f x) x)) y)
      ≤ 3 * ‖negTraceMap‖ ^ 2 * ‖iteratedFDeriv ℝ 3 f y‖ ^ 2 := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := h2.fderiv_right (m := 1) (by norm_num)
  have hT : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) y := h1.differentiable (by norm_num) y
  have e : (fun x => -secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ f x) x)) = fun x => negTraceMap (fderiv ℝ (fderiv ℝ f) x) :=
    funext fun x => (negTraceMap_apply _).symm
  have hd : fderiv ℝ (fun x => negTraceMap (fderiv ℝ (fderiv ℝ f) x)) y = negTraceMap.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y) :=
    (negTraceMap.hasFDerivAt.comp y hT.hasFDerivAt).fderiv
  have hn : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ = ‖iteratedFDeriv ℝ 3 f y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv (f := fderiv ℝ f), norm_iteratedFDeriv_fderiv]
  rw [e, hd]
  refine (columnSq_le_three _).trans ?_
  have hc : ‖negTraceMap.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y)‖ ≤ ‖negTraceMap‖ * ‖iteratedFDeriv ℝ 3 f y‖ := by
    rw [← hn]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  nlinarith [hc2]

theorem periodLIntegral_gradSumSecondPartials_lt_top {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    periodLIntegral (fun σ y => matSq (gradField (negSumSecondPartialsOfField v) σ y)) < ⊤ := by
  have h3 := hS.smooth.derivatives_finite 3 (by norm_num)
  have hV3 : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 3
  have hs : ∀ σ, ContDiff ℝ 3 (v σ) := fun σ => hV3.comp (contDiff_const.prodMk contDiff_id)
  set c : ℝ := 3 * ‖negTraceMap‖ ^ 2
  have hc : 0 ≤ c := by positivity
  have hle : periodLIntegral (fun σ y => matSq (gradField (negSumSecondPartialsOfField v) σ y)) ≤
      ENNReal.ofReal c * periodLIntegral (fun σ y => ‖iteratedFDeriv ℝ 3 (v σ) y‖ ^ 2) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hc]
    refine ENNReal.ofReal_le_ofReal ?_
    have := columnSq_gradSumSecondPartials_le (hs σ) y
    unfold gradField negSumSecondPartialsOfField secondDerivField
    linarith
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h3)

theorem square_gradSmoothRight {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (smoothRight P W v) z.1 z.2) volume ∧
      IsTimePeriodic (gradField (smoothRight P W v)) ∧
      periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ :=
  ⟨(continuous_gradField_of (contDiff_smoothRight (contDiff_infty.mp hS.smooth.smooth 3)
      hS.flow_smooth)).aestronglyMeasurable,
    gradField_periodic (smoothRight_periodic hS.smooth.periodic hS.flow_periodic),
    periodLIntegral_gradSmoothRight_lt_top hS⟩

theorem square_gradSumSecondPartials {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (negSumSecondPartialsOfField v) z.1 z.2) volume ∧
      IsTimePeriodic (gradField (negSumSecondPartialsOfField v)) ∧
      periodLIntegral (fun σ y => matSq (gradField (negSumSecondPartialsOfField v) σ y)) < ⊤ := by
  have hH := contDiff_secondDerivField_one (contDiff_infty.mp hS.smooth.smooth 3)
  have hL : ContDiff ℝ 1 (fun z : ℝ × Space => negSumSecondPartialsOfField v z.1 z.2) := by
    unfold negSumSecondPartialsOfField secondDerivTrace secondDerivField
    exact (ContDiff.sum fun j _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const).neg
  exact ⟨(continuous_gradField_of hL).aestronglyMeasurable,
    gradField_periodic (negSumSecondPartialsOfField_periodic hS.smooth.periodic), periodLIntegral_gradSumSecondPartials_lt_top hS⟩

end SmoothEpsInternal

end Coercive

end Breakdown
