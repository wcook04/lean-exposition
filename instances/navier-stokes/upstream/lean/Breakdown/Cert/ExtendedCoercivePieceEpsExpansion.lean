import Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.OnceExpansion

open Filter Coercive Coercive.Internal.MuSmooth Coercive.Internal.ModeRotation Coercive.ModeDerivative.Internal
  Coercive.CurlWeight.Internal.TestModes Coercive.Internal.SmoothPieceEpsCore

theorem slice_contDiff_of_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) : ContDiff ℝ 1 (W s) :=
  hW.comp (contDiff_const.prodMk contDiff_id)

theorem continuous_slice_fderiv_of_once {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
  (Coercive.Internal.SmoothRightGradient.contDiff_fderiv_param (F := W) (m := 0) hW (by norm_num)).continuous

theorem hasFDerivAt_integrand_of_once {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ)
    (σ : ℝ) (l : Fin 3) (x : Space) (p : ℝ × ℝ) :
    HasFDerivAt (fun x => modeTestIntegrand W ι σ l x p) (modeTestIntegrandDeriv W ι σ l x p) x := by
  have hRot := axialRotationHolds_proof
  have e1 : (fun x => axialRot p.2 x) = ⇑((rotIso hRot p.2 : Space ≃ₗᵢ[ℝ] Space).toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext x
    exact (rotIso_apply hRot p.2 x).symm
  have h1 : HasFDerivAt (fun x => axialRot p.2 x)
      ((rotIso hRot p.2).toContinuousLinearEquiv : Space →L[ℝ] Space) x := by
    rw [e1]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 : HasFDerivAt (W (σ + p.1)) (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) (axialRot p.2 x) :=
    ((slice_contDiff_of_once hW (σ + p.1)).differentiable (by norm_num) _).hasFDerivAt
  have e3 : (fun w : Space => axialRot (-p.2) w) = ⇑((rotIso hRot p.2).symm.toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext w
    exact (rotIso_symm_apply hRot p.2 w).symm
  have h3 : ∀ w, HasFDerivAt (fun w : Space => axialRot (-p.2) w)
      ((rotIso hRot p.2).symm.toContinuousLinearEquiv : Space →L[ℝ] Space) w := by
    intro w
    rw [e3]
    exact ContinuousLinearMap.hasFDerivAt _
  have h4 := (h3 _).comp x (h2.comp x h1)
  have h5 := ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).hasFDerivAt).comp x h4
  have h6 := (Complex.ofRealCLM.hasFDerivAt).comp x h5
  have h7 := h6.const_mul (expFactor ι p.1 p.2)
  refine HasFDerivAt.congr_of_eventuallyEq (h7.congr_fderiv ?_) (Filter.Eventually.of_forall fun y => ?_)
  · refine ContinuousLinearMap.ext fun u => ?_
    simp [modeTestIntegrandDeriv, rotConj_apply, rotIso_apply, rotIso_symm_apply]
  · simp [modeTestIntegrand]

theorem continuous_integrandDeriv_of_once {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrandDeriv W ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) :=
    (continuous_slice_fderiv_of_once hW).comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ =>
      rotConj axialRotationHolds_proof p.2 (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x))) :=
    Continuous.comp (g := fun q : ℝ × (Space →L[ℝ] Space) => rotConj axialRotationHolds_proof q.1 q.2)
      (f := fun p : ℝ × ℝ => (p.2, fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)))
      (continuous_rotConj axialRotationHolds_proof) (continuous_snd.prodMk hA)
  refine continuous_clm_apply.2 fun u => ?_
  have e : (fun p => modeTestIntegrandDeriv W ι σ l x p u) = fun p => expFactor ι p.1 p.2 *
      ((rotConj axialRotationHolds_proof p.2 (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) u l : ℝ) : ℂ) := by
    funext p
    simp [modeTestIntegrandDeriv]
  rw [e]
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp (hB.clm_apply continuous_const)))

theorem continuous_integrand_of_once {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrand W ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 x)) :=
    hW.continuous.comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (W (σ + p.1) (axialRot p.2 x))) :=
    continuous_axialRot_comp continuous_snd.neg hA
  unfold modeTestIntegrand
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp hB))

theorem modeVel_eq_box_of_once {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ)
    (l : Fin 3) (x : Space) :
    modeVel ι W σ x l = (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
  unfold modeVel
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (W (σ + τ) (axialRot φ x)) l : ℝ) : ℂ))
    (integrable_box_of_continuous (continuous_integrand_of_once hW ι σ l x))

theorem modeVel_hasFDerivAt_of_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (y : Space) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeVel ι W σ x l) L y ∧
      ∀ j, L (unitVector j) = modeGrad ι (gradField W) σ y (l, j) := by
  have hbound : ∀ᵐ p ∂boxMeasure, ∀ x ∈ (Set.univ : Set Space),
      ‖modeTestIntegrandDeriv W ι σ l x p‖ ≤ B :=
    Filter.Eventually.of_forall fun p x _ => (norm_modeTestIntegrandDeriv_le ι σ l x p).trans (hB _ _)
  refine ⟨(1 / (2 * Real.pi) : ℂ) • ∫ p, modeTestIntegrandDeriv W ι σ l y p ∂boxMeasure, ?_, ?_⟩
  · have hfun : (fun x => modeVel ι W σ x l) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
      funext x
      exact modeVel_eq_box_of_once hW ι σ l x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => modeTestIntegrand W ι σ l x p) (F' := fun x p => modeTestIntegrandDeriv W ι σ l x p)
      (bound := fun _ => B) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (continuous_integrand_of_once hW ι σ l x).aestronglyMeasurable)
      (integrable_box_of_continuous (continuous_integrand_of_once hW ι σ l y))
      (continuous_integrandDeriv_of_once hW ι σ l y).aestronglyMeasurable hbound
      (integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => hasFDerivAt_integrand_of_once hW ι σ l x p)
    exact hI.const_mul _
  · intro j
    have hint := integrable_box_of_continuous (continuous_integrandDeriv_of_once hW ι σ l y)
    rw [smul_apply, ContinuousLinearMap.integral_apply hint, smul_eq_mul]
    unfold modeGrad
    rw [modeAverage_eq]
    congr 1
    rw [iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (gradField W (σ + τ) (axialRot φ y)
      (axialRot φ (unitVector (l, j).2))) (l, j).1 : ℝ) : ℂ))]
    · congr 1
      funext p
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]
    · refine (hint.apply_continuousLinearMap (unitVector j)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]


theorem slice_differentiable_of_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) : Differentiable ℝ (W s) :=
  ((hW.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) : Differentiable ℝ (fun y => W s y))

theorem grad_expansion_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (i j : Fin 3) :
    axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i
      = (modeGrad (0, 0) (gradField W) σ y (i, j)).re
        + ∑ α ∈ s, (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeGrad α (gradField W) σ y (i, j)).re := by
  have hRot := axialRotationHolds_proof
  set Rp : Space →L[ℝ] Space := ((rotIso hRot φ).toContinuousLinearEquiv : Space →L[ℝ] Space)
  set Rm : Space →L[ℝ] Space := ((rotIso hRot φ).symm.toContinuousLinearEquiv : Space →L[ℝ] Space)
  have hRp : ∀ x, Rp x = axialRot φ x := fun x => rotIso_apply hRot φ x
  have hRm : ∀ x, Rm x = axialRot (-φ) x := fun x => rotIso_symm_apply hRot φ x
  set c : ℤ × ℤ → ℂ := fun α => Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
  have hf : HasFDerivAt (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (Rm.comp ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp))) y := by
    have h1 : HasFDerivAt (fun x => W (σ + τ) (Rp x)) ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp) y :=
      ((slice_differentiable_of_once hW (σ + τ)) (Rp y)).hasFDerivAt.comp y Rp.hasFDerivAt
    have h2 := (Rm.hasFDerivAt (x := W (σ + τ) (Rp y))).comp y h1
    have h3 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h2
    have hfun : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
        = (⇑(EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ ⇑Rm ∘ fun x => W (σ + τ) (Rp x)) := by
      funext x
      simp only [Function.comp, hRp, hRm]
      rfl
    rw [hfun]
    exact h3
  choose L hL hLe using fun α => modeVel_hasFDerivAt_of_once hW hB α σ i y
  have hg : HasFDerivAt (fun x => (modeVel (0, 0) W σ x i).re
        + ∑ α ∈ s, (c α * modeVel α W σ x i).re)
      (Complex.reCLM.comp (L (0, 0)) + ∑ α ∈ s, Complex.reCLM.comp (c α • L α)) y := by
    refine (Complex.reCLM.hasFDerivAt.comp y (hL (0, 0))).add ?_
    refine HasFDerivAt.fun_sum fun α _ => ?_
    exact Complex.reCLM.hasFDerivAt.comp y ((hL α).const_mul (c α))
  have heq : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      = fun x => (modeVel (0, 0) W σ x i).re + ∑ α ∈ s, (c α * modeVel α W σ x i).re :=
    funext fun x => rot_field_expansion hW.continuous hWp s hh σ τ φ x i
  rw [heq] at hf
  have hu := congrArg (fun T : Space →L[ℝ] ℝ => T (unitVector j)) (hf.unique hg)
  simp only [ContinuousLinearMap.comp_apply, add_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_apply, Complex.reCLM_apply, smul_eq_mul, hLe] at hu
  rw [← hu]
  simp only [hRp, hRm]
  rfl

theorem meanField_fderiv_apply_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (σ : ℝ) (y : Space) (i j : Fin 3) :
    fderiv ℝ (meanField W) y (unitVector j) i = (modeGrad (0, 0) (gradField W) σ y (i, j)).re := by
  have hm : meanField W = fun x => ∑ k : Fin 3, (modeVel (0, 0) W σ x k).re • unitVector k := by
    funext x
    unfold meanField
    simp_rw [modeVel_mean_shift hWp σ x]
  choose L hL hLe using fun k => modeVel_hasFDerivAt_of_once hW hB (0, 0) σ k y
  have hd : HasFDerivAt (meanField W)
      (∑ k : Fin 3, (Complex.reCLM.comp (L k)).smulRight (unitVector k)) y := by
    rw [hm]
    exact HasFDerivAt.fun_sum fun k _ => (Complex.reCLM.hasFDerivAt.comp y (hL k)).smul_const (unitVector k)
  rw [hd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hLe]
  exact space_sum_apply (fun k => (modeGrad (0, 0) (gradField W) σ y (k, j)).re) i

theorem gradW_expansion_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (i j : Fin 3) :
    ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = ((fderiv ℝ (meanField W) y (unitVector j) i : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeGrad α (gradField W) σ y (i, j) := by
  rw [grad_expansion_once hW hB hWp s hh σ τ φ y i j, Complex.ofReal_add]
  congr 1
  · rw [meanField_fderiv_apply_once hW hB hWp σ y i j]
  · exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeGrad_neg, map_mul]

theorem vortW_expansion_once {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (j : Fin 3) :
    ((axialRot (-φ) (vortField W (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = ((curlVec (fderiv ℝ (meanField W) y) j : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * curlOfGrad (modeGrad α (gradField W) σ y) j := by
  unfold vortField
  rw [← Internal.CurlEnergy.curlVec_axialRot φ _ j, StretchInternal.curlVec_apply]
  push_cast
  simp_rw [gradW_expansion_once hW hB hWp s hs hh σ τ φ y]
  unfold curlOfGrad
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  simp only [Fin.sum_univ_three, Finset.sum_add_distrib]
  simp only [mul_left_comm]
  push_cast
  rfl


end Internal.OnceExpansion

end CoerciveWeak

end Breakdown
