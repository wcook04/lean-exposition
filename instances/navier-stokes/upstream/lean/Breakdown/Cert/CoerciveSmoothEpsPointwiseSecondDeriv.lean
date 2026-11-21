import Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsPointwise

open Internal.SmoothPieceEpsCore Internal.MuSmooth Internal.PieceAbsorb Internal.ModeRotation

def gradModeIntegrand (W : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) (p : ℝ × ℝ) : ℂ :=
  expFactor κ p.1 p.2 * ((axialRot (-p.2) (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x) (axialRot p.2 (unitVector a))) b
    : ℝ) : ℂ)

def gradModeIntegrandDeriv (W : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) (p : ℝ × ℝ) :
    Space →L[ℝ] ℂ :=
  expFactor κ p.1 p.2 • (Complex.ofRealCLM.comp ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp
    ((StretchInternal.rotCLM (-p.2)).comp ((ContinuousLinearMap.apply ℝ Space (axialRot p.2 (unitVector a))).comp
      ((fderiv ℝ (fderiv ℝ (W (σ + p.1))) (axialRot p.2 x)).comp (StretchInternal.rotCLM p.2))))))

theorem gradModeIntegrandDeriv_apply (W : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space)
    (p : ℝ × ℝ) (u : Space) :
    gradModeIntegrandDeriv W κ σ b a x p u = expFactor κ p.1 p.2
      * ((axialRot (-p.2) (fderiv ℝ (fderiv ℝ (W (σ + p.1))) (axialRot p.2 x) (axialRot p.2 u)
        (axialRot p.2 (unitVector a))) b : ℝ) : ℂ) := rfl

theorem slice_fderiv_differentiable {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) : Differentiable ℝ (fderiv ℝ (W s)) :=
  ((slice_contDiff hW s).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

theorem hasFDerivAt_gradModeIntegrand {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space)
    (p : ℝ × ℝ) :
    HasFDerivAt (fun x => gradModeIntegrand W κ σ b a x p) (gradModeIntegrandDeriv W κ σ b a x p) x := by
  have h1 : HasFDerivAt (fun x => axialRot p.2 x) (StretchInternal.rotCLM p.2) x :=
    (StretchInternal.rotCLM p.2).hasFDerivAt
  have h2 := ((slice_fderiv_differentiable hW (σ + p.1)) (axialRot p.2 x)).hasFDerivAt
  have h3 := h2.comp x h1
  have h4 := (ContinuousLinearMap.apply ℝ Space (axialRot p.2 (unitVector a))).hasFDerivAt.comp x h3
  have h5 := (StretchInternal.rotCLM (-p.2)).hasFDerivAt.comp x h4
  have h6 := (EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp x h5
  have h7 := Complex.ofRealCLM.hasFDerivAt.comp x h6
  exact h7.const_mul (expFactor κ p.1 p.2)

theorem norm_gradModeIntegrandDeriv_le (W : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space)
    (p : ℝ × ℝ) :
    ‖gradModeIntegrandDeriv W κ σ b a x p‖ ≤ ‖fderiv ℝ (fderiv ℝ (W (σ + p.1))) (axialRot p.2 x)‖ := by
  have hRot := axialRotationHolds_proof
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  rw [gradModeIntegrandDeriv_apply, norm_mul, norm_expFactor, one_mul, Complex.norm_real]
  set H := fderiv ℝ (fderiv ℝ (W (σ + p.1))) (axialRot p.2 x)
  calc ‖axialRot (-p.2) (H (axialRot p.2 u) (axialRot p.2 (unitVector a))) b‖
      ≤ ‖axialRot (-p.2) (H (axialRot p.2 u) (axialRot p.2 (unitVector a)))‖ := by
        simpa using PiLp.norm_apply_le (axialRot (-p.2) (H (axialRot p.2 u) (axialRot p.2 (unitVector a)))) b
    _ = ‖H (axialRot p.2 u) (axialRot p.2 (unitVector a))‖ := norm_axialRot hRot _ _
    _ ≤ ‖H (axialRot p.2 u)‖ * ‖axialRot p.2 (unitVector a)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖H‖ * ‖axialRot p.2 u‖) * ‖axialRot p.2 (unitVector a)‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖H‖ * ‖u‖ := by
        rw [norm_axialRot hRot, norm_axialRot hRot, ModeDerivative.Internal.norm_unitVector_one, mul_one]

theorem continuous_gradModeIntegrand {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) :
    Continuous (fun p => gradModeIntegrand W κ σ b a x p) := by
  have h0 : Continuous fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x) :=
    (continuous_fderiv_slice hW).comp ((continuous_const.add continuous_fst).prodMk
      (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const))
  have h1 := h0.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => unitVector a)
    continuous_snd continuous_const)
  have h2 := ModeDerivative.Internal.continuous_axialRot_comp continuous_snd.neg h1
  exact (continuous_expFactor κ).mul (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ b).comp h2))

theorem continuous_gradModeIntegrandDeriv {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) :
    Continuous (fun p => gradModeIntegrandDeriv W κ σ b a x p) := by
  refine continuous_clm_apply.2 fun u => ?_
  simp only [gradModeIntegrandDeriv_apply]
  have h0 : Continuous fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ (W (σ + p.1))) (axialRot p.2 x) :=
    (secondDeriv_continuous hW).comp ((continuous_const.add continuous_fst).prodMk
      (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const))
  have h1 := (h0.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => u)
    continuous_snd continuous_const)).clm_apply
    (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => unitVector a) continuous_snd
      continuous_const)
  have h2 := ModeDerivative.Internal.continuous_axialRot_comp continuous_snd.neg h1
  exact (continuous_expFactor κ).mul (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ b).comp h2))

theorem modeGrad_eq_box {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) :
    modeGrad κ (gradField W) σ x (b, a)
      = (1 / (2 * Real.pi) : ℂ) * ∫ p, gradModeIntegrand W κ σ b a x p ∂boxMeasure := by
  unfold modeGrad
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor κ τ φ * ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x)
    (axialRot φ (unitVector a))) b : ℝ) : ℂ))
    (StretchInternal.integrable_box_of_continuous (continuous_gradModeIntegrand hW κ σ b a x))

theorem modeGrad_hasFDerivAt {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (fderiv ℝ (W s)) y‖ ≤ B) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (y : Space) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeGrad κ (gradField W) σ x (b, a)) L y ∧
      ∀ j, L (unitVector j) = modeSecondDeriv κ (secondDerivField W) σ y (b, j, a) := by
  have hbound : ∀ᵐ p ∂boxMeasure, ∀ x ∈ (Set.univ : Set Space),
      ‖gradModeIntegrandDeriv W κ σ b a x p‖ ≤ B :=
    Filter.Eventually.of_forall fun p x _ => (norm_gradModeIntegrandDeriv_le W κ σ b a x p).trans (hB _ _)
  refine ⟨(1 / (2 * Real.pi) : ℂ) • ∫ p, gradModeIntegrandDeriv W κ σ b a y p ∂boxMeasure, ?_, ?_⟩
  · have hfun : (fun x => modeGrad κ (gradField W) σ x (b, a)) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, gradModeIntegrand W κ σ b a x p ∂boxMeasure := by
      funext x
      exact modeGrad_eq_box hW κ σ b a x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => gradModeIntegrand W κ σ b a x p) (F' := fun x p => gradModeIntegrandDeriv W κ σ b a x p)
      (bound := fun _ => B) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (continuous_gradModeIntegrand hW κ σ b a x).aestronglyMeasurable)
      (StretchInternal.integrable_box_of_continuous (continuous_gradModeIntegrand hW κ σ b a y))
      (continuous_gradModeIntegrandDeriv hW κ σ b a y).aestronglyMeasurable hbound
      (StretchInternal.integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => hasFDerivAt_gradModeIntegrand hW κ σ b a x p)
    exact hI.const_mul _
  · intro j
    have hint := StretchInternal.integrable_box_of_continuous (continuous_gradModeIntegrandDeriv hW κ σ b a y)
    rw [smul_apply, ContinuousLinearMap.integral_apply hint, smul_eq_mul]
    unfold modeSecondDeriv
    rw [modeAverage_eq]
    congr 1
    rw [iter_eq_prod (fun τ φ => expFactor κ τ φ * ((axialRot (-φ) (secondDerivField W (σ + τ) (axialRot φ y)
      (axialRot φ (unitVector j)) (axialRot φ (unitVector a))) b : ℝ) : ℂ))]
    · rfl
    · exact (hint.apply_continuousLinearMap (unitVector j)).congr (Filter.Eventually.of_forall fun p => rfl)

theorem secondDeriv_bound_of_decay {W : ℝ → Space → Space}
    (hD : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ B, ∀ s x, ‖fderiv ℝ (fderiv ℝ (W s)) x‖ ≤ B := by
  obtain ⟨D, hD⟩ := hD
  refine ⟨|D|, fun s x => ?_⟩
  have h := hD s x 2 le_rfl
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  refine h.trans ?_
  have hp : 1 ≤ (1 + ‖x‖) ^ (2 + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
  calc D / (1 + ‖x‖) ^ (2 + 1) ≤ |D| / (1 + ‖x‖) ^ (2 + 1) :=
        div_le_div_of_nonneg_right (le_abs_self D) (by positivity)
    _ ≤ |D| := div_le_self (abs_nonneg D) hp

theorem modeSecondDeriv_neg (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (ijl : Fin 3 × Fin 3 × Fin 3) : modeSecondDeriv (-ι) H σ y ijl = (starRingEnd ℂ) (modeSecondDeriv ι H σ y ijl) := by
  unfold modeSecondDeriv
  exact modeAverage_neg _ _ _

theorem secondDeriv_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) {B₂ : ℝ} (hB₂ : ∀ s y, ‖fderiv ℝ (fderiv ℝ (W s)) y‖ ≤ B₂)
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (b j a : Fin 3) :
    axialRot (-φ) (fderiv ℝ (fderiv ℝ (W (σ + τ))) (axialRot φ y) (axialRot φ (unitVector j))
        (axialRot φ (unitVector a))) b
      = (modeSecondDeriv (0, 0) (secondDerivField W) σ y (b, j, a)).re
        + ∑ α ∈ s, (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeSecondDeriv α (secondDerivField W) σ y (b, j, a)).re := by
  set c : ℤ × ℤ → ℂ := fun α => Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
  have hf : HasFDerivAt (fun x => axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x) (axialRot φ (unitVector a))) b)
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp ((StretchInternal.rotCLM (-φ)).comp
        ((ContinuousLinearMap.apply ℝ Space (axialRot φ (unitVector a))).comp
          ((fderiv ℝ (fderiv ℝ (W (σ + τ))) (axialRot φ y)).comp (StretchInternal.rotCLM φ))))) y := by
    have h1 : HasFDerivAt (fun x => axialRot φ x) (StretchInternal.rotCLM φ) y :=
      (StretchInternal.rotCLM φ).hasFDerivAt
    have h2 := ((slice_fderiv_differentiable hW (σ + τ)) (axialRot φ y)).hasFDerivAt
    have h3 := h2.comp y h1
    have h4 := (ContinuousLinearMap.apply ℝ Space (axialRot φ (unitVector a))).hasFDerivAt.comp y h3
    have h5 := (StretchInternal.rotCLM (-φ)).hasFDerivAt.comp y h4
    exact (EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y h5
  choose L hL hLe using fun α => modeGrad_hasFDerivAt hW hB₂ α σ b a y
  have hg : HasFDerivAt (fun x => (modeGrad (0, 0) (gradField W) σ x (b, a)).re
        + ∑ α ∈ s, (c α * modeGrad α (gradField W) σ x (b, a)).re)
      (Complex.reCLM.comp (L (0, 0)) + ∑ α ∈ s, Complex.reCLM.comp (c α • L α)) y := by
    refine (Complex.reCLM.hasFDerivAt.comp y (hL (0, 0))).add ?_
    refine HasFDerivAt.fun_sum fun α _ => ?_
    exact Complex.reCLM.hasFDerivAt.comp y ((hL α).const_mul (c α))
  have heq : (fun x => axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x) (axialRot φ (unitVector a))) b)
      = fun x => (modeGrad (0, 0) (gradField W) σ x (b, a)).re + ∑ α ∈ s, (c α * modeGrad α (gradField W) σ x (b, a)).re :=
    funext fun x => grad_expansion hW hB hWp s hh σ τ φ x b a
  rw [heq] at hf
  have hu := congrArg (fun T : Space →L[ℝ] ℝ => T (unitVector j)) (hf.unique hg)
  simp only [ContinuousLinearMap.comp_apply, add_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_apply, Complex.reCLM_apply, smul_eq_mul, hLe] at hu
  rw [← hu]
  rfl

theorem secondDerivC_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) {B₂ : ℝ} (hB₂ : ∀ s y, ‖fderiv ℝ (fderiv ℝ (W s)) y‖ ≤ B₂)
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (b j a : Fin 3) :
    ((axialRot (-φ) (fderiv ℝ (fderiv ℝ (W (σ + τ))) (axialRot φ y) (axialRot φ (unitVector j))
        (axialRot φ (unitVector a))) b : ℝ) : ℂ)
      = (((modeSecondDeriv (0, 0) (secondDerivField W) σ y (b, j, a)).re : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeSecondDeriv α (secondDerivField W) σ y (b, j, a) := by
  rw [secondDeriv_expansion hW hB hB₂ hWp s hh σ τ φ y b j a, Complex.ofReal_add]
  congr 1
  exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeSecondDeriv_neg, map_mul]

theorem meanCurl_fderiv_apply {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) {B₂ : ℝ} (hB₂ : ∀ s y, ‖fderiv ℝ (fderiv ℝ (W s)) y‖ ≤ B₂)
    (hWp : IsTimePeriodic W) (σ : ℝ) (y : Space) (i j : Fin 3) :
    fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y (unitVector j) i
      = ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol i a b * (modeSecondDeriv (0, 0) (secondDerivField W) σ y (b, j, a)).re := by
  have hc : ∀ x k, curlVec (fderiv ℝ (meanField W) x) k
      = ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol k a b * (modeGrad (0, 0) (gradField W) σ x (b, a)).re := by
    intro x k
    rw [StretchInternal.curlVec_apply]
    simp_rw [meanField_fderiv_apply hW hB hWp σ x]
  choose L hL hLe using fun ba : Fin 3 × Fin 3 => modeGrad_hasFDerivAt hW hB₂ (0, 0) σ ba.1 ba.2 y
  have hcomp : ∀ k, HasFDerivAt (fun x => curlVec (fderiv ℝ (meanField W) x) k)
      (∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol k a b • Complex.reCLM.comp (L (b, a))) y := by
    intro k
    rw [show (fun x => curlVec (fderiv ℝ (meanField W) x) k) = fun x => ∑ a : Fin 3, ∑ b : Fin 3,
      alternatingSymbol k a b * (modeGrad (0, 0) (gradField W) σ x (b, a)).re from funext fun x => hc x k]
    exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
      (Complex.reCLM.hasFDerivAt.comp y (hL (b, a))).const_mul _
  have hd : HasFDerivAt (fun x => curlVec (fderiv ℝ (meanField W) x))
      (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol k a b • Complex.reCLM.comp (L (b, a))).smulRight
        (unitVector k)) y := by
    rw [show (fun x => curlVec (fderiv ℝ (meanField W) x))
      = fun x => ∑ k : Fin 3, curlVec (fderiv ℝ (meanField W) x) k • unitVector k from
        funext fun x => vec_expand _]
    exact HasFDerivAt.fun_sum fun k _ => (hcomp k).smul_const (unitVector k)
  rw [hd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [space_sum_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply, smul_eq_mul, hLe]

theorem vortGradW_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) {B₂ : ℝ} (hB₂ : ∀ s y, ‖fderiv ℝ (fderiv ℝ (W s)) y‖ ≤ B₂)
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (i j : Fin 3) :
    ((axialRot (-φ) (fderiv ℝ (vortField W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = ((fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y (unitVector j) i : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) σ y) (i, j) := by
  have e := vortGrad_eq hW (σ + τ) (axialRot φ y)
  have e' : fderiv ℝ (vortField W (σ + τ)) (axialRot φ y)
      = Internal.SmoothPieceEps.curlLinear.comp (fderiv ℝ (fderiv ℝ (W (σ + τ))) (axialRot φ y)) := e
  rw [e', ContinuousLinearMap.comp_apply, Internal.SmoothPieceEps.curlLinear_apply,
    ← Internal.CurlEnergy.curlVec_axialRot, meanCurl_fderiv_apply hW hB hB₂ hWp σ y i j]
  push_cast
  simp_rw [secondDerivC_expansion hW hB hB₂ hWp s hs hh σ τ φ y]
  unfold curlGradOfSecondDeriv
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  simp only [Fin.sum_univ_three, Finset.sum_add_distrib]
  simp only [mul_left_comm]
  push_cast
  rfl

end Internal.SmoothEpsPointwise

end Coercive

end Breakdown
