import Breakdown.Cert.CoerciveSmoothPieceMuReflect
import Breakdown.Cert.ExtendedCoercivePairingSplit

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.WeakPieceMuHarmonics

open Filter

open Internal.ModeRotation ModeDerivative.Internal CurlWeight.Internal.TestModes Internal.MuSmooth

theorem orbit_expansion {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (σ : ℝ) (y : Space) (τ φ : ℝ) (i : Fin 3) :
    ((axialRot (-φ) (W (σ + τ) (axialRot φ y)) i : ℝ) : ℂ)
      = ∑ β ∈ h.harmonics, Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeVel β W σ y i := by
  rw [Internal.SmoothPieceMuHarmonics.orbit_expansion_re h.harmonics W hW.continuous hWp hm.harmonics_span σ y τ φ i]
  refine Internal.MuSmooth.re_sum_sym h.harmonics hm.harmonics_neg
    (fun β => Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel β W σ y i)
    fun β => ?_
  rw [Internal.MuSmooth.phase_neg, Internal.SmoothPieceMuDivergence.modeVel_neg, map_mul]

theorem continuous_slice_fderiv_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
  (ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => W z.1 y) (g := fun z => z.2)
    (hW.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (n := 0) (by norm_num)).continuous

theorem hasFDerivAt_integrand_of {W : ℝ → Space → Space}
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
    (((hW.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ 1 (W (σ + p.1)))).differentiable (by norm_num) _).hasFDerivAt
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

theorem continuous_integrandDeriv_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrandDeriv W ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) :=
    (continuous_slice_fderiv_of hW).comp ((continuous_const.add continuous_fst).prodMk
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

theorem continuous_integrand_of {W : ℝ → Space → Space}
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

theorem modeVel_eq_box_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ)
    (l : Fin 3) (x : Space) :
    modeVel ι W σ x l = (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
  unfold modeVel
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (W (σ + τ) (axialRot φ x)) l : ℝ) : ℂ))
    (integrable_box_of_continuous (continuous_integrand_of hW ι σ l x))

section Derivative

open Filter Internal.ModeRotation ModeDerivative.Internal CurlWeight.Internal.TestModes

theorem modeVel_hasFDerivAt_local {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (y : Space) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeVel ι W σ x l) L y ∧
      ∀ j, L (unitVector j) = modeGrad ι (gradField W) σ y (l, j) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ Set.Icc σ (σ + 1) ×ˢ Metric.closedBall (0 : Space) (‖y‖ + 1),
      ‖fderiv ℝ (W z.1) z.2‖ ≤ B :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      (continuous_slice_fderiv_of hW).continuousOn
  have hbound : ∀ᵐ p ∂boxMeasure, ∀ x ∈ Metric.ball y 1,
      ‖modeTestIntegrandDeriv W ι σ l x p‖ ≤ B := by
    filter_upwards [ae_box_mem] with p hp x hx
    refine (norm_modeTestIntegrandDeriv_le ι σ l x p).trans (hB (σ + p.1, axialRot p.2 x) ⟨?_, ?_⟩)
    · exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    · rw [Metric.mem_closedBall, dist_zero_right,
        Internal.ModeRotation.norm_axialRot axialRotationHolds_proof]
      exact (norm_lt_of_mem_ball hx).le
  refine ⟨(1 / (2 * Real.pi) : ℂ) • ∫ p, modeTestIntegrandDeriv W ι σ l y p ∂boxMeasure, ?_, ?_⟩
  · have hfun : (fun x => modeVel ι W σ x l) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
      funext x
      exact modeVel_eq_box_of hW ι σ l x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => modeTestIntegrand W ι σ l x p) (F' := fun x p => modeTestIntegrandDeriv W ι σ l x p)
      (bound := fun _ => B) (Metric.ball_mem_nhds y one_pos)
      (Filter.Eventually.of_forall fun x =>
        (continuous_integrand_of hW ι σ l x).aestronglyMeasurable)
      (integrable_box_of_continuous (continuous_integrand_of hW ι σ l y))
      (continuous_integrandDeriv_of hW ι σ l y).aestronglyMeasurable hbound
      (integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => hasFDerivAt_integrand_of hW ι σ l x p)
    exact hI.const_mul _
  · intro j
    have hint := integrable_box_of_continuous (continuous_integrandDeriv_of hW ι σ l y)
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

theorem grad_orbit_expansion_re (H : Finset (ℤ × ℤ)) {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hspan : ∀ σ y i, W σ y i = ∑ β ∈ H, (modeVel β W σ y i).re)
    (σ : ℝ) (y : Space) (τ φ : ℝ) (i j : Fin 3) :
    axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i
      = ∑ β ∈ H, (Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeGrad β (gradField W) σ y (i, j)).re := by
  have hRot := axialRotationHolds_proof
  set Rp : Space →L[ℝ] Space := ((rotIso hRot φ).toContinuousLinearEquiv : Space →L[ℝ] Space)
  set Rm : Space →L[ℝ] Space := ((rotIso hRot φ).symm.toContinuousLinearEquiv : Space →L[ℝ] Space)
  have hRp : ∀ x, Rp x = axialRot φ x := fun x => rotIso_apply hRot φ x
  have hRm : ∀ x, Rm x = axialRot (-φ) x := fun x => rotIso_symm_apply hRot φ x
  have hf : HasFDerivAt (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (Rm.comp ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp))) y := by
    have h1 : HasFDerivAt (fun x => W (σ + τ) (Rp x)) ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp) y :=
      ((((hW.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ 1 (W (σ + τ)))).differentiable (by norm_num)) (Rp y)).hasFDerivAt.comp y Rp.hasFDerivAt
    have h2 := (Rm.hasFDerivAt (x := W (σ + τ) (Rp y))).comp y h1
    have h3 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h2
    have hfun : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
        = (⇑(EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ ⇑Rm ∘ fun x => W (σ + τ) (Rp x)) := by
      funext x
      simp only [Function.comp, hRp, hRm]
      rfl
    rw [hfun]
    exact h3
  choose L hL hLe using fun α => modeVel_hasFDerivAt_local hW α σ i y
  have hg : HasFDerivAt (fun x => ∑ α ∈ H,
        (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ x i).re)
      (∑ α ∈ H, Complex.reCLM.comp
        (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) • L α)) y :=
    HasFDerivAt.fun_sum fun α _ => Complex.reCLM.hasFDerivAt.comp y ((hL α).const_mul _)
  have heq : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      = fun x => ∑ α ∈ H,
        (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ x i).re :=
    funext fun x => Internal.SmoothPieceMuHarmonics.orbit_expansion_re H W hW.continuous hWp hspan σ x τ φ i
  rw [heq] at hf
  have hu := congrArg (fun T : Space →L[ℝ] ℝ => T (unitVector j)) (hf.unique hg)
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_apply, Complex.reCLM_apply, smul_eq_mul, hLe] at hu
  rw [← hu]
  simp only [hRp, hRm]
  rfl

end Derivative

theorem grad_orbit_expansion {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (σ : ℝ) (y : Space) (τ φ : ℝ) (i j : Fin 3) :
    ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = ∑ β ∈ h.harmonics, Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeGrad β (gradField W) σ y (i, j) := by
  rw [grad_orbit_expansion_re h.harmonics hW hWp hm.harmonics_span σ y τ φ i j]
  refine Internal.MuSmooth.re_sum_sym h.harmonics hm.harmonics_neg
    (fun β => Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
      * modeGrad β (gradField W) σ y (i, j)) fun β => ?_
  rw [Internal.MuSmooth.phase_neg, Internal.MuSmooth.modeGrad_neg, map_mul]

theorem stretch_mode_le {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (v : ℝ → Space → Space) (hvc : Continuous (fun z : ℝ × Space => v z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    velAmp (fun σ y => fderiv ℝ (W σ) y (v σ y)) ι σ y
      ≤ ∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y := by
  have hE : ∀ τ φ : ℝ, ∀ i j : Fin 3,
      ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
        = (((0 : ℝ) : ℝ) : ℂ) + ∑ α ∈ h.harmonics,
          Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
            * modeGrad α (gradField W) σ y (i, j) := by
    intro τ φ i j
    rw [grad_orbit_expansion m P h w W HW hm hW hWp σ y τ φ i j, Complex.ofReal_zero, zero_add]
  have hmp := fun i => Internal.MuSmooth.mode_product h.harmonics W v hvc σ y (fun _ _ => 0)
    (fun α ij => modeGrad α (gradField W) σ y ij) hE ι i
  have hsplit : modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y
      = ∑ α ∈ h.harmonics,
        (fun i => ∑ j : Fin 3, modeGrad α (gradField W) σ y (i, j) * modeVel (ι - α) v σ y j) := by
    funext i
    rw [hmp i, Finset.sum_apply]
    simp only [Complex.ofReal_zero, zero_mul, zero_add]
    exact Finset.sum_comm
  show Internal.MuSmooth.cnorm3 (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)
    ≤ ∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y
  rw [hsplit]
  refine (Internal.MuSmooth.cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  exact Internal.MuSmooth.cnorm3_mat_le (fun ij => modeGrad α (gradField W) σ y ij) _

end Internal.WeakPieceMuHarmonics

namespace Internal.WeakPieceMuReflect

open ModeL2Internal (IsSquareField weightedModeTerm slab)

private def pressDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (β : Fin nM) (ι : ℤ × ℤ) (z : ℝ × Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
    * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2 / (2 * (m.muP β).eta)
      + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)

private def reflDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (v Y : ℝ → Space → Space) (β : Fin nM) (ι : ℤ × ℤ) (z : ℝ × Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
    * (cnormSq (modeVel ι Y z.1 z.2) / (2 * (m.muP β).eta)
      + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)

theorem reflected_pairing_bound_weak {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (_hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
        (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds)
    (Y : ℝ → Space → Space)
    (hYm : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) (hYp : IsTimePeriodic Y)
    (hY2 : periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤)
    (hYmodes : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Y σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)))
    (hPr : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) < ⊤) :
    -(∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))).toReal ≤ muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Y := by
  have hη : 0 < (m.muP β).eta := hm.mu_eta_pos β
  have hη2 : 0 < 2 * (m.muP β).eta := by linarith
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  obtain ⟨Kl, hKl⟩ := hm.mu_increment β
  have hφc : Continuous (m.muP β).wt := hKl.continuous
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGc : Continuous (fun z : ℝ × Space => gradField W z.1 z.2) :=
    Internal.WeakPieceMuHarmonics.continuous_slice_fderiv_of hW
  have hFc : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    (Internal.WeakPieceMuHarmonics.continuous_slice_fderiv_of hW).clm_apply hvc
  obtain ⟨B, hB⟩ := CoerciveWeak.Internal.WeakPairingSplit.muWeight_bound hm
  have hB' : ∀ ι y, |CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι y| ≤ B := hB β
  have hwm := CoerciveWeak.Internal.WeakPairingSplit.muWeight_measurable hm β
  have hU := Internal.SmoothWeightSplit.scaledField_square hv
  have hYs : IsSquareField Y := ⟨hYm, hYp, hY2⟩
  obtain ⟨K, hK⟩ := ModeL2Internal.weightedMode_bound hPars (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β) hwm hB' hU
  have hsY := (hK _ _ hYs hYs).1
  have e : muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Y
      = ∑' ι, weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β)
        (Internal.SmoothWeightSplit.scaledField v) Y ι :=
    Internal.SmoothPieceSplit.muPairing_eq_scaled _ v Y
  have hqc : ∀ ι, Continuous (pressDensity m h W v β ι) := by
    intro ι
    unfold pressDensity
    refine continuous_const.mul (((continuous_finsetSum _ fun α _ =>
      (Internal.MuSmooth.continuous_gradAmp hGc α).mul (Internal.MuSmooth.continuous_velAmp hvc (ι - α))).pow 2).div_const _
        |>.add (((continuous_const.mul ((hφc.comp continuous_snd).pow 2)).mul
          ((Internal.MuSmooth.continuous_velAmp hvc ι).pow 2))))
  have hqm : ∀ ι, AEMeasurable (fun z => ENNReal.ofReal (pressDensity m h W v β ι z)) slab :=
    fun ι => (ENNReal.measurable_ofReal.comp (hqc ι).measurable).aemeasurable
  have hPrEq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) = ∑' ι, ∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab := by
    rw [← lintegral_tsum hqm]
    exact (lintegral_prod _ (AEMeasurable.tsum hqm)).symm
  rw [hPrEq] at hPr ⊢
  have hQt : ∀ ι, ∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hPr.ne (ENNReal.le_tsum ι)
  have hterm : ∀ ι, -weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β)
      (Internal.SmoothWeightSplit.scaledField v) Y ι
        ≤ (∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab).toReal := by
    intro ι
    have hint := ModeL2Internal.integrable_weightedMode hPars _ hwm hB' hU hYs ι
    rw [ModeL2Internal.weightedModeTerm_eq hPars _ hwm hB' hU hYs ι, ← integral_neg]
    have h1 : ∫ z, -(Complex.I * (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂slab
        ≤ (∫⁻ z, ENNReal.ofReal (-(Complex.I * (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) ∂slab).toReal := by
      have hn : Integrable (fun z : ℝ × Space => -(Complex.I * (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) slab :=
        hint.neg
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hn]
      linarith [@ENNReal.toReal_nonneg (∫⁻ z, ENNReal.ofReal (- -(Complex.I * (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) ∂slab)]
    refine h1.trans (ENNReal.toReal_mono (hQt ι) ?_)
    have hd0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
      rcases Internal.SmoothPieceMuReflect.ind_cases (PieceWeights.inPiece (m.muP β).modes ι) with h | h <;> simp [h]
    have hb0 : ∀ z : ℝ × Space, 0 ≤ (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2 :=
      fun z => by positivity
    have hpt : ∀ z : ℝ × Space, ENNReal.ofReal (-(Complex.I * (CoerciveWeak.Internal.WeakPairingSplit.muWeight m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re)
        ≤ ENNReal.ofReal (reflDensity m v Y β ι z) := by
      intro z
      apply ENNReal.ofReal_le_ofReal
      exact Internal.SmoothPieceMuReflect.pointwise_absorb (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)
        (Internal.SmoothPieceMuReflect.abs_sgn _ ι) (Internal.SmoothPieceMuReflect.ind_cases _) (hφ0 z.2) (by positivity) hη
        (Internal.SmoothPieceMuReflect.cnormSq_scaled v ι z.1 z.2)
    have hYa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2))) slab :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (ModeL2Internal.aestronglyMeasurable_cnormSq
        (fun i => Internal.FieldModes.aestronglyMeasurable_modeVel hYm ι i)).aemeasurable).mono_ac ModeL2Internal.slab_ac
    have hFa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι
        (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2))) slab :=
      (ENNReal.measurable_ofReal.comp (Internal.MuSmooth.continuous_cnormSq_modeVel hFc ι).measurable).aemeasurable
    have hSc : Continuous (fun z : ℝ × Space => (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
        * velAmp v (ι - α) z.1 z.2) ^ 2) :=
      (continuous_finsetSum _ fun α _ =>
        (Internal.MuSmooth.continuous_gradAmp hGc α).mul (Internal.MuSmooth.continuous_velAmp hvc (ι - α))).pow 2
    have hSa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
        * velAmp v (ι - α) z.1 z.2) ^ 2)) slab :=
      (ENNReal.measurable_ofReal.comp hSc.measurable).aemeasurable
    have hYF : ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab
        = ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)) ∂slab := by
      calc ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab
          = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Y σ y)) := lintegral_prod _ hYa
        _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι
            (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)) := hYmodes ι
        _ = _ := (lintegral_prod _ hFa).symm
    have hFS : ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)) ∂slab
        ≤ ∫⁻ z, ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
          * velAmp v (ι - α) z.1 z.2) ^ 2) ∂slab := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have hs := Internal.WeakPieceMuHarmonics.stretch_mode_le m P h w W HW hm hW hWp v hvc ι z.1 z.2
      have e2 : cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)
          = velAmp (fun σ y => fderiv ℝ (W σ) y (v σ y)) ι z.1 z.2 ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      rw [e2]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    have e1 : ∀ z : ℝ × Space, ENNReal.ofReal (reflDensity m v Y β ι z)
        = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2))
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) := fun z =>
      Internal.SmoothPieceMuReflect.ofReal_split _ _ _ _ hd0 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hη2 (hb0 z)
    have e2 : ∀ z : ℝ × Space, ENNReal.ofReal (pressDensity m h W v β ι z)
        = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) := fun z =>
      Internal.SmoothPieceMuReflect.ofReal_split _ _ _ _ hd0 (sq_nonneg _) hη2 (hb0 z)
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (reflDensity m v Y β ι z) ∂slab := lintegral_mono hpt
      _ = _ := lintegral_congr fun z => e1 z
      _ = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * (∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab)
          + ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) ∂slab := by
          rw [lintegral_add_left' (hYa.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * (∫⁻ z, ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
              * velAmp v (ι - α) z.1 z.2) ^ 2) ∂slab)
          + ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) ∂slab := by
          rw [hYF]
          gcongr
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' (hSa.const_mul _)]
          exact lintegral_congr fun z => (e2 z).symm
  have hsQ : Summable (fun ι => (∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab).toReal) :=
    ENNReal.summable_toReal hPr.ne
  rw [ENNReal.tsum_toReal_eq hQt, e]
  have hle := hsY.neg.tsum_le_tsum hterm hsQ
  rw [tsum_neg] at hle
  linarith

end Internal.WeakPieceMuReflect

end Coercive

end Breakdown
