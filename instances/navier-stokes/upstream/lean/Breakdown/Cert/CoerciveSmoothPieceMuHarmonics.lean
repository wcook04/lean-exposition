import Breakdown.Cert.CoerciveSmoothMuWave

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuHarmonics

theorem velAmp_neg (W : ℝ → Space → Space) (β : ℤ × ℤ) (σ : ℝ) (y : Space) :
    velAmp W (-β) σ y = velAmp W β σ y := by
  unfold velAmp cnormSq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Internal.SmoothPieceMuDivergence.modeVel_neg, Complex.norm_conj]

theorem exp_sum_real (H : Finset (ℤ × ℤ)) (hH : ∀ β ∈ H, -β ∈ H) (c : ℤ × ℤ → ℂ)
    (hc : ∀ β, c (-β) = (starRingEnd ℂ) (c β)) (τ φ : ℝ) :
    ∑ β ∈ H, Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * c β
      = ((∑ β ∈ H, (Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * c β).re : ℝ) : ℂ) := by
  set f : ℤ × ℤ → ℂ := fun β => Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * c β
    with hf
  have hneg : ∀ β, f (-β) = (starRingEnd ℂ) (f β) := by
    intro β
    rw [hf]
    simp only [map_mul, hc, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg,
      Prod.snd_neg, Int.cast_neg]
    congr 2
    push_cast
    ring
  have hconj : (starRingEnd ℂ) (∑ β ∈ H, f β) = ∑ β ∈ H, f β := by
    rw [map_sum]
    refine Finset.sum_nbij' (fun β => -β) (fun β => -β) (fun β hb => hH β hb) (fun β hb => hH β hb)
      (fun β _ => neg_neg β) (fun β _ => neg_neg β) fun β _ => ?_
    rw [hneg]
  have hre : ((∑ β ∈ H, f β).re : ℂ) = ∑ β ∈ H, f β := Complex.conj_eq_iff_re.1 hconj
  rw [← hre, Complex.re_sum]

theorem orbit_expansion_re (H : Finset (ℤ × ℤ)) (W : ℝ → Space → Space)
    (hWc : Continuous (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hspan : ∀ σ y i, W σ y i = ∑ β ∈ H, (modeVel β W σ y i).re)
    (σ : ℝ) (y : Space) (τ φ : ℝ) (i : Fin 3) :
    axialRot (-φ) (W (σ + τ) (axialRot φ y)) i
      = ∑ β ∈ H, (Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeVel β W σ y i).re := by
  have hS : ∀ β : ℤ × ℤ, Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeVel β W σ y i
      = ∑ k : Fin 3, ((axialRot (-φ) (unitVector k) i : ℝ) : ℂ) * modeVel β W (σ + τ) (axialRot φ y) k := by
    intro β
    rw [← Internal.SmoothPieceMuDivergence.modeVel_shiftRot β W hWp τ φ σ y i,
      Internal.MuSmooth.rot_modeVel_eq hWc]
  simp_rw [hS, Internal.MuSmooth.re_sum_real_mul]
  rw [Internal.ModeRotation.axialRot_apply (-φ) _ i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hspan (σ + τ) (axialRot φ y) k, Finset.mul_sum]

theorem orbit_expansion {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (σ : ℝ) (y : Space) (τ φ : ℝ) (i : Fin 3) :
    ((axialRot (-φ) (W (σ + τ) (axialRot φ y)) i : ℝ) : ℂ)
      = ∑ β ∈ h.harmonics, Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
        * modeVel β W σ y i := by
  rw [orbit_expansion_re h.harmonics W hW.continuous hWp hm.harmonics_span σ y τ φ i]
  refine Internal.MuSmooth.re_sum_sym h.harmonics hm.harmonics_neg
    (fun β => Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel β W σ y i)
    fun β => ?_
  rw [Internal.MuSmooth.phase_neg, Internal.SmoothPieceMuDivergence.modeVel_neg, map_mul]

section Derivative

open Filter Internal.ModeRotation ModeDerivative.Internal CurlWeight.Internal.TestModes

theorem modeVel_hasFDerivAt_local {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (y : Space) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeVel ι W σ x l) L y ∧
      ∀ j, L (unitVector j) = modeGrad ι (gradField W) σ y (l, j) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ Set.Icc σ (σ + 1) ×ˢ Metric.closedBall (0 : Space) (‖y‖ + 1),
      ‖fderiv ℝ (W z.1) z.2‖ ≤ B :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      (Internal.MuSmooth.continuous_slice_fderiv_of hW).continuousOn
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
      exact Internal.MuSmooth.modeVel_eq_box_of hW ι σ l x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => modeTestIntegrand W ι σ l x p) (F' := fun x p => modeTestIntegrandDeriv W ι σ l x p)
      (bound := fun _ => B) (Metric.ball_mem_nhds y one_pos)
      (Filter.Eventually.of_forall fun x =>
        (Internal.MuSmooth.continuous_integrand_of hW ι σ l x).aestronglyMeasurable)
      (integrable_box_of_continuous (Internal.MuSmooth.continuous_integrand_of hW ι σ l y))
      (Internal.MuSmooth.continuous_integrandDeriv_of hW ι σ l y).aestronglyMeasurable hbound
      (integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => Internal.MuSmooth.hasFDerivAt_integrand_of hW ι σ l x p)
    exact hI.const_mul _
  · intro j
    have hint := integrable_box_of_continuous (Internal.MuSmooth.continuous_integrandDeriv_of hW ι σ l y)
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
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
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
      ((Internal.MuSmooth.slice_differentiable_of hW (σ + τ)) (Rp y)).hasFDerivAt.comp y Rp.hasFDerivAt
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
    funext fun x => orbit_expansion_re H W hW.continuous hWp hspan σ x τ φ i
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
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
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
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
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
    rw [grad_orbit_expansion m P h w W hm hW hWp σ y τ φ i j, Complex.ofReal_zero, zero_add]
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

end Internal.SmoothPieceMuHarmonics

end Coercive

end Breakdown
