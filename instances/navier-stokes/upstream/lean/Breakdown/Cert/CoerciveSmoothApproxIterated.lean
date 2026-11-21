import Breakdown.Cert.CoerciveSmoothApproxDerivative
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem norm_iteratedFDeriv_convolution_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : LocallyIntegrable f volume) (k : ℕ) :
    ∀ {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F']
      [NormedSpace ℝ F'] [CompleteSpace F'] (ψ : ℝ × Space → E')
      (L : E' →L[ℝ] E →L[ℝ] F'), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ‖L‖ ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ k (ψ ⋆[L, volume] f) x‖ ≤ ∫ t, ‖iteratedFDeriv ℝ k ψ t‖ * ‖f (x - t)‖ := by
  have := volume_prod_invariantClass
  induction k with
  | zero =>
    intro E' F' _ _ _ _ _ ψ L hψ hc hL x
    rw [norm_iteratedFDeriv_zero, convolution_def]
    have hex := (hc.norm.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ.continuous.norm hf) x
    refine norm_integral_le_of_norm_le (hex.norm.congr (Eventually.of_forall fun t => by
      simp [norm_smul])) (Eventually.of_forall fun t => ?_)
    rw [norm_iteratedFDeriv_zero]
    calc ‖L (ψ t) (f (x - t))‖ ≤ ‖L (ψ t)‖ * ‖f (x - t)‖ := (L (ψ t)).le_opNorm _
      _ ≤ ‖L‖ * ‖ψ t‖ * ‖f (x - t)‖ := by gcongr; exact L.le_opNorm _
      _ ≤ 1 * ‖ψ t‖ * ‖f (x - t)‖ := by gcongr
      _ = ‖ψ t‖ * ‖f (x - t)‖ := by ring
  | succ k ih =>
    intro E' F' _ _ _ _ _ ψ L hψ hc hL x
    have hd : fderiv ℝ (ψ ⋆[L, volume] f) = fderiv ℝ ψ ⋆[L.precompL (ℝ × Space), volume] f := by
      funext z
      exact (hc.hasFDerivAt_convolution_left L (hψ.of_le (by exact_mod_cast le_top)) hf z).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    refine (ih (fderiv ℝ ψ) (L.precompL (ℝ × Space)) (hψ.fderiv_right (by simp)) (hc.fderiv (𝕜 := ℝ))
      ((ContinuousLinearMap.norm_precompL_le (ℝ × Space) L).trans hL) x).trans (le_of_eq ?_)
    simp only [norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_slice_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × Space → F} (hh : ContDiff ℝ ∞ h) (k : ℕ) (σ : ℝ) (y : Space) :
    ‖iteratedFDeriv ℝ k (fun y => h (σ, y)) y‖ ≤ ‖iteratedFDeriv ℝ k h (σ, y)‖ := by
  have e : (fun y : Space => h (σ, y)) =
      (fun z => h ((σ, 0) + z)) ∘ (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext y
    simp
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Space => h ((σ, 0) + z)) :=
    hh.comp (contDiff_const.add contDiff_id)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs y (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ Space‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp
  have hp : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ Space‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hinr
  have hxy : ((σ, 0) : ℝ × Space) + (ContinuousLinearMap.inr ℝ ℝ Space) y = (σ, y) := by simp
  rw [hxy]
  calc ‖iteratedFDeriv ℝ k h (σ, y)‖ * ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ Space‖
      ≤ ‖iteratedFDeriv ℝ k h (σ, y)‖ * 1 := by gcongr
    _ = ‖iteratedFDeriv ℝ k h (σ, y)‖ := mul_one _

theorem mollify_fderiv_clm (n : ℕ) {f : ℝ → Space → Space} {F : ℝ → Space → (Space →L[ℝ] Space)}
    (hf : LocallyIntegrable (joint f) volume) (hF : LocallyIntegrable (joint F) volume)
    (hw : ∀ᵐ s, IsWeakGradient (f s) (F s)) (σ : ℝ) :
    fderiv ℝ (mollify n f σ) = fun y => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint F) (σ, y) := by
  have := volume_prod_invariantClass
  funext y
  refine ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_)
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe]
  have h1 := mollify_partial n hf hF hw i σ y
  simp only [unitVector] at h1
  rw [h1]
  have hex := ((kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_contDiff n).continuous hF) (σ, y)
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  simp [mollify, convolution_def, joint]

end Internal.SmoothApprox

end Coercive

end Breakdown
