import Breakdown.Defs
import Breakdown.Cert.ExtendedCoerciveStatement
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakGradientSlope

theorem opNorm_le_of_columns (A : Space →L[ℝ] Space) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i, ‖A (unitVector i)‖ ≤ K) : ‖A‖ ≤ 3 * K := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw : w = ∑ i, w i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
  calc ‖A w‖ = ‖∑ i, w i • A (unitVector i)‖ := by
        conv_lhs => rw [hw]
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖w i • A (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖w‖ * K := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le w i) (h i) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * K * ‖w‖ := by simp; ring

section Mollify

variable {u : Space → Space} {g : Space → (Space →L[ℝ] Space)} {K : ℝ}

theorem test_reflect (ρ : ContDiffBump (0 : Space)) (x : Space) :
    IsTestFunction (fun t => ρ.normed volume (x - t)) := by
  refine ⟨(ρ.contDiff_normed (μ := volume)).comp (contDiff_const.sub contDiff_id), ?_⟩
  exact (ρ.hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.subLeft x)

theorem fderiv_reflect (ρ : ContDiffBump (0 : Space)) (x t w : Space) :
    fderiv ℝ (fun s => ρ.normed volume (x - s)) t w = -fderiv ℝ (ρ.normed volume) (x - t) w := by
  have hd : DifferentiableAt ℝ (ρ.normed volume) (x - t) :=
    ((ρ.contDiff_normed (μ := volume) (n := 1)).differentiable (by norm_num)) _
  have h1 : HasFDerivAt (fun s : Space => x - s) (-ContinuousLinearMap.id ℝ Space) t :=
    (hasFDerivAt_id t).const_sub x
  have h2 := hd.hasFDerivAt.comp t h1
  rw [show (fun s => ρ.normed volume (x - s)) = (ρ.normed volume) ∘ (fun s : Space => x - s) from rfl,
    h2.fderiv]
  simp

theorem mollify_hasFDerivAt (ρ : ContDiffBump (0 : Space)) (hu : LocallyIntegrable u) (x : Space) :
    HasFDerivAt (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      ((fderiv ℝ (ρ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] u) x) x :=
  (ρ.hasCompactSupport_normed (μ := volume)).hasFDerivAt_convolution_left _
    (ρ.contDiff_normed (μ := volume)) hu x

theorem mollify_column (ρ : ContDiffBump (0 : Space)) (hu : Continuous u) (hg : IsWeakGradient u g)
    (x : Space) (i : Fin 3) :
    ((fderiv ℝ (ρ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] u) x)
        (unitVector i) = ∫ t, ρ.normed volume (x - t) • g t (unitVector i) := by
  have hw := hg.2.2 _ (test_reflect ρ x) i
  have hc : Continuous (fun t => fderiv ℝ (ρ.normed volume) (x - t)) :=
    ((ρ.contDiff_normed (μ := volume) (n := 1)).continuous_fderiv (by norm_num)).comp
      (continuous_const.sub continuous_id)
  have hs : HasCompactSupport (fun t => fderiv ℝ (ρ.normed volume) (x - t)) :=
    ((ρ.hasCompactSupport_normed (μ := volume)).fderiv (𝕜 := ℝ)).comp_homeomorph (Homeomorph.subLeft x)
  have hint : Integrable (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space)
      (fderiv ℝ (ρ.normed volume) (x - t)) (u t)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space).continuous₂.comp (hc.prodMk hu))
    · refine hs.mono fun t ht => ?_
      contrapose! ht
      rw [Function.notMem_support] at ht ⊢
      simp [ht]
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hint, hw, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  rw [fderiv_reflect, neg_smul, neg_neg]

theorem mollify_column_norm_le (ρ : ContDiffBump (0 : Space)) (hgK : ∀ t, ‖g t‖ ≤ K) (x : Space)
    (i : Fin 3) : ‖∫ t, ρ.normed volume (x - t) • g t (unitVector i)‖ ≤ K := by
  have hint : Integrable (fun t => K * ρ.normed volume (x - t)) :=
    ((ρ.integrable_normed (μ := volume)).comp_sub_left x).const_mul K
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (ρ.nonneg_normed _)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 : ‖unitVector i‖ = 1 := by simp [unitVector]
    rw [h1, mul_one]
    exact hgK t
  · rw [integral_const_mul, integral_sub_left_eq_self (fun t => ρ.normed volume t) volume x,
      ρ.integral_normed, mul_one]

theorem mollify_slopeBound (ρ : ContDiffBump (0 : Space)) (hu : Continuous u) (hg : IsWeakGradient u g)
    (hK : 0 ≤ K) (hgK : ∀ t, ‖g t‖ ≤ K) :
    LipschitzWith (Real.toNNReal (3 * K)) (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  have hd := mollify_hasFDerivAt ρ hu.locallyIntegrable
  refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).fderiv]
  have := opNorm_le_of_columns _ hK fun i => by
    rw [mollify_column ρ hu hg x i]
    exact mollify_column_norm_le ρ hgK x i
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  exact this

theorem slopeBound_of_weakGradient (hu : Continuous u) (hg : IsWeakGradient u g) (hK : 0 ≤ K)
    (hgK : ∀ t, ‖g t‖ ≤ K) : LipschitzWith (Real.toNNReal (3 * K)) u := by
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1)), by positivity, by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  have hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    simpa [φ] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hx := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hu x
  have hy := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hu y
  refine le_of_tendsto (hx.dist hy) (Filter.Eventually.of_forall fun n => ?_)
  exact (mollify_slopeBound (φ n) hu hg hK hgK).dist_le_mul x y

end Mollify

theorem column_slopeBound {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (j : Fin 3) :
    LipschitzWith (Real.toNNReal (3 * D)) (fun y => fderiv ℝ (W σ) y (unitVector j)) := by
  have hs : ContDiff ℝ 1 (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hc : Continuous (fun y => fderiv ℝ (W σ) y (unitVector j)) :=
    (hs.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hD0 : 0 ≤ D := by
    have h := le_trans (norm_nonneg _) (hW.decay 0 0).1
    simpa using h
  refine slopeBound_of_weakGradient hc (hW.secondDeriv_weak σ j) hD0 fun y => ?_
  refine (ContinuousLinearMap.le_opNorm _ (unitVector j)).trans ?_
  have h1 : ‖unitVector j‖ = 1 := by simp [unitVector]
  rw [ContinuousLinearMap.opNorm_flip, h1, mul_one]
  refine (hW.decay σ y).2.2.trans (div_le_self hD0 ?_)
  exact one_le_pow₀ (by linarith [norm_nonneg y])

theorem fderiv_slopeBound {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) :
    LipschitzWith (Real.toNNReal (3 * (3 * D))) (fderiv ℝ (W σ)) := by
  have hD0 : 0 ≤ D := by
    have h := le_trans (norm_nonneg _) (hW.decay 0 0).1
    simpa using h
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have hxy : 0 ≤ 3 * D * dist x y := by positivity
  refine (opNorm_le_of_columns _ hxy fun j => ?_).trans (le_of_eq (by ring))
  have := (column_slopeBound hW σ j).dist_le_mul x y
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm] at this
  simpa using this

end Internal.WeakGradientSlope

end CoerciveWeak

end Breakdown
