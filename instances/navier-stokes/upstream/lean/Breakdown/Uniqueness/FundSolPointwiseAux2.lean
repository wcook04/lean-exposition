import Breakdown.Uniqueness.FundSolPointwiseAux

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.FundSol.Internal

theorem potential_apply (g : Space → ℝ) (z : Space) :
    potential g z = ∫ t, g t * kernel (z - t) := by
  simp [potential, convolution_def, smul_eq_mul]

theorem abs_kernel (w : Space) : |kernel w| = (4 * π)⁻¹ * ‖w‖⁻¹ := by
  unfold kernel
  rw [neg_mul, abs_neg, abs_of_nonneg (by positivity)]

theorem abs_potential_le {g : Space → ℝ} {A ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ t, |g t| ≤ A)
    (hs : ∀ t, ρ < ‖t‖ → g t = 0) {z : Space} (hz : ‖z‖ ≤ ρ) :
    |potential g z| ≤ A * (4 * π)⁻¹ * ∫ w, ballPow 1 (3 * ρ) w := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  rw [potential_apply, ← integral_sub_left_eq_self (ballPow 1 (3 * ρ)) volume z,
    ← integral_const_mul, ← Real.norm_eq_abs]
  refine MeasureTheory.norm_integral_le_of_norm_le
    (((integrable_ballPow (n := 1) (by norm_num) _).comp_sub_left z).const_mul _) (Eventually.of_forall ?_)
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_kernel]
  by_cases ht : ρ < ‖t‖
  · rw [hs t ht, abs_zero, zero_mul]
    exact mul_nonneg (by positivity) (ballPow_nonneg _ _ _)
  · have h1 : ‖z - t‖ < 3 * ρ := by
      have := norm_sub_le z t
      have h0 : 0 ≤ ‖t‖ := norm_nonneg t
      linarith [not_lt.1 ht]
    rw [ballPow_of_lt h1, pow_one, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hA t) (by positivity))
      (by positivity)

theorem smooth_dir {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (contDiff_infty_iff_fderiv.1 hh).2.clm_apply contDiff_const

theorem differentiable_of_smooth {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) : Differentiable ℝ h :=
  (contDiff_infty_iff_fderiv.1 hh).1

theorem secondPartial_eq_dir {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (a b : Fin 3) (y : Space) :
    secondPartial h a b y =
      fderiv ℝ (fun y => fderiv ℝ h y (unitVector b)) y (unitVector a) := by
  have hd : Differentiable ℝ (fderiv ℝ h) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hh).2).1
  unfold secondPartial
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply (hd y) (differentiableAt_const _)]
  simp

theorem fderiv_reflect {φ : Space → ℝ} (hφ : Differentiable ℝ φ) (x₀ y v : Space) :
    fderiv ℝ (fun y => φ (x₀ - y)) y v = -(fderiv ℝ φ (x₀ - y) v) := by
  have h : HasFDerivAt (fun y => φ (x₀ - y))
      ((fderiv ℝ φ (x₀ - y)).comp (-ContinuousLinearMap.id ℝ Space)) y :=
    (hφ (x₀ - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x₀)
  rw [h.fderiv]
  simp

theorem integrable_mul_of_cpt {u w : Space → ℝ} (hu : Continuous u) (hw : Continuous w)
    (h : HasCompactSupport u ∨ HasCompactSupport w) : Integrable (fun y => u y * w y) :=
  (hu.mul hw).integrable_of_hasCompactSupport (h.elim (fun h => h.mul_right) (fun h => h.mul_left))

theorem integral_secondPartial_mul {f K : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hK : ContDiff ℝ ∞ K) (x₀ : Space) (i j : Fin 3) :
    ∫ y, secondPartial f i j y * K (x₀ - y) = ∫ y, f y * secondPartial K j i (x₀ - y) := by
  set g : Space → ℝ := fun y => K (x₀ - y) with hg
  have hgs : ContDiff ℝ ∞ g := hK.comp (contDiff_const.sub contDiff_id)
  set Fj : Space → ℝ := fun y => fderiv ℝ f y (unitVector j) with hFj
  set Gi : Space → ℝ := fun y => fderiv ℝ g y (unitVector i) with hGi
  have hFjs : ContDiff ℝ ∞ Fj := smooth_dir hf _
  have hGis : ContDiff ℝ ∞ Gi := smooth_dir hgs _
  have hFjc : HasCompactSupport Fj := hc.fderiv_apply (𝕜 := ℝ) _
  have hFjic : HasCompactSupport (fun y => fderiv ℝ Fj y (unitVector i)) :=
    hFjc.fderiv_apply (𝕜 := ℝ) _
  have s1 : ∫ y, secondPartial f i j y * g y = -∫ y, Gi y * Fj y := by
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := Fj)
      (v := unitVector i)
      (integrable_mul_of_cpt (smooth_dir hgs _).continuous hFjs.continuous (Or.inr hFjc))
      (integrable_mul_of_cpt hgs.continuous (smooth_dir hFjs _).continuous (Or.inr hFjic))
      (integrable_mul_of_cpt hgs.continuous hFjs.continuous (Or.inr hFjc))
      (fun x _ => differentiable_of_smooth hgs x) (fun x _ => differentiable_of_smooth hFjs x)
    rw [← this]
    congr 1; ext y
    rw [secondPartial_eq_dir hf, mul_comm]
  have s2 : ∫ y, Gi y * Fj y = -∫ y, fderiv ℝ Gi y (unitVector j) * f y :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := Gi) (g := f)
      (v := unitVector j)
      (integrable_mul_of_cpt (smooth_dir hGis _).continuous hf.continuous (Or.inr hc))
      (integrable_mul_of_cpt hGis.continuous hFjs.continuous (Or.inr hFjc))
      (integrable_mul_of_cpt hGis.continuous hf.continuous (Or.inr hc))
      (fun x _ => differentiable_of_smooth hGis x) (fun x _ => differentiable_of_smooth hf x)
  have hKd : Differentiable ℝ K := differentiable_of_smooth hK
  have hGi' : Gi = fun y => -(fderiv ℝ K (x₀ - y) (unitVector i)) := by
    ext y; exact fderiv_reflect hKd x₀ y _
  have s3 : ∀ y, fderiv ℝ Gi y (unitVector j) = secondPartial K j i (x₀ - y) := by
    intro y
    rw [hGi', fderiv_fun_neg, ContinuousLinearMap.neg_apply,
      fderiv_reflect (differentiable_of_smooth (smooth_dir hK _)) x₀ y, neg_neg,
      secondPartial_eq_dir hK]
  change ∫ y, secondPartial f i j y * g y = _
  rw [s1, s2, neg_neg]
  congr 1; ext y
  rw [s3, mul_comm]

theorem secondPartial_congr {h₁ h₂ : Space → ℝ} {z : Space} (h : h₁ =ᶠ[𝓝 z] h₂) (a b : Fin 3) :
    secondPartial h₁ a b z = secondPartial h₂ a b z := by
  unfold secondPartial
  rw [(h.iteratedFDeriv ℝ 2).eq_of_nhds]

theorem abs_secondPartial_le (h : Space → ℝ) (a b : Fin 3) (z : Space) :
    |secondPartial h a b z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ := by
  unfold secondPartial
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [unitVector, Fin.prod_univ_two]

end Breakdown.FundSol.Internal
