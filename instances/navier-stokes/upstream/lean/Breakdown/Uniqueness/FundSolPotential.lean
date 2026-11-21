import Breakdown.Uniqueness.FundSolKernel

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

private lemma fderiv_potential_of_contDiff_one {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (x v : Space) :
    fderiv ℝ (potential g) x v = potential (fun y => fderiv ℝ g y v) x := by
  have h := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hg
    locallyIntegrable_kernel x
  have hex := (hc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) (hg.continuous_fderiv one_ne_zero)
    locallyIntegrable_kernel x
  unfold potential
  rw [h.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  rfl

private lemma fderiv_apply_const {f : Space → Space →L[ℝ] ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (v w : Space) :
    fderiv ℝ (fun y => f y v) x w = fderiv ℝ f x w v := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

private lemma hasCompactSupport_fderiv_apply {g : Space → ℝ} (hc : HasCompactSupport g)
    (v : Space) : HasCompactSupport (fun y => fderiv ℝ g y v) :=
  (hc.fderiv ℝ).comp_left (g := fun A : Space →L[ℝ] ℝ => A v) rfl

private lemma contDiff_fderiv_apply {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ g y v) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (potential g) :=
  hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hg locallyIntegrable_kernel

theorem fderiv_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (x v : Space) : fderiv ℝ (potential g) x v = potential (fun y => fderiv ℝ g y v) x :=
  fderiv_potential_of_contDiff_one (hg.of_le (WithTop.coe_le_coe.2 le_top)) hc x v

theorem secondPartial_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (i j : Fin 3) (x : Space) :
    secondPartial (potential g) i j x = potential (secondPartial g i j) x := by
  have hP := contDiff_potential hg hc
  have hdP : Differentiable ℝ (fderiv ℝ (potential g)) :=
    (hP.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hfun : (fun y => fderiv ℝ (potential g) y (unitVector j)) =
      potential (fun y => fderiv ℝ g y (unitVector j)) :=
    funext fun y => fderiv_potential hg hc y (unitVector j)
  have hsec : secondPartial g i j =
      fun y => fderiv ℝ (fun z => fderiv ℝ g z (unitVector j)) y (unitVector i) := by
    funext y
    rw [secondPartial, iteratedFDeriv_two_apply, fderiv_apply_const (hdg y)]
    simp
  rw [secondPartial, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← fderiv_apply_const (hdP x), hfun, hsec,
    fderiv_potential (contDiff_fderiv_apply hg _) (hasCompactSupport_fderiv_apply hc _)]

theorem potential_add {g h : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    potential (g + h) = potential g + potential h :=
  ConvolutionExists.add_distrib
    (hgc.convolutionExists_left _ hg.continuous locallyIntegrable_kernel)
    (hhc.convolutionExists_left _ hh.continuous locallyIntegrable_kernel)

theorem potential_smul (c : ℝ) (g : Space → ℝ) : potential (c • g) = c • potential g :=
  smul_convolution

end Breakdown.FundSol
