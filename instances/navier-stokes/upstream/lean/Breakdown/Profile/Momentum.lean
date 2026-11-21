import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma gradientAt_const_mul (c : ℝ) (g : Space → ℝ) (hg : ContDiff ℝ ∞ g) (x : Space) :
    gradientAt (fun y => c * g y) x = c • gradientAt g x := by
  have hd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  unfold gradientAt
  rw [fderiv_const_mul hd c, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_apply, smul_eq_mul, mul_smul]

theorem physicalMomentum_holds (htime : PhysicalTimeDeriv) (hcalc : DilateCalculus)
    (hgrad : GradientScale) : PhysicalMomentum := by
  intro W q C h s₀ t ht x
  refine (htime W h.smooth s₀ t ht x).congr_deriv ?_
  have hres := h.residual (physicalTime s₀ t) (physicalScale t • x)
  unfold SimilarityResidual at hres
  have hsim : deriv (fun σ => W σ (physicalScale t • x)) (physicalTime s₀ t)
        + (1 / 2 : ℝ) • W (physicalTime s₀ t) (physicalScale t • x)
        + (1 / 2 : ℝ) • fderiv ℝ (W (physicalTime s₀ t)) (physicalScale t • x)
            (physicalScale t • x)
      = sumSecondPartialsAt (W (physicalTime s₀ t)) (physicalScale t • x)
        - advectionAt (W (physicalTime s₀ t)) (physicalScale t • x)
        - gradientAt (q (physicalTime s₀ t)) (physicalScale t • x) := by
    rw [← sub_eq_zero, ← hres]
    abel
  rw [hsim]
  have hWs : ContDiff ℝ ∞ (W (physicalTime s₀ t)) :=
    h.smooth.comp (contDiff_prodMk_right (physicalTime s₀ t))
  have hqs : ContDiff ℝ ∞ (q (physicalTime s₀ t)) :=
    h.smooth_pressure.comp (contDiff_prodMk_right (physicalTime s₀ t))
  obtain ⟨-, hssp, hadv⟩ := hcalc ((1 - t)⁻¹) (W (physicalTime s₀ t)) hWs x
  have hpres : physicalPressure q s₀ t =
      fun y => physicalScale t ^ 2 * (fun z => q (physicalTime s₀ t) (physicalScale t • z)) y := by
    funext y
    have hnn : (0 : ℝ) ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith)
    simp only [physicalPressure, physicalScale, Real.sq_sqrt hnn]
  have hqc : ContDiff ℝ ∞ (fun z => q (physicalTime s₀ t) (physicalScale t • z)) :=
    hqs.comp (contDiff_const_smul (physicalScale t))
  have hfield : physicalField W s₀ t = dilateField ((1 - t)⁻¹) (W (physicalTime s₀ t)) := rfl
  rw [hfield, hssp, hadv, hpres, gradientAt_const_mul _ _ hqc x,
    hgrad (physicalScale t) (q (physicalTime s₀ t)) hqs x]
  change physicalScale t ^ 3 • _ = physicalScale t ^ 3 • _ - physicalScale t ^ 3 • _ - _
  rw [smul_smul, smul_sub, smul_sub]
  congr 2

end Breakdown
