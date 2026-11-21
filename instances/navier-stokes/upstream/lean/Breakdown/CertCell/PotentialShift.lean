import Breakdown.CertCell.BridgeTraceStatements

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open SteadyCert CellCert.CellFormula

namespace Internal

theorem locallyIntegrable_of_square (q : Space → ℝ) (hm : AEStronglyMeasurable q volume)
    (hsq : IsLocalSquareIntegrable (fun y => q y ^ 2)) : LocallyIntegrable q volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h1 : IntegrableOn (fun _ : Space => (1 : ℝ)) K volume := (continuous_const.locallyIntegrable (μ := volume)).integrableOn_isCompact hK
  refine Integrable.mono' (h1.add (hsq K hK)) hm.restrict ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  show |q y| ≤ 1 + q y ^ 2
  nlinarith [abs_nonneg (q y), sq_abs (q y), sq_nonneg (|q y| - 1)]

theorem integral_directionalDeriv_eq_zero (φ : Space → ℝ) (hφ : IsTestScalar φ) (v : Space) :
    (∫ y, fderiv ℝ φ y v) = 0 := by
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hdcont : Continuous (fun y => fderiv ℝ φ y v) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsupp : HasCompactSupport (fun y => fderiv ℝ φ y v) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) v
  have hdint : Integrable (fun y => fderiv ℝ φ y v) volume :=
    hdcont.integrable_of_hasCompactSupport hdsupp
  have hφint : Integrable φ volume := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℝ)) (g := φ) (v := v)
    (by simp) (by simpa using hdint) (by simpa using hφint)
    (fun x _ => differentiableAt_const _) (fun x _ => hdiff x)
  simpa using key

end Internal

theorem potentialShift : PotentialShiftHolds := by
  intro Q q C hq
  obtain ⟨hm, hsq, hw⟩ := hq
  have hloc := Internal.locallyIntegrable_of_square q hm hsq
  refine ⟨hm.sub aestronglyMeasurable_const, ?_, ?_⟩
  · intro K hK
    have hqK : IntegrableOn q K volume := hloc.integrableOn_isCompact hK
    have h1 : IntegrableOn (fun _ : Space => (1 : ℝ)) K volume :=
      (continuous_const.locallyIntegrable (μ := volume)).integrableOn_isCompact hK
    have hexp : (fun y => (q y - C) ^ 2) = fun y => q y ^ 2 - 2 * C * q y + C ^ 2 * 1 := by
      funext y
      ring
    rw [hexp]
    exact ((hsq K hK).sub (hqK.const_mul (2 * C))).add (h1.const_mul (C ^ 2))
  · intro φ hφ j
    have hdcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)
    have hdint : Integrable (fun y => fderiv ℝ φ y (unitVector j)) volume :=
      hdcont.integrable_of_hasCompactSupport hdsupp
    have hint : Integrable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume :=
      hloc.integrable_smul_left_of_hasCompactSupport hdcont hdsupp
    have hsplit : (fun y => fderiv ℝ φ y (unitVector j) * (q y - C)) =
        fun y => fderiv ℝ φ y (unitVector j) * q y - C * fderiv ℝ φ y (unitVector j) := by
      funext y
      ring
    show (∫ y, fderiv ℝ φ y (unitVector j) * (q y - C)) = -∫ y, φ y * inner ℝ (Q y) (unitVector j)
    rw [hsplit, integral_sub hint (hdint.const_mul C), integral_const_mul,
      Internal.integral_directionalDeriv_eq_zero φ hφ (unitVector j), mul_zero, sub_zero]
    exact hw φ hφ j

end SideTrace

end CertCell

end Breakdown
