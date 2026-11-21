import Breakdown.Frac.StSymbol

open MeasureTheory Real
open scoped ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace Breakdown

namespace FracInternal

open Freq

theorem norm_complexifyVec_eq (z : Space) : ‖complexifyVec z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [complexifyVec]

def complexifyIsom : Space →ₗᵢ[ℝ] CSpace :=
  ⟨complexifyVec.toLinearMap, norm_complexifyVec_eq⟩

theorem complexifyIsom_apply (z : Space) : complexifyIsom z = complexifyVec z := rfl

theorem continuous_remainder (φ : SchwartzMap Space Space) :
    Continuous (fun p : Space × Space => secondOrderRemainder φ p.1 p.2) := by
  have h1 : Continuous (fun x => fderiv ℝ φ x) := (φ.smooth 1).continuous_fderiv (by simp)
  have h2 : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
    (φ.smooth 2).continuous_iteratedFDeriv le_rfl
  unfold secondOrderRemainder
  fun_prop

theorem integrable_product (α : ℝ) (φ : SchwartzMap Space Space) (ξ : Space)
    (h : Integrable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ p.1 p.2‖)
      (volume.prod volume)) :
    Integrable (Function.uncurry fun (x z : Space) =>
      Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) •
        (‖z‖ ^ (-(3 + 2 * α)) • complexifyVec (secondOrderRemainder φ x z)))
      (volume.prod volume) := by
  refine h.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hE : Continuous (fun p : Space × Space => Complex.exp (↑(-2 * π * ⟪p.1, ξ⟫) * Complex.I)) := by
      fun_prop
    have hK : Measurable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α))) :=
      (measurable_norm.comp measurable_snd).pow_const _
    have hR : Continuous (fun p : Space × Space => complexifyVec (secondOrderRemainder φ p.1 p.2)) :=
      complexifyVec.continuous.comp (continuous_remainder φ)
    exact hE.aestronglyMeasurable.smul (hK.aestronglyMeasurable.smul hR.aestronglyMeasurable)
  · obtain ⟨x, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [norm_smul, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_complexifyVec_eq,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem inner_step (h1 : RemainderTransformStatement) (α : ℝ) (φ : SchwartzMap Space Space)
    (ξ z : Space) :
    ∫ x : Space, Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) •
        (‖z‖ ^ (-(3 + 2 * α)) • complexifyVec (secondOrderRemainder φ x z)) =
      symbolIntegrand α ξ z • 𝓕 (fun x => complexifyVec (φ x)) ξ := by
  simp_rw [smul_comm (Complex.exp _) (‖z‖ ^ (-(3 + 2 * α)) : ℝ)]
  rw [integral_smul, ← Real.fourier_eq', h1 φ z ξ, symbolIntegrand, ← phaseRemainder,
    ← Complex.coe_smul, smul_smul]

end FracInternal

open FracInternal Freq

theorem symbolExchange_of (h1 : RemainderTransformStatement) (h2 : RemainderProductIntegrableStatement) :
    SymbolExchangeStatement := by
  intro α hα hα' φ ξ
  have hI := integrable_product α φ ξ (h2 α hα hα' φ)
  rw [Real.fourier_eq']
  have hA : ∀ x : Space, Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) •
      complexifyVec (fractionalPowerAt α φ x) =
      (fractionalNormalizer α)⁻¹ • ∫ z : Space, Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * Complex.I) •
        (‖z‖ ^ (-(3 + 2 * α)) • complexifyVec (secondOrderRemainder φ x z)) := by
    intro x
    rw [fractionalPowerAt, map_smul, ← complexifyIsom_apply, ← LinearIsometry.integral_comp_comm,
      integral_smul, smul_comm]
    simp_rw [LinearIsometry.map_smul, complexifyIsom_apply]
  simp_rw [hA]
  rw [integral_smul, integral_integral_swap hI]
  simp_rw [inner_step h1]
  rw [integral_smul_const, Complex.coe_smul]

end Breakdown
