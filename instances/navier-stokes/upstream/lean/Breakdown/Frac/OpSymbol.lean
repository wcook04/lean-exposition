import Breakdown.Frac.StOperator

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace FracInternal

theorem symbolIntegrand_split (α : ℝ) (ξ z : Space) :
    symbolIntegrand α ξ z =
      ((‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ((2 * π) • ξ)) - 1
          + (inner ℝ z ((2 * π) • ξ)) ^ 2 / 2) : ℝ) : ℂ)
        + ((‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ((2 * π) • ξ))
          - inner ℝ z ((2 * π) • ξ)) : ℝ) : ℂ) * Complex.I := by
  have hi : inner ℝ z ((2 * π) • ξ) = 2 * π * inner ℝ z ξ := real_inner_smul_right _ _ _
  simp only [symbolIntegrand]
  rw [hi]
  push_cast
  rw [Complex.exp_mul_I]
  ring

theorem symbolIntegral_eq (h2 : SymbolScalarStatement) (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (ξ : Space) :
    ∫ z : Space, symbolIntegrand α ξ z =
      ((‖(2 * π) • ξ‖ ^ (2 * α) * fractionalNormalizer α : ℝ) : ℂ) := by
  obtain ⟨hfi, hfe, hgi, hge⟩ := h2 α hα1 hα2 ((2 * π) • ξ)
  rw [integral_congr_ae (Filter.Eventually.of_forall (symbolIntegrand_split α ξ))]
  rw [integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hfe, hge]
  · simp
  · exact hfi.ofReal
  · exact hgi.ofReal.mul_const Complex.I

end FracInternal

theorem symbol_of (h1 : SymbolExchangeStatement) (h2 : SymbolScalarStatement)
    (h3 : NormalizerStatement) : SymbolStatement := by
  intro α hα1 hα2 φ ξ
  have hM : fractionalNormalizer α ≠ 0 := (h3 α hα1 (by linarith)).2.ne'
  have hn : ‖(2 * π) • ξ‖ = 2 * π * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have key : (((fractionalNormalizer α)⁻¹ : ℝ) : ℂ) * ∫ z : Space, symbolIntegrand α ξ z =
      (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) := by
    rw [FracInternal.symbolIntegral_eq h2 α hα1 hα2 ξ, ← Complex.ofReal_mul, hn]
    congr 1
    rw [mul_comm ((2 * π * ‖ξ‖) ^ (2 * α)) _, inv_mul_cancel_left₀ hM]
  rw [h1 α hα1 hα2 φ ξ, smul_smul, key]

end Breakdown
