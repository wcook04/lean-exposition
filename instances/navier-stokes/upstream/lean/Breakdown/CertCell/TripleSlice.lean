import Breakdown.CertCell.SixthPowerStatements

open MeasureTheory

noncomputable section

namespace Breakdown

private lemma lintegral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ^ ((1 : ℝ) / 2) * g a ^ ((1 : ℝ) / 2) ∂μ ≤
      (∫⁻ a, f a ∂μ) ^ ((1 : ℝ) / 2) * (∫⁻ a, g a ∂μ) ^ ((1 : ℝ) / 2) := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hf.pow_const ((1 : ℝ) / 2)) (hg.pow_const ((1 : ℝ) / 2))
  have e : ∀ x : ENNReal, (x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  simp only [Pi.mul_apply, e] at key
  exact key

theorem tripleSliceBound : TripleSliceBound := by
  intro f₁ f₂ f₃ h₁ h₂ h₃
  have hsplit : ∀ x y z : ℝ, (f₁ (y, z) * f₂ (x, z) * f₃ (x, y)) ^ ((1 : ℝ) / 2) =
      f₁ (y, z) ^ ((1 : ℝ) / 2) * (f₂ (x, z) ^ ((1 : ℝ) / 2) * f₃ (x, y) ^ ((1 : ℝ) / 2)) := by
    intro x y z
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      mul_assoc]
  simp_rw [hsplit]
  have hH : Measurable fun q : (ℝ × ℝ) × ℝ =>
      f₁ (q.1.2, q.2) ^ ((1 : ℝ) / 2) * (f₂ (q.1.1, q.2) ^ ((1 : ℝ) / 2) *
        f₃ (q.1.1, q.1.2) ^ ((1 : ℝ) / 2)) := by fun_prop
  have hF₂ : Measurable fun z : ℝ => ∫⁻ x, f₂ (x, z) := h₂.lintegral_prod_left'
  have hF₃ : Measurable fun y : ℝ => ∫⁻ x, f₃ (x, y) := h₃.lintegral_prod_left'
  have hG : Measurable fun p : ℝ × ℝ => f₁ p ^ ((1 : ℝ) / 2) *
      ((∫⁻ x, f₃ (x, p.1)) * ∫⁻ x, f₂ (x, p.2)) ^ ((1 : ℝ) / 2) := by fun_prop
  calc ∫⁻ x, ∫⁻ y, ∫⁻ z, f₁ (y, z) ^ ((1 : ℝ) / 2) *
          (f₂ (x, z) ^ ((1 : ℝ) / 2) * f₃ (x, y) ^ ((1 : ℝ) / 2))
      = ∫⁻ y, ∫⁻ x, ∫⁻ z, f₁ (y, z) ^ ((1 : ℝ) / 2) *
          (f₂ (x, z) ^ ((1 : ℝ) / 2) * f₃ (x, y) ^ ((1 : ℝ) / 2)) :=
        lintegral_lintegral_swap (hH.lintegral_prod_right').aemeasurable
    _ = ∫⁻ y, ∫⁻ z, ∫⁻ x, f₁ (y, z) ^ ((1 : ℝ) / 2) *
          (f₂ (x, z) ^ ((1 : ℝ) / 2) * f₃ (x, y) ^ ((1 : ℝ) / 2)) := by
        refine lintegral_congr fun y => lintegral_lintegral_swap ?_
        exact (hH.comp (by fun_prop : Measurable fun p : ℝ × ℝ => ((p.1, y), p.2))).aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ z, f₁ (y, z) ^ ((1 : ℝ) / 2) *
          ((∫⁻ x, f₃ (x, y)) * ∫⁻ x, f₂ (x, z)) ^ ((1 : ℝ) / 2) := by
        refine lintegral_mono fun y => lintegral_mono fun z => ?_
        rw [lintegral_const_mul _ (by fun_prop), mul_comm (∫⁻ x, f₃ (x, y)),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        gcongr
        exact lintegral_sqrt_mul_sqrt_le volume (by fun_prop) (by fun_prop)
    _ = ∫⁻ p : ℝ × ℝ, f₁ p ^ ((1 : ℝ) / 2) *
          ((∫⁻ x, f₃ (x, p.1)) * ∫⁻ x, f₂ (x, p.2)) ^ ((1 : ℝ) / 2) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hG.aemeasurable]
    _ ≤ (∫⁻ p, f₁ p) ^ ((1 : ℝ) / 2) *
          (∫⁻ p : ℝ × ℝ, (∫⁻ x, f₃ (x, p.1)) * ∫⁻ x, f₂ (x, p.2)) ^ ((1 : ℝ) / 2) :=
        lintegral_sqrt_mul_sqrt_le volume h₁.aemeasurable (by fun_prop)
    _ = (∫⁻ p, f₁ p) ^ ((1 : ℝ) / 2) * ((∫⁻ p, f₃ p) * ∫⁻ p, f₂ p) ^ ((1 : ℝ) / 2) := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul hF₃.aemeasurable hF₂.aemeasurable,
          lintegral_prod_symm' _ h₃, lintegral_prod_symm' _ h₂]
    _ = ((∫⁻ p, f₁ p) * (∫⁻ p, f₂ p) * (∫⁻ p, f₃ p)) ^ ((1 : ℝ) / 2) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_assoc, mul_comm (∫⁻ p, f₃ p)]

end Breakdown
