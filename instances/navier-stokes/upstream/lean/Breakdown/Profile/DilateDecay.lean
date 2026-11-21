import Breakdown.Profile.StatementsField

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma inv_shift_le {c t a : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    a / (1 + c * t) ≤ a * max 1 c⁻¹ / (1 + t) := by
  have hm1 : 1 ≤ max 1 c⁻¹ := le_max_left _ _
  have hmc : 1 ≤ max 1 c⁻¹ * c := by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
  have key : 1 + t ≤ max 1 c⁻¹ * (1 + c * t) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key ha]

private lemma inv_shift_sq_le {c t a : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    a / (1 + c * t) ^ 2 ≤ a * max 1 c⁻¹ ^ 2 / (1 + t) ^ 2 := by
  have hm1 : 1 ≤ max 1 c⁻¹ := le_max_left _ _
  have hmc : 1 ≤ max 1 c⁻¹ * c := by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
  have key : 1 + t ≤ max 1 c⁻¹ * (1 + c * t) := by nlinarith
  have key2 : (1 + t) ^ 2 ≤ max 1 c⁻¹ ^ 2 * (1 + c * t) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) key 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key2 ha]

theorem decayFieldDilate_holds (hcalc : DilateCalculus) : DecayFieldDilate := by
  intro μ f hμ hf
  obtain ⟨hsm, hdiv, Cf, hC⟩ := hf
  set c := Real.sqrt μ with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr hμ
  have hCf : 0 ≤ Cf := by
    have h0 := (hC 0).1
    simp only [norm_zero, add_zero, div_one] at h0
    exact (norm_nonneg _).trans h0
  have hfd : ∀ y, fderiv ℝ (dilateField μ f) y = c ^ 2 • fderiv ℝ f (c • y) :=
    fun y => (hcalc μ f hsm y).1
  have hnorm : ∀ y : Space, ‖c • y‖ = c * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
  refine ⟨?_, ?_, ?_⟩
  · exact (hsm.comp (contDiff_const_smul c)).const_smul c
  · intro y
    have h := hdiv (c • y)
    unfold divergenceAt at h ⊢
    simp only [hfd, FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h, mul_zero]
  · set m := max 1 c⁻¹
    refine ⟨c * Cf * m + c ^ 2 * Cf * m ^ 2, fun y => ⟨?_, ?_⟩⟩
    · have e1 : ‖dilateField μ f y‖ = c * ‖f (c • y)‖ := by
        simp only [dilateField, ← hcdef, norm_smul, Real.norm_of_nonneg hc.le]
      have b1 : ‖f (c • y)‖ ≤ Cf / (1 + c * ‖y‖) := by
        have := (hC (c • y)).1; rwa [hnorm] at this
      have b2 := inv_shift_le hc (norm_nonneg y) hCf
      have hm : 0 ≤ m := le_trans zero_le_one (le_max_left _ _)
      have hpos : 0 < 1 + ‖y‖ := by positivity
      rw [e1]
      calc c * ‖f (c • y)‖ ≤ c * (Cf * m / (1 + ‖y‖)) :=
            mul_le_mul_of_nonneg_left (b1.trans b2) hc.le
        _ = c * Cf * m / (1 + ‖y‖) := by ring
        _ ≤ (c * Cf * m + c ^ 2 * Cf * m ^ 2) / (1 + ‖y‖) := by
            apply div_le_div_of_nonneg_right _ hpos.le
            have : 0 ≤ c ^ 2 * Cf * m ^ 2 := by positivity
            linarith
    · have e1 : ‖fderiv ℝ (dilateField μ f) y‖ = c ^ 2 * ‖fderiv ℝ f (c • y)‖ := by
        rw [hfd, norm_smul, Real.norm_of_nonneg (by positivity)]
      have b1 : ‖fderiv ℝ f (c • y)‖ ≤ Cf / (1 + c * ‖y‖) ^ 2 := by
        have := (hC (c • y)).2; rwa [hnorm] at this
      have b2 := inv_shift_sq_le hc (norm_nonneg y) hCf
      have hm : 0 ≤ m := le_trans zero_le_one (le_max_left _ _)
      have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
      rw [e1]
      calc c ^ 2 * ‖fderiv ℝ f (c • y)‖ ≤ c ^ 2 * (Cf * m ^ 2 / (1 + ‖y‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (b1.trans b2) (by positivity)
        _ = c ^ 2 * Cf * m ^ 2 / (1 + ‖y‖) ^ 2 := by ring
        _ ≤ (c * Cf * m + c ^ 2 * Cf * m ^ 2) / (1 + ‖y‖) ^ 2 := by
            apply div_le_div_of_nonneg_right _ hpos.le
            have : 0 ≤ c * Cf * m := by positivity
            linarith

end Breakdown
