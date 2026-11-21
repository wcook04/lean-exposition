import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

namespace Internal

private lemma hasDerivAt_neg_inv_pow_add_sqrt (a C ρ : ℝ) (ha : 0 ≤ a) (hρ : 0 < ρ) :
    HasDerivAt (fun r : ℝ => -(C / 2) * ((a + Real.sqrt r) ^ 4)⁻¹)
      (C / ((a + Real.sqrt ρ) ^ 5 * Real.sqrt ρ)) ρ := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hpos : 0 < a + Real.sqrt ρ := by linarith
  have h1 : HasDerivAt (fun r : ℝ => a + Real.sqrt r) (1 / (2 * Real.sqrt ρ)) ρ :=
    (Real.hasDerivAt_sqrt hρ.ne').const_add a
  have h2 := (h1.pow 4).inv (pow_ne_zero 4 hpos.ne')
  have h3 := h2.const_mul (-(C / 2))
  refine h3.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [show (4 : ℕ) - 1 = 3 from rfl]
  field_simp
  ring

private lemma integral_Ioi_inv_pow_add_sqrt (a C τ : ℝ) (ha : 0 ≤ a) (hτ : 0 < τ) (hC : 0 ≤ C) :
    IntegrableOn (fun ρ => C / ((a + Real.sqrt ρ) ^ 5 * Real.sqrt ρ)) (Ioi τ) ∧
      ∫ ρ in Ioi τ, C / ((a + Real.sqrt ρ) ^ 5 * Real.sqrt ρ) = C / 2 / (a + Real.sqrt τ) ^ 4 := by
  have hderiv : ∀ ρ ∈ Ici τ, HasDerivAt (fun r : ℝ => -(C / 2) * ((a + Real.sqrt r) ^ 4)⁻¹)
      (C / ((a + Real.sqrt ρ) ^ 5 * Real.sqrt ρ)) ρ :=
    fun ρ hρ => hasDerivAt_neg_inv_pow_add_sqrt a C ρ ha (lt_of_lt_of_le hτ hρ)
  have hnn : ∀ ρ ∈ Ioi τ, 0 ≤ C / ((a + Real.sqrt ρ) ^ 5 * Real.sqrt ρ) := fun ρ _ => by
    have : 0 ≤ a + Real.sqrt ρ := add_nonneg ha (Real.sqrt_nonneg ρ)
    positivity
  have hlim : Tendsto (fun r : ℝ => -(C / 2) * ((a + Real.sqrt r) ^ 4)⁻¹) atTop (nhds 0) := by
    have h1 : Tendsto (fun r : ℝ => a + Real.sqrt r) atTop atTop :=
      tendsto_atTop_add_const_left atTop a Real.tendsto_sqrt_atTop
    have h2 : Tendsto (fun r : ℝ => ((a + Real.sqrt r) ^ 4)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp h1)
    simpa using h2.const_mul (-(C / 2))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim]
  ring

end Internal

theorem lerayKernelBound_of_heatKernelBounds : HeatKernelBounds → LerayKernelBound := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    have h := (hC 1 one_pos 0).2.2 0 0 0
    simp only [norm_zero, Real.sqrt_one, zero_add, one_pow, div_one] at h
    exact (abs_nonneg _).trans h
  refine ⟨2 * C, fun i j k τ x hτ => ?_⟩
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hpos : 0 < ‖x‖ + Real.sqrt τ := by linarith [norm_nonneg x]
  have hfirst : |(if i = j then -(x k / (2 * τ)) * heatKernel τ x else 0)| ≤
      C / (‖x‖ + Real.sqrt τ) ^ 4 := by
    split_ifs
    · rw [neg_mul, abs_neg]
      exact (hC τ hτ x).2.1 k
    · rw [abs_zero]
      positivity
  obtain ⟨hint, hval⟩ :=
    Internal.integral_Ioi_inv_pow_add_sqrt ‖x‖ C τ (norm_nonneg x) hτ hC0
  have hsecond : |∫ ρ in Ioi τ, heatKernelThird i j k ρ x| ≤ C / 2 / (‖x‖ + Real.sqrt τ) ^ 4 := by
    rw [← Real.norm_eq_abs, ← hval]
    refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
    intro ρ hρ
    have hρ0 : 0 < ρ := lt_trans hτ hρ
    have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
    have hq : 0 < ‖x‖ + Real.sqrt ρ := by linarith [norm_nonneg x]
    rw [Real.norm_eq_abs]
    refine ((hC ρ hρ0 x).2.2 i j k).trans (div_le_div_of_nonneg_left hC0 (by positivity) ?_)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) (by positivity)
  have hhalf : 0 ≤ C / 2 / (‖x‖ + Real.sqrt τ) ^ 4 := by positivity
  have hsplit : 2 * C / (‖x‖ + Real.sqrt τ) ^ 4 =
      C / (‖x‖ + Real.sqrt τ) ^ 4 + C / 2 / (‖x‖ + Real.sqrt τ) ^ 4 +
        C / 2 / (‖x‖ + Real.sqrt τ) ^ 4 := by ring
  unfold lerayKernel
  rw [hsplit]
  linarith [abs_add_le (if i = j then -(x k / (2 * τ)) * heatKernel τ x else 0)
    (∫ ρ in Ioi τ, heatKernelThird i j k ρ x)]

end Breakdown.FarField
