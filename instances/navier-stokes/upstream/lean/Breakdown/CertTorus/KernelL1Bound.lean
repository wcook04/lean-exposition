import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace Internal.KernelL1

lemma integrable_bracket : Integrable (fun x : Space => (1 + ‖x‖) ^ (-(4 : ℝ))) := by
  apply integrable_one_add_norm
  rw [finrank_euclideanSpace_fin]
  norm_num

lemma bracket_smul_eq {s : ℝ} (hs : 0 < s) (x : Space) :
    (1 + ‖s⁻¹ • x‖) ^ (-(4 : ℝ)) = s ^ 4 / (‖x‖ + s) ^ 4 := by
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hpos : 0 < 1 + s⁻¹ * ‖x‖ := by positivity
  rw [Real.rpow_neg hpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : 1 + s⁻¹ * ‖x‖ = (‖x‖ + s) / s := by
    field_simp
    ring
  rw [h1, div_pow, inv_div]

lemma bound_eq {s : ℝ} (C : ℝ) (hs : 0 < s) (x : Space) :
    C / (‖x‖ + s) ^ 4 = C * (s ^ 4)⁻¹ * (1 + ‖s⁻¹ • x‖) ^ (-(4 : ℝ)) := by
  rw [bracket_smul_eq hs x]
  have : 0 < ‖x‖ + s := by positivity
  field_simp

lemma integrable_bound (C : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : Space => C / (‖x‖ + s) ^ 4) := by
  have h := (integrable_bracket.comp_smul (inv_ne_zero hs.ne')).const_mul (C * (s ^ 4)⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (bound_eq C hs x).symm

lemma integral_bound (C : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x : Space, C / (‖x‖ + s) ^ 4 =
      C * (∫ x : Space, (1 + ‖x‖) ^ (-(4 : ℝ))) * s⁻¹ := by
  simp_rw [bound_eq C hs]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume
      (fun x : Space => (1 + ‖x‖) ^ (-(4 : ℝ))) s, finrank_euclideanSpace_fin, smul_eq_mul,
      abs_of_pos (by positivity)]
  field_simp

end Internal.KernelL1

theorem kernelL1Bound_of_bound : LerayKernelBound → LerayKernelMeasurable → KernelL1Bound := by
  rintro ⟨C, hC⟩ hM
  refine ⟨C * ∫ x : Space, (1 + ‖x‖) ^ (-(4 : ℝ)), fun i j k τ hτ => ?_⟩
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hmeas : Measurable (lerayKernel i j k τ) :=
    (hM i j k).comp (measurable_const.prodMk measurable_id)
  have hint : Integrable (lerayKernel i j k τ) :=
    (Internal.KernelL1.integrable_bound C hs).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hC i j k τ x hτ)
  refine ⟨hint, ?_⟩
  calc ∫ x, |lerayKernel i j k τ x| ≤ ∫ x : Space, C / (‖x‖ + Real.sqrt τ) ^ 4 :=
        integral_mono hint.abs (Internal.KernelL1.integrable_bound C hs)
          fun x => hC i j k τ x hτ
    _ = C * (∫ x : Space, (1 + ‖x‖) ^ (-(4 : ℝ))) * (Real.sqrt τ)⁻¹ :=
        Internal.KernelL1.integral_bound C hs
    _ = C * (∫ x : Space, (1 + ‖x‖) ^ (-(4 : ℝ))) * τ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le]

end Breakdown.FarField
