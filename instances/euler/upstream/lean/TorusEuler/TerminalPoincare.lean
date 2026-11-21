import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set

namespace TorusEuler

private theorem sq_intervalIntegral_le {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg_nonneg : ∀ x, 0 ≤ g x) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  let μ := volume.restrict (Ioc a b)
  have hg_int : Integrable g μ := (hg.intervalIntegrable_of_Icc hab).1
  have hg_sq_int : Integrable (fun x => g x ^ 2) μ :=
    ((hg.pow 2).intervalIntegrable_of_Icc hab).1
  have hg_lp : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg_int.aestronglyMeasurable).2 hg_sq_int
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := fun _ => (1 : ℝ)) (g := g) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => zero_le_one) (ae_of_all _ hg_nonneg)
    (by simpa only [ENNReal.ofReal_ofNat] using (memLp_const (μ := μ) (p := 2) (1 : ℝ)))
    (by simpa only [ENNReal.ofReal_ofNat] using hg_lp)
  simp only [one_mul, Real.rpow_two, one_pow, ← Real.sqrt_eq_rpow] at hholder
  have hlength : (∫ _ : ℝ, (1 : ℝ) ∂μ) = b - a := by
    rw [show (∫ _ : ℝ, (1 : ℝ) ∂μ) = (∫ _ in a..b, (1 : ℝ)) from
      (intervalIntegral.integral_of_le hab).symm]
    simp [intervalIntegral.integral_const]
  rw [hlength, ← Real.sqrt_mul (sub_nonneg.mpr hab)] at hholder
  have hle := pow_le_pow_left₀ (integral_nonneg hg_nonneg) hholder 2
  rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hab)
    (integral_nonneg fun _ => sq_nonneg _))] at hle
  simpa only [intervalIntegral.integral_of_le hab] using hle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The squared pointwise bound of (4.5) for a continuously differentiable path
vanishing at the terminal time. -/
theorem terminal_poincare_pointwise {T : ℝ} {f f' : ℝ → E} (hT : 0 ≤ T)
    (hterminal : f T = 0) (hderiv_cont : ContinuousOn f' (Icc 0 T))
    (hderiv : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖f t‖ ^ 2 ≤ (T - t) * ∫ s in (0 : ℝ)..T, ‖f' s‖ ^ 2 := by
  have hsub : Icc t T ⊆ Icc 0 T := Icc_subset_Icc ht.1 le_rfl
  have hf_cont : ContinuousOn f (Icc 0 T) :=
    fun s hs => (hderiv s hs).continuousWithinAt
  have hFTC : (∫ s in t..T, f' s) = f T - f t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2 (hf_cont.mono hsub)
    · intro s hs
      exact (hderiv s (hsub (Ioo_subset_Icc_self hs))).hasDerivAt
        (Icc_mem_nhds (ht.1.trans_lt hs.1) hs.2)
    · exact (hderiv_cont.mono hsub).intervalIntegrable_of_Icc ht.2
  have hnorm : ‖f t‖ ≤ ∫ s in t..T, ‖f' s‖ := by
    simpa [hFTC, hterminal] using
      (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f') ht.2)
  calc
    ‖f t‖ ^ 2 ≤ (∫ s in t..T, ‖f' s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (T - t) * ∫ s in t..T, ‖f' s‖ ^ 2 :=
      sq_intervalIntegral_le ht.2 (hderiv_cont.norm.mono hsub) (fun s => norm_nonneg _)
    _ ≤ (T - t) * ∫ s in (0 : ℝ)..T, ‖f' s‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval
        ht.1 ht.2 le_rfl (ae_of_all _ fun s => sq_nonneg ‖f' s‖)
        ((hderiv_cont.norm.pow 2).intervalIntegrable_of_Icc hT)) (sub_nonneg.mpr ht.2)

/-- The squared time-integrated bound of (4.5) with coefficient `T ^ 2 / 2`. -/
theorem terminal_poincare_integral {T : ℝ} {f f' : ℝ → E} (hT : 0 ≤ T)
    (hterminal : f T = 0) (hderiv_cont : ContinuousOn f' (Icc 0 T))
    (hderiv : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t) :
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      (T ^ 2 / 2) * ∫ s in (0 : ℝ)..T, ‖f' s‖ ^ 2 := by
  let energy := ∫ s in (0 : ℝ)..T, ‖f' s‖ ^ 2
  have hf_cont : ContinuousOn f (Icc 0 T) :=
    fun s hs => (hderiv s hs).continuousWithinAt
  have hbound_cont : Continuous (fun t => (T - t) * energy) :=
    (continuous_const.sub continuous_id).mul continuous_const
  calc
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤ ∫ t in (0 : ℝ)..T, (T - t) * energy :=
      intervalIntegral.integral_mono_on hT ((hf_cont.norm.pow 2).intervalIntegrable_of_Icc hT)
        (hbound_cont.intervalIntegrable 0 T)
        (fun t ht => terminal_poincare_pointwise hT hterminal hderiv_cont hderiv ht)
    _ = (T ^ 2 / 2) * energy := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_const, integral_id]
      simp only [sub_zero, smul_eq_mul, zero_pow (by decide : 2 ≠ 0)]
      ring

end TorusEuler
