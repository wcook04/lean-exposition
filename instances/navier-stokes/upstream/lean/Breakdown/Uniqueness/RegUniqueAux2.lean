import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem divFreeC_sub (ξ : Space) (z w : CSpace) : divFreeC ξ z - divFreeC ξ w = divFreeC ξ (z - w) := by
  simp only [divFreeC, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_smul]
  abel

private theorem sum_eq_inner (ξ : Space) (z : CSpace) :
    (∑ i, ((ξ i : ℝ) : ℂ) * z i) = inner ℂ (freqVec ξ) z := by
  simp [PiLp.inner_apply, freqVec, complexifyVec, mul_comm]

private theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec, complexifyVec, Complex.norm_real]

theorem norm_divFreeC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ ≤ 2 * ‖z‖ := by
  unfold divFreeC
  rw [sum_eq_inner]
  have hin := norm_inner_le_norm (𝕜 := ℂ) (freqVec ξ) z
  rw [norm_freqVec] at hin
  have key : ‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) z) • freqVec ξ‖ ≤ ‖z‖ := by
    rw [norm_smul, norm_mul, norm_freqVec, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | hpos
    · rw [← h0]; simp
    · calc (‖ξ‖ ^ 2)⁻¹ * ‖inner ℂ (freqVec ξ) z‖ * ‖ξ‖ ≤ (‖ξ‖ ^ 2)⁻¹ * (‖ξ‖ * ‖z‖) * ‖ξ‖ := by
            gcongr
        _ = ‖z‖ := by field_simp
  calc _ ≤ ‖z‖ + _ := norm_sub_le _ _
    _ ≤ ‖z‖ + ‖z‖ := by gcongr
    _ = 2 * ‖z‖ := by ring

private theorem integral_exp_neg {k h : ℝ} (hk : 0 < k) :
    ∫ u in (0 : ℝ)..h, Real.exp ((-k) * u) = (1 - Real.exp (-(k * h))) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by linarith : (-k) ≠ 0),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring_nf

theorem heatSymbol_integral_le {T t : ℝ} (hTt : T ≤ t) (ξ : Space) :
    (1 + ‖ξ‖) * ∫ s in T..t, heatSymbol (t - s) ξ ≤ (t - T) + Real.sqrt (t - T) := by
  have hsub : ∫ s in T..t, heatSymbol (t - s) ξ = ∫ u in (0 : ℝ)..(t - T), heatSymbol u ξ := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => heatSymbol u ξ) t]
    simp
  rw [hsub]
  set h := t - T with hh
  have h0 : 0 ≤ h := by rw [hh]; linarith
  set x := ‖ξ‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  rcases eq_or_lt_of_le hx0 with hxz | hxp
  · have : ∀ u, heatSymbol u ξ = 1 := fun u => by simp [heatSymbol, ← hx, ← hxz]
    simp only [this, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [← hxz]
    have := Real.sqrt_nonneg h
    linarith
  · set k := 4 * π ^ 2 * x ^ 2 with hk
    have hkp : 0 < k := by positivity
    have hform : ∀ u, heatSymbol u ξ = Real.exp ((-k) * u) := fun u => by
      simp only [heatSymbol, hk, ← hx]; ring_nf
    simp only [hform]
    rw [integral_exp_neg hkp]
    set I := (1 - Real.exp (-(k * h))) / k with hI
    have hI1 : I ≤ h := by
      rw [hI, div_le_iff₀ hkp]
      have := Real.add_one_le_exp (-(k * h))
      linarith
    have hI2 : I ≤ 1 / k := by
      rw [hI]
      gcongr
      have := Real.exp_pos (-(k * h))
      linarith
    have hIx : x * I ≤ Real.sqrt h := by
      have hs0 := Real.sqrt_nonneg h
      have hss : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt h0
      rcases le_or_gt (x * Real.sqrt h) 1 with hc | hc
      · calc x * I ≤ x * h := by gcongr
          _ = (x * Real.sqrt h) * Real.sqrt h := by rw [mul_assoc, hss]
          _ ≤ 1 * Real.sqrt h := by gcongr
          _ = Real.sqrt h := one_mul _
      · have hpi : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
        calc x * I ≤ x * (1 / k) := by gcongr
          _ = 1 / (4 * π ^ 2 * x) := by rw [hk]; field_simp
          _ ≤ Real.sqrt h := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
    nlinarith

theorem heatSymbol_nonneg (t : ℝ) (ξ : Space) : 0 ≤ heatSymbol t ξ := Real.exp_nonneg _

theorem continuous_heatSymbol_sub (t : ℝ) (ξ : Space) :
    Continuous (fun s => heatSymbol (t - s) ξ) := by
  unfold heatSymbol; fun_prop

theorem hsNormSq_zero_le_three (f : Space → CSpace) : hsNormSq 0 f ≤ hsNormSq 3 f := by
  refine lintegral_mono fun ξ => ?_
  gcongr
  simp only [hsWeight, pow_zero]
  exact one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _))

theorem homNormSq_one_le_three (f : Space → CSpace) : homNormSq 1 f ≤ hsNormSq 3 f := by
  refine lintegral_mono fun ξ => ?_
  gcongr
  simp only [hsWeight, mul_one]
  exact (le_add_of_nonneg_left zero_le_one).trans
    (le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num))

theorem freqL1Norm_le_weighted (f : Space → CSpace) :
    freqL1Norm f ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 1) * ‖f ξ‖ₑ := by
  refine lintegral_mono fun ξ => ?_
  refine le_mul_of_one_le_left bot_le ?_
  rw [ENNReal.one_le_ofReal, pow_one]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem gradFreqL1Norm_le_weighted (f : Space → CSpace) :
    gradFreqL1Norm f ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 1) * ‖f ξ‖ₑ := by
  refine lintegral_mono fun ξ => ?_
  gcongr
  rw [pow_one]
  exact le_add_of_nonneg_left zero_le_one

theorem hsNormSq_add_le_two_mul (m : ℕ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    hsNormSq m (f + g) ≤ 2 * (hsNormSq m f + hsNormSq m g) := by
  have hw : Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight m ξ)) := by
    unfold hsWeight; fun_prop
  have hmeas : AEMeasurable (fun ξ => ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) volume :=
    hw.aemeasurable.mul (hf.enorm.pow_const 2)
  unfold hsNormSq
  rw [← lintegral_add_left' hmeas, ← lintegral_const_mul' 2 _ (by simp)]
  refine lintegral_mono fun ξ => ?_
  have h1 : ‖(f + g) ξ‖ₑ ^ 2 ≤ 2 * (‖f ξ‖ₑ ^ 2 + ‖g ξ‖ₑ ^ 2) := by
    have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖f ξ‖ₑ ‖g ξ‖ₑ (p := 2) (by norm_num)
    have h3 : ‖(f + g) ξ‖ₑ ≤ ‖f ξ‖ₑ + ‖g ξ‖ₑ := enorm_add_le _ _
    norm_num at h2
    calc ‖(f + g) ξ‖ₑ ^ 2 ≤ (‖f ξ‖ₑ + ‖g ξ‖ₑ) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * (‖f ξ‖ₑ ^ 2 + ‖g ξ‖ₑ ^ 2)) := by gcongr
    _ = _ := by ring

theorem hsCurve_bound {m : ℕ} {F : ℝ → Space → CSpace} {a b : ℝ} (hF : IsHsCurve m F a b) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ t ∈ Icc a b, hsNormSq m (F t) ≤ C := by
  have key : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ t ∈ Icc a b ∩ Icc a b, hsNormSq m (F t) ≤ C := by
    refine (isCompact_Icc (a := a) (b := b)).induction_on
      (p := fun U => ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ t ∈ U ∩ Icc a b, hsNormSq m (F t) ≤ C) ?_ ?_ ?_ ?_
    · exact ⟨0, by simp, by simp⟩
    · intro s u hsu ⟨C, hC, hb⟩
      exact ⟨C, hC, fun t ht => hb t ⟨hsu ht.1, ht.2⟩⟩
    · intro s u ⟨C, hC, hb⟩ ⟨D, hD, hd⟩
      refine ⟨max C D, by simp [hC, hD], fun t ht => ?_⟩
      rcases ht.1 with h1 | h1
      · exact (hb t ⟨h1, ht.2⟩).trans (le_max_left _ _)
      · exact (hd t ⟨h1, ht.2⟩).trans (le_max_right _ _)
    · intro x hx
      have hev : ∀ᶠ t in 𝓝[Icc a b] x, hsNormSq m (F t - F x) < 1 :=
        (tendsto_order.1 (hF.2 x hx)).2 1 one_pos
      refine ⟨_, hev, 2 * (1 + hsNormSq m (F x)), ?_, fun t ht => ?_⟩
      · have := (hF.1 x hx).2
        exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨by simp, this.ne⟩)
      · have hm : AEStronglyMeasurable (F t - F x) volume :=
          (hF.1 t ht.2).1.sub (hF.1 x hx).1
        have heq : F t = (F t - F x) + F x := by abel
        rw [heq]
        refine (hsNormSq_add_le_two_mul m hm).trans ?_
        gcongr
        exact (ht.1 : hsNormSq m (F t - F x) < 1).le
  obtain ⟨C, hC, hb⟩ := key
  exact ⟨C, hC, fun t ht => hb t ⟨ht, ht⟩⟩

end Breakdown.SmoothFlow
