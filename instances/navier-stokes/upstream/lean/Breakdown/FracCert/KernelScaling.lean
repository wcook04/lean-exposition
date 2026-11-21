import Breakdown.FracCert.StKernel

open scoped ContDiff
open MeasureTheory Real Module

noncomputable section

namespace Breakdown.FracCert

private lemma symbol_scale {α t c : ℝ} (hc : 0 < c) (hc2 : c ^ (2 * α) = t) (i j k : Fin 3)
    (ξ : Space) :
    projDivSymbol α 1 i j k (c • ξ) = (c : ℂ) * projDivSymbol α t i j k ξ := by
  have hnorm : ‖c • ξ‖ = c * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hpow : (2 * π * (c * ‖ξ‖)) ^ (2 * α) = t * (2 * π * ‖ξ‖) ^ (2 * α) := by
    rw [show 2 * π * (c * ‖ξ‖) = c * (2 * π * ‖ξ‖) by ring,
      Real.mul_rpow hc.le (by positivity), hc2]
  have hfrac : (c • ξ) i * (c • ξ) j / (c * ‖ξ‖) ^ 2 = ξ i * ξ j / ‖ξ‖ ^ 2 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show c * ξ i * (c * ξ j) = c ^ 2 * (ξ i * ξ j) by ring, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]
  unfold projDivSymbol
  rw [hnorm, hpow, hfrac]
  simp only [PiLp.smul_apply, smul_eq_mul, one_mul]
  push_cast
  ring

private lemma symbol_neg (α t : ℝ) (i j k : Fin 3) (ξ : Space) :
    projDivSymbol α t i j k (-ξ) = (starRingEnd ℂ) (projDivSymbol α t i j k ξ) := by
  unfold projDivSymbol
  simp only [PiLp.neg_apply, norm_neg, neg_mul_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring

private lemma kernel_scale {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3) (x : Space) :
    projDivKernel α t i j k x =
      ((t ^ (-(2 / α)) : ℝ) : ℂ) * projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x) := by
  obtain ⟨c, hc⟩ : ∃ c, c = t ^ (1 / (2 * α)) := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ Real.rpow_pos_of_pos ht _
  have hc2 : c ^ (2 * α) = t := by
    rw [hc, ← Real.rpow_mul ht.le]
    have : 1 / (2 * α) * (2 * α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hs : t ^ (-(1 / (2 * α))) = c⁻¹ := by rw [Real.rpow_neg ht.le, hc]
  have hA : t ^ (-(2 / α)) = |(c ^ finrank ℝ Space)⁻¹| * c⁻¹ := by
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 (pow_pos hcpos _)), ← mul_inv,
      ← pow_succ, hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
    congr 1
    push_cast
    field_simp
    ring
  obtain ⟨G, hG⟩ : ∃ G : Space → ℂ, ∀ η, G η = ((c⁻¹ : ℝ) : ℂ) *
      (Complex.exp (↑(2 * π * inner ℝ η (c⁻¹ • x)) * Complex.I) * projDivSymbol α 1 i j k η) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ ξ : Space, Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I) •
      projDivSymbol α t i j k ξ = G (c • ξ) := by
    intro ξ
    rw [hG, symbol_scale hcpos hc2, real_inner_smul_left, real_inner_smul_right, ← mul_assoc c,
      mul_inv_cancel₀ hcpos.ne', one_mul, smul_eq_mul]
    have : ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hcpos.ne', Complex.ofReal_one]
    linear_combination (-Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I) *
      projDivSymbol α t i j k ξ) * this
  unfold projDivKernel
  rw [Real.fourierInv_eq', Real.fourierInv_eq', hs, integral_congr_ae (ae_of_all _ key),
    Measure.integral_comp_smul volume G c]
  simp_rw [hG]
  rw [integral_const_mul, hA, Complex.real_smul]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma kernel_real (α t : ℝ) (i j k : Fin 3) (x : Space) :
    (projDivKernel α t i j k x).im = 0 := by
  have h : (starRingEnd ℂ) (projDivKernel α t i j k x) = projDivKernel α t i j k x := by
    unfold projDivKernel
    rw [Real.fourierInv_eq', ← integral_conj]
    conv_rhs => rw [← integral_neg_eq_self]
    congr 1
    ext ξ
    rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, symbol_neg, inner_neg_left,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  exact Complex.conj_eq_iff_im.1 h

private lemma rpow_pow_three {t : ℝ} (ht : 0 < t) (a : ℝ) : (t ^ a) ^ (3 : ℕ) = t ^ (a * 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem kernelScaling_of (h1 : KernelDecayStatement) : KernelScalingStatement := by
  intro α hα i j k t ht
  obtain ⟨hsmooth, hdec⟩ := h1 α hα i j k
  obtain ⟨C, hC⟩ := hdec 0
  have hbound : ∀ x, ‖projDivKernel α 1 i j k x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
    intro x
    have := hC 1 one_pos x
    rwa [norm_iteratedFDeriv_zero, Real.one_rpow, Nat.cast_zero, add_zero] at this
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hbound 0)
    simpa using this
  have hcont : Continuous (projDivKernel α 1 i j k) := (hsmooth 1 one_pos).continuous
  have hint1 : Integrable (projDivKernel α 1 i j k) := by
    refine Integrable.mono' ((integrable_one_add_norm (E := Space) (μ := volume) (r := 4)
      (by simp; norm_num)).const_mul C) hcont.aestronglyMeasurable (ae_of_all _ hbound)
  have hp0 : (3 / 2 : ENNReal) ≠ 0 := (ENNReal.div_pos (by norm_num) (by norm_num)).ne'
  have hpt : (3 / 2 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hp : (3 / 2 : ENNReal).toReal = 3 / 2 := by
    rw [ENNReal.toReal_div]
    norm_num
  have hint1p : Integrable (fun x => ‖projDivKernel α 1 i j k x‖ ^ (3 / 2 : ℝ)) := by
    refine Integrable.mono' ((integrable_one_add_norm (E := Space) (μ := volume) (r := 6)
      (by simp; norm_num)).const_mul (C ^ (3 / 2 : ℝ)))
      (hcont.norm.rpow_const (fun _ => Or.inr (by norm_num))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖projDivKernel α 1 i j k x‖ ^ (3 / 2 : ℝ)
        ≤ (C * (1 + ‖x‖) ^ (-(4 : ℝ))) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) (hbound x) (by norm_num)
      _ = C ^ (3 / 2 : ℝ) * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
          rw [Real.mul_rpow hC0 (by positivity), ← Real.rpow_mul (by positivity)]
          norm_num
  have hmem1 : MemLp (projDivKernel α 1 i j k) (3 / 2) := by
    rw [← integrable_norm_rpow_iff hcont.aestronglyMeasurable hp0 hpt, hp]
    exact hint1p
  have hspos : 0 < t ^ (-(1 / (2 * α))) := Real.rpow_pos_of_pos ht _
  have hApos : 0 < t ^ (-(2 / α)) := Real.rpow_pos_of_pos ht _
  have hscale : projDivKernel α t i j k = fun x => ((t ^ (-(2 / α)) : ℝ) : ℂ) *
      projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x) :=
    funext (kernel_scale hα ht i j k)
  have hnorm : ∀ x, ‖projDivKernel α t i j k x‖ =
      t ^ (-(2 / α)) * ‖projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x)‖ := by
    intro x
    rw [hscale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
  have hint : Integrable (projDivKernel α t i j k) := by
    rw [hscale]
    exact (hint1.comp_smul hspos.ne').const_mul _
  have hnormp : ∀ x, ‖projDivKernel α t i j k x‖ ^ (3 / 2 : ℝ) =
      (t ^ (-(2 / α))) ^ (3 / 2 : ℝ) *
        ‖projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x)‖ ^ (3 / 2 : ℝ) := by
    intro x
    rw [hnorm, Real.mul_rpow hApos.le (norm_nonneg _)]
  have hmem : MemLp (projDivKernel α t i j k) (3 / 2) := by
    rw [← integrable_norm_rpow_iff hint.aestronglyMeasurable hp0 hpt, hp]
    simp_rw [hnormp]
    exact (hint1p.comp_smul hspos.ne').const_mul _
  have hs3 : ((t ^ (-(1 / (2 * α)))) ^ finrank ℝ Space)⁻¹ = t ^ (3 / (2 * α)) := by
    rw [finrank_euclideanSpace_fin, rpow_pow_three ht, ← Real.rpow_neg ht.le]
    congr 1
    ring
  refine ⟨kernel_scale hα ht i j k, kernel_real α t i j k, hint, ?_, hmem, ?_⟩
  · simp_rw [hnorm]
    rw [integral_const_mul, Measure.integral_comp_smul volume (fun y => ‖projDivKernel α 1 i j k y‖),
      smul_eq_mul, abs_of_pos (inv_pos.2 (pow_pos hspos _)), hs3, ← mul_assoc,
      ← Real.rpow_add ht]
    congr 2
    field_simp
    ring
  · rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 hpt,
      hmem1.eLpNorm_eq_integral_rpow_norm hp0 hpt, hp,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
    simp_rw [hnormp]
    rw [integral_const_mul,
      Measure.integral_comp_smul volume (fun y => ‖projDivKernel α 1 i j k y‖ ^ (3 / 2 : ℝ)),
      smul_eq_mul, abs_of_pos (inv_pos.2 (pow_pos hspos _)), hs3, ← mul_assoc,
      Real.mul_rpow (by positivity) (integral_nonneg fun _ => by positivity),
      ← Real.rpow_mul ht.le, ← Real.rpow_add ht, ← Real.rpow_mul ht.le]
    congr 2
    field_simp
    ring

end Breakdown.FracCert
