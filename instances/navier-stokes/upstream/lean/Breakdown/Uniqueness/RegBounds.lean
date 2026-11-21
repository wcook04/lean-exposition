import Breakdown.Uniqueness.RegToolkit
import Breakdown.FreqTr.FreqTrL1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem norm_realVec_le (z : CSpace) : ‖realVec z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have h : ‖(realVec z) i‖ ≤ ‖z i‖ := by
    change ‖(z i).re‖ ≤ ‖z i‖
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem opNorm_realVec_le : ‖realVec‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by simpa using norm_realVec_le z)

private theorem hsWeight_mono {m n : ℕ} (h : m ≤ n) (ξ : Space) :
    hsWeight m ξ ≤ hsWeight n ξ :=
  pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg _)) h

private theorem hsNormSq_mono {m n : ℕ} (h : m ≤ n) (f : Space → CSpace) :
    hsNormSq m f ≤ hsNormSq n f :=
  lintegral_mono fun ξ => by
    gcongr
    exact hsWeight_mono h ξ

private theorem hsNormSq_zero_eq (f : Space → CSpace) :
    hsNormSq 0 f = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
  simp [hsNormSq, hsWeight]

private theorem freqL1Norm_lt_top {f : Space → CSpace} (hf : hsNormSq 2 f < ⊤) :
    freqL1Norm f < ⊤ := by
  obtain ⟨C, hC⟩ := freqL1Norm_le_hsNormSq
  exact (hC f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf.ne))

private theorem gradFreqL1Norm_le_weighted (f : Space → CSpace) :
    gradFreqL1Norm f ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 1) * ‖f ξ‖ₑ :=
  lintegral_mono fun ξ => by
    gcongr
    rw [pow_one]
    linarith [norm_nonneg ξ]

private theorem gradFreqL1Norm_lt_top {f : Space → CSpace} (hf : hsNormSq 3 f < ⊤) :
    gradFreqL1Norm f < ⊤ := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le 1
  exact ((gradFreqL1Norm_le_weighted f).trans (hC f)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (show hsNormSq (1 + 2) f < ⊤ from hf).ne))

private theorem integrable_of_freqL1Norm {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (h : freqL1Norm f < ⊤) : Integrable f volume :=
  ⟨hm, hasFiniteIntegral_iff_enorm.2 h⟩

private theorem lintegral_sq_eq (g : Space → CSpace) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 = eLpNorm g 2 volume ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  exact h.symm

private theorem memLp_two_of {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (h : hsNormSq 0 f < ⊤) : MemLp f 2 volume := by
  refine ⟨hm, ?_⟩
  rw [hsNormSq_zero_eq, lintegral_sq_eq] at h
  exact (ENNReal.pow_lt_top_iff.1 h).resolve_right two_ne_zero

theorem integral_sq_physField_le {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : hsNormSq 2 f < ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖physField f x‖ ^ 2) ≤ hsNormSq 0 f := by
  have h1 : MemLp f 1 volume :=
    memLp_one_iff_integrable.2 (integrable_of_freqL1Norm hm (freqL1Norm_lt_top hf))
  have h2 : MemLp f 2 volume := memLp_two_of hm ((hsNormSq_mono (by norm_num) f).trans_lt hf)
  have hae := Breakdown.Freq.freqTrL1L2.2 f h1 h2
  have hto : toLpOrZero 2 f = h2.toLp f := by simp [toLpOrZero, h2]
  have hnorm : eLpNorm (freqTrL2.symm (toLpOrZero 2 f) : Space → CSpace) 2 volume =
      eLpNorm f 2 volume := by
    have e1 : (eLpNorm (freqTrL2.symm (toLpOrZero 2 f) : Space → CSpace) 2 volume).toReal =
        (eLpNorm (toLpOrZero 2 f : Space → CSpace) 2 volume).toReal := by
      rw [← Lp.norm_def, ← Lp.norm_def]
      exact LinearIsometryEquiv.norm_map _ _
    rw [ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)] at e1
    rw [e1, hto]
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp h2)
  calc ∫⁻ x, ENNReal.ofReal (‖physField f x‖ ^ 2) ≤ ∫⁻ x, ‖𝓕⁻ f x‖ₑ ^ 2 :=
        lintegral_mono fun x => by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (norm_nonneg _) (norm_realVec_le _) 2)
    _ = ∫⁻ x, ‖(freqTrL2.symm (toLpOrZero 2 f) : Space → CSpace) x‖ₑ ^ 2 :=
        lintegral_congr_ae (hae.mono fun x hx => by dsimp only; rw [hx])
    _ = eLpNorm f 2 volume ^ 2 := by rw [lintegral_sq_eq, hnorm]
    _ = hsNormSq 0 f := by rw [hsNormSq_zero_eq, lintegral_sq_eq]

private theorem norm_freqTr_le_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : Space → E) (w : Space) : ‖𝓕 g w‖ ≤ ∫ v, ‖g v‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

theorem norm_physField_le {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : hsNormSq 3 f < ⊤) (x : Space) : ‖physField f x‖ ≤ (freqL1Norm f).toReal := by
  calc ‖physField f x‖ ≤ ‖𝓕⁻ f x‖ := norm_realVec_le _
    _ = ‖𝓕 f (-x)‖ := by rw [fourierInv_eq_fourier_neg]
    _ ≤ ∫ ξ, ‖f ξ‖ := norm_freqTr_le_integral f (-x)
    _ = (freqL1Norm f).toReal := by rw [freqL1Norm, integral_norm_eq_lintegral_enorm hm]

theorem norm_fderiv_physField_le {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : hsNormSq 3 f < ⊤) (x : Space) :
    ‖fderiv ℝ (physField f) x‖ ≤ 2 * π * (gradFreqL1Norm f).toReal := by
  have hw := freqL1Norm_lt_top ((hsNormSq_mono (by norm_num) f).trans_lt hf)
  have hg := gradFreqL1Norm_lt_top hf
  have hi : Integrable f volume := integrable_of_freqL1Norm hm hw
  have hmeas : AEStronglyMeasurable (fun v : Space => ‖v‖ * ‖f v‖) volume :=
    continuous_norm.aestronglyMeasurable.mul hm.norm
  have hlin : ∫⁻ v, ENNReal.ofReal (‖v‖ * ‖f v‖) = gradFreqL1Norm f := by
    unfold gradFreqL1Norm
    refine lintegral_congr fun v => ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [ofReal_norm]
  have hi' : Integrable (fun v : Space => ‖v‖ * ‖f v‖) volume := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v => by positivity), hlin]
    exact hg
  have hD := Real.hasFDerivAt_fourier hi hi' (-x)
  have hphys : physField f = fun y => realVec (𝓕 f (-y)) := by
    ext1 y
    simp only [physField, fourierInv_eq_fourier_neg]
  have hE : HasFDerivAt (physField f) (realVec.comp ((𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) (-x)).comp
      (-ContinuousLinearMap.id ℝ Space))) x := by
    rw [hphys]
    exact realVec.hasFDerivAt.comp x (hD.comp x (hasFDerivAt_id x).neg)
  rw [hE.fderiv]
  have hint : ∫ v, ‖VectorFourier.fourierSMulRight (innerSL ℝ) f v‖ ≤ ∫ v, 2 * π * (‖v‖ * ‖f v‖) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
      (hi'.const_mul (2 * π)) (Eventually.of_forall fun v => ?_)
    calc ‖VectorFourier.fourierSMulRight (innerSL ℝ) f v‖ ≤ 2 * π * ‖innerSL ℝ (E := Space)‖ * ‖v‖ * ‖f v‖ :=
          VectorFourier.norm_fourierSMulRight_le _ _ _
      _ ≤ 2 * π * 1 * ‖v‖ * ‖f v‖ := by gcongr; exact norm_innerSL_le ℝ
      _ = 2 * π * (‖v‖ * ‖f v‖) := by ring
  have hval : ∫ v, ‖v‖ * ‖f v‖ = (gradFreqL1Norm f).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun v => by positivity) hmeas, hlin]
  calc ‖realVec.comp ((𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) (-x)).comp
        (-ContinuousLinearMap.id ℝ Space))‖
      ≤ ‖realVec‖ * (‖𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) (-x)‖ *
          ‖-ContinuousLinearMap.id ℝ Space‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) (-x)‖ * 1) := by
        gcongr
        · exact opNorm_realVec_le
        · rw [norm_neg]
          exact ContinuousLinearMap.norm_id_le
    _ ≤ ∫ v, ‖VectorFourier.fourierSMulRight (innerSL ℝ) f v‖ := by
        rw [one_mul, mul_one]
        exact norm_freqTr_le_integral _ _
    _ ≤ ∫ v, 2 * π * (‖v‖ * ‖f v‖) := hint
    _ = 2 * π * (gradFreqL1Norm f).toReal := by rw [integral_const_mul, hval]

private theorem hsNormSq_le_two_mul (m : ℕ) (f : Space → CSpace) {g : Space → CSpace}
    (hg : AEStronglyMeasurable g volume) :
    hsNormSq m f ≤ 2 * hsNormSq m (f - g) + 2 * hsNormSq m g := by
  unfold hsNormSq
  have hmeas : AEMeasurable (fun ξ => 2 * (ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2)) volume := by
    have hw : Measurable fun ξ : Space => hsWeight m ξ := by
      unfold hsWeight
      fun_prop
    exact aemeasurable_const.mul
      ((ENNReal.measurable_ofReal.comp hw).aemeasurable.mul (hg.enorm.pow_const 2))
  rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_right' _ hmeas]
  refine lintegral_mono fun ξ => ?_
  have hw0 : 0 ≤ hsWeight m ξ := pow_nonneg (by positivity) _
  have key : ‖f ξ‖ ^ 2 ≤ 2 * ‖(f - g) ξ‖ ^ 2 + 2 * ‖g ξ‖ ^ 2 := by
    have t : ‖f ξ‖ ≤ ‖(f - g) ξ‖ + ‖g ξ‖ := by
      rw [Pi.sub_apply]
      exact norm_le_norm_sub_add _ _
    nlinarith [norm_nonneg (f ξ), norm_nonneg ((f - g) ξ), norm_nonneg (g ξ),
      sq_nonneg (‖(f - g) ξ‖ - ‖g ξ‖)]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
  simp only [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hw0]
  have e : ENNReal.ofReal (2 * (hsWeight m ξ * ‖(f - g) ξ‖ ^ 2) + 2 * (hsWeight m ξ * ‖g ξ‖ ^ 2)) =
      2 * ENNReal.ofReal (hsWeight m ξ * ‖(f - g) ξ‖ ^ 2) +
        2 * ENNReal.ofReal (hsWeight m ξ * ‖g ξ‖ ^ 2) := by
    have a1 : 0 ≤ hsWeight m ξ * ‖(f - g) ξ‖ ^ 2 := mul_nonneg hw0 (sq_nonneg _)
    have a2 : 0 ≤ hsWeight m ξ * ‖g ξ‖ ^ 2 := mul_nonneg hw0 (sq_nonneg _)
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (by norm_num),
      ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  rw [← e]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_le_mul_of_nonneg_left key hw0]

private theorem hsNormSq_boundedOn {m : ℕ} {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ t ∈ Icc 0 T, hsNormSq m (F t) ≤ A := by
  have key := (isCompact_Icc (a := (0 : ℝ)) (b := T)).induction_on
    (p := fun s => ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ t ∈ s, t ∈ Icc 0 T → hsNormSq m (F t) ≤ A)
    ⟨0, ENNReal.zero_lt_top, fun t ht => ht.elim⟩
    (fun s u hsu ⟨A, hA, h⟩ => ⟨A, hA, fun t ht => h t (hsu ht)⟩)
    (fun s u ⟨A, hA, h⟩ ⟨B, hB, h'⟩ => ⟨max A B, max_lt hA hB, fun t ht htI =>
      ht.elim (fun h1 => (h t h1 htI).trans (le_max_left _ _))
        (fun h2 => (h' t h2 htI).trans (le_max_right _ _))⟩)
    (fun t₀ ht₀ => ⟨{t | hsNormSq m (F t - F t₀) ∈ Iio 1}, (hF.2 t₀ ht₀) (Iio_mem_nhds zero_lt_one),
      2 * 1 + 2 * hsNormSq m (F t₀),
      ENNReal.add_lt_top.2 ⟨by norm_num, ENNReal.mul_lt_top (by norm_num) (hF.1 t₀ ht₀).2⟩,
      fun t ht _ => (hsNormSq_le_two_mul m (F t) (hF.1 t₀ ht₀).1).trans (by
        gcongr
        exact le_of_lt ht)⟩)
  obtain ⟨A, hA, h⟩ := key
  exact ⟨A, hA, fun t ht => h t ht ht⟩

theorem energyBoundedOn_physField {T : ℝ} {F : ℝ → Space → CSpace} (hF : IsHsCurve 3 F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    EnergyBoundedOn T (fun t => physField (F t)) := by
  obtain ⟨A, hA, hb⟩ := hsNormSq_boundedOn hF
  refine ⟨A.toReal, fun t ht => ?_⟩
  rw [ENNReal.ofReal_toReal hA.ne]
  exact (integral_sq_physField_le (hF.1 t ht).1 (hs t ht)
    ((hsNormSq_mono (by norm_num) _).trans_lt (hF.1 t ht).2)).trans
    ((hsNormSq_mono (by norm_num) _).trans (hb t ht))

theorem gradientBoundedOn_physField {T : ℝ} {F : ℝ → Space → CSpace} (hF : IsHsCurve 4 F 0 T) :
    GradientBoundedOn T (fun t => physField (F t)) := by
  obtain ⟨A, hA, hb⟩ := hsNormSq_boundedOn hF
  obtain ⟨C₁, h₁⟩ := freqL1Norm_le_hsNormSq
  obtain ⟨C₂, h₂⟩ := weightedFreqL1_le 1
  have hA' : A ^ (1 / 2 : ℝ) ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne).ne
  have hK₁ : ENNReal.ofReal C₁ * A ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA'
  have hK₂ : ENNReal.ofReal C₂ * A ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA'
  refine ⟨max (ENNReal.ofReal C₁ * A ^ (1 / 2 : ℝ)).toReal
    (2 * π * (ENNReal.ofReal C₂ * A ^ (1 / 2 : ℝ)).toReal), fun t ht x => ⟨?_, ?_⟩⟩
  · refine (norm_physField_le (hF.1 t ht).1
      ((hsNormSq_mono (by norm_num) _).trans_lt (hF.1 t ht).2) x).trans
      (le_trans ?_ (le_max_left _ _))
    refine ENNReal.toReal_mono hK₁ ((h₁ (F t)).trans ?_)
    gcongr
    exact (hsNormSq_mono (by norm_num) _).trans (hb t ht)
  · refine (norm_fderiv_physField_le (hF.1 t ht).1
      ((hsNormSq_mono (by norm_num) _).trans_lt (hF.1 t ht).2) x).trans
      (le_trans ?_ (le_max_right _ _))
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hK₂
      (((gradFreqL1Norm_le_weighted (F t)).trans (h₂ (F t))).trans ?_)) (by positivity)
    gcongr
    exact (hsNormSq_mono (by norm_num) _).trans (hb t ht)

end Breakdown.SmoothFlow
