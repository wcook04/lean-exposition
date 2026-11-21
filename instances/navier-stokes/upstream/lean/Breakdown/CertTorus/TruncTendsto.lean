import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

open Freq

private lemma norm_tensorField_le_mul {a b : Space → Space} {A B : ℝ} (ha : ∀ z, ‖a z‖ ≤ A)
    (hb : ∀ z, ‖b z‖ ≤ B) (z : Space) : ‖tensorField a b z‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha z)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb z)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hA hB)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hA hB)).2 fun k => ?_
  show ‖a z j * b z k‖ ≤ A * B
  rw [norm_mul]
  exact mul_le_mul ((PiLp.norm_apply_le (a z) j).trans (ha z))
    ((PiLp.norm_apply_le (b z) k).trans (hb z)) (norm_nonneg _) hA

private lemma measurable_similarityArg (s : ℝ) :
    Measurable (fun p : ℝ × Space => (s - Real.log (1 + p.1), (Real.sqrt (1 + p.1))⁻¹ • p.2)) :=
  (measurable_const.sub (Real.measurable_log.comp (measurable_const.add measurable_fst))).prodMk
    (((Real.continuous_sqrt.measurable.comp (measurable_const.add measurable_fst)).inv).smul
      measurable_snd)

private lemma continuous_similarityShift {W : ℝ → Space → Space}
    (hW : Continuous (fun p : ℝ × Space => W p.1 p.2)) (s τ : ℝ) :
    Continuous (similarityShift W s τ) :=
  hW.comp (continuous_const.prodMk (continuous_const_smul _))

private lemma measurable_tensorField_shift {W : ℝ → Space → Space}
    (hW : Continuous (fun p : ℝ × Space => W p.1 p.2)) (s τ : ℝ) :
    Measurable (tensorField (similarityShift W s τ) (similarityShift W s τ)) := by
  have h := continuous_similarityShift hW s τ
  have hj : ∀ j : Fin 3, Continuous fun z => similarityShift W s τ z j :=
    fun j => (EuclideanSpace.proj j).continuous.comp h
  exact (continuous_pi fun j => continuous_pi fun k => (hj j).mul (hj k)).measurable

private lemma integrableOn_inv_one_add_mul_rpow :
    IntegrableOn (fun τ : ℝ => (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have hmeas : Measurable (fun τ : ℝ => (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) :=
    (measurable_const.add measurable_id).inv.mul (measurable_id.pow_const _)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    refine h1.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_))
    have hτ0 : 0 < τ := hτ.1
    have hr : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le _
    have hinv : (1 + τ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hinv0 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hinv0 hr)]
    calc (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ)) ≤ 1 * τ ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hr
      _ = τ ^ (-(1 / 2 : ℝ)) := one_mul _
  · have h2 : IntegrableOn (fun τ : ℝ => τ ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine h2.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_))
    have hτ0 : 0 < τ := lt_trans zero_lt_one hτ
    have hr : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le _
    have hinv0 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
    have hinv : (1 + τ)⁻¹ ≤ τ ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      exact inv_anti₀ hτ0 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hinv0 hr)]
    calc (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ)) ≤ τ ^ (-(1 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hr
      _ = τ ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hτ0]
          norm_num

theorem truncTendsto_of_kernel :
    KernelConvSup → LerayKernelBound → LerayKernelMeasurable → TruncTendsto := by
  intro hSup _ hM W hW CW hCW s y
  obtain ⟨C, hC⟩ := hSup
  set f : ℝ → Space := fun τ =>
    (1 + τ)⁻¹ • kernelConv τ (tensorField (similarityShift W s τ) (similarityShift W s τ)) y with hf
  set G : Fin 3 → ℝ × Space → ℝ := fun i p =>
    ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k p.1 (y - p.2) *
      (W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2) j *
        W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2) k) with hG
  have hfG : f = fun τ => (1 + τ)⁻¹ • ∑ i : Fin 3, (∫ z, G i (τ, z)) • unitVector i := rfl
  have hV : Measurable (fun p : ℝ × Space =>
      W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2)) :=
    hW.measurable.comp (measurable_similarityArg s)
  have hVj : ∀ j : Fin 3, Measurable (fun p : ℝ × Space =>
      W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2) j) :=
    fun j => (EuclideanSpace.proj j).continuous.measurable.comp hV
  have hGm : ∀ i, Measurable (G i) := by
    intro i
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    exact ((hM i j k).comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))).mul
      ((hVj j).mul (hVj k))
  have hIm : ∀ i, Measurable (fun τ : ℝ => ∫ z, G i (τ, z)) :=
    fun i => (hGm i).stronglyMeasurable.integral_prod_right'.measurable
  have hfm : Measurable f := by
    rw [hfG]
    exact (measurable_const.add measurable_id).inv.smul
      (Finset.measurable_sum _ fun i _ => (hIm i).smul_const _)
  have hbound : ∀ τ ∈ Ioi (0 : ℝ),
      ‖f τ‖ ≤ (C * (CW * CW)) * ((1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have hsh : ∀ z, ‖similarityShift W s τ z‖ ≤ CW := fun z => hCW _ _
    have hk := hC τ hτ0 _ (measurable_tensorField_shift hW s τ) (CW * CW)
      (norm_tensorField_le_mul hsh hsh) y
    have hinv0 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
    calc ‖f τ‖ = (1 + τ)⁻¹ *
          ‖kernelConv τ (tensorField (similarityShift W s τ) (similarityShift W s τ)) y‖ := by
          rw [hf, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
      _ ≤ (1 + τ)⁻¹ * (C * τ ^ (-(1 / 2 : ℝ)) * (CW * CW)) :=
          mul_le_mul_of_nonneg_left hk hinv0
      _ = (C * (CW * CW)) * ((1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) := by ring
  have hint : IntegrableOn f (Ioi 0) :=
    (integrableOn_inv_one_add_mul_rpow.const_mul (C * (CW * CW))).mono' hfm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
  have hlim := (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).neg
  refine hlim.congr' ((eventually_ge_atTop 0).mono fun T hT => ?_)
  simp only [id, profileBilinTrunc]
  rw [intervalIntegral.integral_of_le hT]
