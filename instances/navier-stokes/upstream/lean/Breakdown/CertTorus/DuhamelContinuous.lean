import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

namespace Internal.DuhamelContinuity

theorem continuous_conv_of_dominated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → Space → E) (bound : Space → ℝ) (hb : Integrable bound)
    (hmeas : ∀ y, AEStronglyMeasurable (fun w => g w (y - w)))
    (hle : ∀ y w, ‖g w (y - w)‖ ≤ bound w)
    (hc : ∀ w, Continuous (fun y => g w (y - w))) :
    Continuous (fun y => ∫ z, g (y - z) z) := by
  have e : (fun y => ∫ z, g (y - z) z) = fun y => ∫ w, g w (y - w) := by
    funext y
    have h := integral_sub_left_eq_self (fun w => g w (y - w)) (volume : Measure Space) y
    simp only [sub_sub_cancel] at h
    exact h
  rw [e]
  exact continuous_of_dominated hmeas (fun y => Eventually.of_forall (hle y)) hb
    (Eventually.of_forall hc)

theorem integrable_of_le_inv_pow_four {K : Space → ℝ} (hK : AEStronglyMeasurable K) {B τ : ℝ}
    (hτ : 0 < τ) (hKB : ∀ x, |K x| ≤ B / (‖x‖ + Real.sqrt τ) ^ 4) : Integrable K := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hm : 0 < min 1 (Real.sqrt τ) := lt_min one_pos hs
  have hint : Integrable (fun x : Space => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine (hint.const_mul (|B| / min 1 (Real.sqrt τ) ^ 4)).mono' hK (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (hKB x).trans ?_
  have hx := norm_nonneg x
  have a1 : min 1 (Real.sqrt τ) ≤ 1 := min_le_left _ _
  have a2 : min 1 (Real.sqrt τ) ≤ Real.sqrt τ := min_le_right _ _
  have h1 : min 1 (Real.sqrt τ) * (1 + ‖x‖) ≤ ‖x‖ + Real.sqrt τ := by nlinarith
  have hp : 0 < 1 + ‖x‖ := by positivity
  have hq : 0 < min 1 (Real.sqrt τ) * (1 + ‖x‖) := mul_pos hm hp
  have e4 : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hp.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e4]
  calc B / (‖x‖ + Real.sqrt τ) ^ 4 ≤ |B| / (‖x‖ + Real.sqrt τ) ^ 4 :=
        div_le_div_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ |B| / (min 1 (Real.sqrt τ) * (1 + ‖x‖)) ^ 4 :=
        div_le_div_of_nonneg_left (abs_nonneg B) (pow_pos hq 4) (pow_le_pow_left₀ hq.le h1 4)
    _ = |B| / min 1 (Real.sqrt τ) ^ 4 * ((1 + ‖x‖) ^ (4 : ℕ))⁻¹ := by
        rw [mul_pow, div_mul_eq_div_div, div_eq_mul_inv (|B| / min 1 (Real.sqrt τ) ^ 4)]

theorem abs_coord_mul_le {a b : Space} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (j k : Fin 3) :
    |a j * b k| ≤ C * C := by
  rw [abs_mul]
  have h1 : |a j| ≤ C := by
    have := PiLp.norm_apply_le a j
    rw [Real.norm_eq_abs] at this
    exact this.trans ha
  have h2 : |b k| ≤ C := by
    have := PiLp.norm_apply_le b k
    rw [Real.norm_eq_abs] at this
    exact this.trans hb
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem continuous_coord (j : Fin 3) : Continuous (fun v : Space => v j) := by
  fun_prop

theorem continuous_heatKernel_of (T : ℝ) : Continuous (heatKernel T) := by
  unfold heatKernel
  fun_prop

theorem integrable_heatKernel_of {T : ℝ} (hT : 0 < T) : Integrable (heatKernel T) := by
  have hb : 0 < ((1 / (4 * T) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have h := ((GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : Space)).norm).const_mul
    ((4 * π * T) ^ (-(3 / 2 : ℝ)))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  unfold heatKernel
  congr 2
  simp only [neg_mul, Complex.neg_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end Internal.DuhamelContinuity

open Internal.DuhamelContinuity in
theorem duhamelContinuous_of_kernel :
    HeatKernelBounds → KernelConvSup → LerayKernelBound → LerayKernelMeasurable →
      LerayKernelJointContinuous → DuhamelContinuous := by
  intro _ hSup hB hM _ W hW C hC s T hT
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
  have hCC : 0 ≤ C * C := mul_nonneg hC0 hC0
  have hWs : ∀ t, Continuous (W t) := fun t => hW.comp (continuous_const.prodMk continuous_id)
  have hsh : ∀ τ, Continuous (similarityShift W s τ) := fun τ =>
    (hWs _).comp (continuous_const_smul _)
  have hFc : ∀ τ (j k : Fin 3),
      Continuous (fun v => tensorField (similarityShift W s τ) (similarityShift W s τ) v j k) :=
    fun τ j k => ((continuous_coord j).comp (hsh τ)).mul ((continuous_coord k).comp (hsh τ))
  have hFabs : ∀ τ v (j k : Fin 3),
      |tensorField (similarityShift W s τ) (similarityShift W s τ) v j k| ≤ C * C :=
    fun τ v j k => abs_coord_mul_le (hC _ _) (hC _ _) j k
  have hFmeas : ∀ τ, Measurable (tensorField (similarityShift W s τ) (similarityShift W s τ)) :=
    fun τ => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => (hFc τ j k).measurable
  have hFbd : ∀ τ z, ‖tensorField (similarityShift W s τ) (similarityShift W s τ) z‖ ≤ C * C :=
    fun τ z => (pi_norm_le_iff_of_nonneg hCC).2 fun j => (pi_norm_le_iff_of_nonneg hCC).2 fun k => by
      rw [Real.norm_eq_abs]
      exact hFabs τ z j k
  have hKm : ∀ i j k : Fin 3, ∀ τ : ℝ, Measurable (lerayKernel i j k τ) := fun i j k τ =>
    (hM i j k).comp measurable_prodMk_left
  obtain ⟨B, hBd⟩ := hB
  have hKint : ∀ i j k : Fin 3, ∀ τ : ℝ, 0 < τ → Integrable (lerayKernel i j k τ) :=
    fun i j k τ hτ => integrable_of_le_inv_pow_four (hKm i j k τ).aestronglyMeasurable hτ
      (fun x => hBd i j k τ x hτ)
  obtain ⟨K, hK⟩ := hSup
  refine Continuous.add ?_ ?_
  · unfold similarityHeatPart heatConv
    have hH : ∀ w, 0 ≤ heatKernel T w := fun w => by
      unfold heatKernel
      exact mul_nonneg (Real.rpow_nonneg (mul_pos (mul_pos (by norm_num) Real.pi_pos) hT).le _)
        (Real.exp_pos _).le
    have hcont : Continuous fun y => ∫ z, heatKernel T (y - z) • similarityShift W s T z :=
      continuous_conv_of_dominated (fun w v => heatKernel T w • similarityShift W s T v)
      (fun w => heatKernel T w * C) ((integrable_heatKernel_of hT).mul_const C)
      (fun y => ((continuous_heatKernel_of T).smul
        ((hsh T).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (fun y w => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hH w)]
        exact mul_le_mul_of_nonneg_left (hC _ _) (hH w))
      (fun w => continuous_const.fun_smul ((hsh T).comp (continuous_id.sub continuous_const)))
    exact hcont.fun_const_smul _
  · unfold profileBilinTrunc
    refine Continuous.neg ?_
    refine continuous_of_dominated (bound := fun τ => |K| * τ ^ (-(1 / 2 : ℝ)) * (C * C)) ?_ ?_ ?_ ?_
    · intro y
      refine Measurable.aestronglyMeasurable ?_
      unfold kernelConv tensorField similarityShift
      have hWc : Measurable fun p : ℝ × Space =>
          W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2) :=
        hW.measurable.comp (f := fun p : ℝ × Space =>
          (s - Real.log (1 + p.1), (Real.sqrt (1 + p.1))⁻¹ • p.2)) (by fun_prop)
      refine ((measurable_const.add measurable_id).inv).smul ?_
      refine Finset.measurable_sum _ fun i _ => ?_
      refine Measurable.smul_const ?_ _
      have hΦ : Measurable fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          lerayKernel i j k p.1 (y - p.2) *
            ((W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2)) j *
              (W (s - Real.log (1 + p.1)) ((Real.sqrt (1 + p.1))⁻¹ • p.2)) k) :=
        Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
          ((hM i j k).comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))).mul
            (((continuous_coord j).measurable.comp hWc).mul ((continuous_coord k).measurable.comp hWc))
      exact (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure Space))
        hΦ.stronglyMeasurable).measurable
    · intro y
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hτ.1
      have hk := hK τ hτ0 _ (hFmeas τ) (C * C) (hFbd τ) y
      have h1 : (1 + τ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have h2 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
      have h3 : K * τ ^ (-(1 / 2 : ℝ)) * (C * C) ≤ |K| * τ ^ (-(1 / 2 : ℝ)) * (C * C) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hτ0.le _)) hCC
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h2]
      nlinarith [norm_nonneg (kernelConv τ
        (tensorField (similarityShift W s τ) (similarityShift W s τ)) y)]
    · have hi : IntervalIntegrable (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) volume 0 T :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hi).const_mul |K|).mul_const
        (C * C)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hτ.1
      have hcont : Continuous fun y =>
          kernelConv τ (tensorField (similarityShift W s τ) (similarityShift W s τ)) y := by
        unfold kernelConv
        refine continuous_finsetSum _ fun i _ => ?_
        refine Continuous.fun_smul ?_ continuous_const
        exact continuous_conv_of_dominated
          (fun w v => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ w *
            tensorField (similarityShift W s τ) (similarityShift W s τ) v j k)
          (fun w => ∑ j : Fin 3, ∑ k : Fin 3, |lerayKernel i j k τ w| * (C * C))
          (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
            (hKint i j k τ hτ0).abs.mul_const _)
          (fun y => (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
            (hKm i j k τ).mul ((hFc τ j k).measurable.comp
              (measurable_const.sub measurable_id))).aestronglyMeasurable)
          (fun y w => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_left (hFabs τ _ j k) (abs_nonneg _))))
          (fun w => continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
            continuous_const.fun_mul ((hFc τ j k).comp (continuous_id.sub continuous_const)))
      exact hcont.fun_const_smul _

end Breakdown.FarField
