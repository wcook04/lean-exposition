import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField

private theorem inverseQuartic_integrable (hIn : InnerSplitBound) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ y : Space,
      Integrable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) ∧
        ∫ z, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ ≤ C * (Real.sqrt τ)⁻¹ := by
  obtain ⟨C, hC⟩ := hIn 0 le_rfl (by norm_num)
  refine ⟨C, fun τ hτ y => ?_⟩
  obtain ⟨h1, h2, -⟩ := hC τ hτ y
  unfold kernelWeightIntegral at h2
  simp only [neg_zero, Real.rpow_zero, mul_one] at h1 h2
  exact ⟨h1, h2⟩

private theorem kernelConstant_nonneg {C : ℝ}
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4) : 0 ≤ C := by
  have h := (abs_nonneg _).trans (hC 0 0 0 1 0 one_pos)
  have hp : 0 < (‖(0 : Space)‖ + Real.sqrt 1) ^ 4 := by simp
  rwa [le_div_iff₀ hp, zero_mul] at h

private theorem kernelTerm_norm_le {C : ℝ}
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {τ : ℝ} (hτ : 0 < τ) (y z : Space) (H : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ)
    (hA : ∀ z, ‖H z‖ ≤ A) (i j k : Fin 3) :
    ‖lerayKernel i j k τ (y - z) * H z j k‖ ≤ C * A * ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ := by
  have hHjk : ‖H z j k‖ ≤ A :=
    (norm_le_pi_norm (H z j) k).trans ((norm_le_pi_norm (H z) j).trans (hA z))
  rw [norm_mul, Real.norm_eq_abs]
  calc |lerayKernel i j k τ (y - z)| * ‖H z j k‖ ≤ C / (‖y - z‖ + Real.sqrt τ) ^ 4 * A :=
        mul_le_mul (hC i j k τ (y - z) hτ) hHjk (norm_nonneg _)
          ((abs_nonneg _).trans (hC i j k τ (y - z) hτ))
    _ = C * A * ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ := by ring

private theorem kernelTerm_integrable (hKm : LerayKernelMeasurable) {C : ℝ}
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {τ : ℝ} (hτ : 0 < τ) (y : Space)
    (hint : Integrable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹))
    (H : Space → Fin 3 → Fin 3 → ℝ) (hH : Measurable H) (A : ℝ) (hA : ∀ z, ‖H z‖ ≤ A)
    (i j k : Fin 3) :
    Integrable (fun z => lerayKernel i j k τ (y - z) * H z j k) := by
  refine Integrable.mono' (hint.const_mul (C * A)) ?_
    (Eventually.of_forall fun z => kernelTerm_norm_le hC hτ y z H A hA i j k)
  exact (((hKm i j k).comp (measurable_const.prodMk (measurable_const.sub measurable_id))).mul
    ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hH))).aestronglyMeasurable

private theorem kernelConv_add_of_bounded (hKm : LerayKernelMeasurable) {C : ℝ}
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {τ : ℝ} (hτ : 0 < τ) (y : Space)
    (hint : Integrable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹))
    (G H : Space → Fin 3 → Fin 3 → ℝ) (hG : Measurable G) (hH : Measurable H) (A B : ℝ)
    (hA : ∀ z, ‖G z‖ ≤ A) (hB : ∀ z, ‖H z‖ ≤ B) :
    kernelConv τ (G + H) y = kernelConv τ G y + kernelConv τ H y := by
  unfold kernelConv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have iG : Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      kernelTerm_integrable hKm hC hτ y hint G hG A hA i j k
  have iH : Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      kernelTerm_integrable hKm hC hτ y hint H hH B hB i j k
  rw [← add_smul, ← integral_add iG iH]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem kernelConv_norm_le_of_bounded {C : ℝ}
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4) (hC0 : 0 ≤ C)
    {τ : ℝ} (hτ : 0 < τ) (y : Space) {C₁ : ℝ}
    (hint : Integrable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹))
    (hI : ∫ z, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ ≤ C₁ * (Real.sqrt τ)⁻¹)
    (H : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ) (hA : ∀ z, ‖H z‖ ≤ A) :
    ‖kernelConv τ H y‖ ≤ 27 * (C * A * (C₁ * (Real.sqrt τ)⁻¹)) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hcoord : ∀ i : Fin 3,
      ‖∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k‖ ≤
        9 * (C * A * (C₁ * (Real.sqrt τ)⁻¹)) := by
    intro i
    have hb : ∀ z, ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k‖ ≤
        9 * (C * A * ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) := by
      intro z
      calc ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k‖
          ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, C * A * ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun k _ => kernelTerm_norm_le hC hτ y z H A hA i j k))
        _ = 9 * (C * A * ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    refine (norm_integral_le_of_norm_le ((hint.const_mul (C * A)).const_mul 9)
      (Eventually.of_forall hb)).trans ?_
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (mul_nonneg hC0 hA0))
      (by norm_num)
  unfold kernelConv
  calc ‖∑ i : Fin 3, (∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k) •
        unitVector i‖
      ≤ ∑ i : Fin 3, ‖(∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k) •
        unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 9 * (C * A * (C₁ * (Real.sqrt τ)⁻¹)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [hu, mul_one]
        exact hcoord i
    _ = 27 * (C * A * (C₁ * (Real.sqrt τ)⁻¹)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private theorem tensorShift_measurable {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : Measurable (fun p : ℝ × Space => F p.1 p.2)) (s τ : ℝ) :
    Measurable (tensorShift F s τ) := by
  have h : Measurable (fun z : Space => (s - Real.log (1 + τ), (Real.sqrt (1 + τ))⁻¹ • z)) :=
    measurable_const.prodMk (continuous_const_smul _).measurable
  exact hF.comp h

private theorem shiftedIntegrand_measurable (hKm : LerayKernelMeasurable)
    {F : ℝ → Space → Fin 3 → Fin 3 → ℝ} (hF : Measurable (fun p : ℝ × Space => F p.1 p.2))
    (s : ℝ) (y : Space) (i : Fin 3) :
    Measurable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k p.1 (y - p.2) * tensorShift F s p.1 p.2 j k) := by
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.mul ?_ ?_
  · exact (hKm i j k).comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  · have h : Measurable (fun p : ℝ × Space =>
        (s - Real.log (1 + p.1), (Real.sqrt (1 + p.1))⁻¹ • p.2)) :=
      (measurable_const.sub (Real.measurable_log.comp (measurable_const.add measurable_fst))).prodMk
        (((Real.continuous_sqrt.measurable.comp (measurable_const.add measurable_fst)).inv).smul
          measurable_snd)
    exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp (hF.comp h))

private theorem weightedKernelConv_measurable (hKm : LerayKernelMeasurable)
    {F : ℝ → Space → Fin 3 → Fin 3 → ℝ} (hF : Measurable (fun p : ℝ × Space => F p.1 p.2))
    (β s : ℝ) (y : Space) :
    Measurable (fun τ : ℝ => (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) y) := by
  refine ((measurable_const.add measurable_id).pow_const _).smul ?_
  unfold kernelConv
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((shiftedIntegrand_measurable hKm hF s y i).stronglyMeasurable.integral_prod_right'
    ).measurable.smul_const _

private theorem kernelConv_smul' (τ c : ℝ) (G : Space → Fin 3 → Fin 3 → ℝ) (y : Space) :
    kernelConv τ (c • G) y = c • kernelConv τ G y := by
  unfold kernelConv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem profileOp_smul' (β c : ℝ) (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (s : ℝ)
    (y : Space) : profileOp β (c • F) s y = c • profileOp β F s y := by
  unfold profileOp
  rw [smul_neg, ← integral_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  have e : tensorShift (c • F) s τ = c • tensorShift F s τ := rfl
  simp only
  rw [e, kernelConv_smul']
  exact smul_comm _ _ _

theorem opLinear_of_kernel :
    LerayKernelMeasurable → InnerSplitBound → SmallTimeIntegrable → OpLinear := by
  intro hKm hIn hSm hK
  refine ⟨?_, fun β c F s y => profileOp_smul' β c F s y⟩
  intro β hβ F G hF hG s y
  obtain ⟨CK, hCK⟩ := hK
  have hCK0 := kernelConstant_nonneg hCK
  obtain ⟨C₁, hC₁⟩ := inverseQuartic_integrable hIn
  obtain ⟨hFm, AF, hAF⟩ := hF
  obtain ⟨hGm, AG, hAG⟩ := hG
  have h0 := hSm 0
  simp only [Nat.cast_zero, zero_div, add_zero] at h0
  have hout : ∀ (H : ℝ → Space → Fin 3 → Fin 3 → ℝ) (AH : ℝ),
      Measurable (fun p : ℝ × Space => H p.1 p.2) → (∀ s z, ‖H s z‖ ≤ AH) →
        IntegrableOn (fun τ => (1 + τ) ^ (-β) • kernelConv τ (tensorShift H s τ) y) (Ioi 0) := by
    intro H AH hHm hAH
    refine Integrable.mono' (h0.const_mul (27 * (CK * AH * C₁)))
      (weightedKernelConv_measurable hKm hHm β s y).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_)
    have hτ' : 0 < τ := hτ
    have hk := kernelConv_norm_le_of_bounded hCK hCK0 hτ' y (hC₁ τ hτ' y).1 (hC₁ τ hτ' y).2
      (tensorShift H s τ) AH (fun z => hAH _ _)
    have hp : (1 + τ) ^ (-β) ≤ (1 + τ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hp0 : 0 ≤ (1 + τ) ^ (-β) := Real.rpow_nonneg (by linarith) _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
    calc (1 + τ) ^ (-β) * ‖kernelConv τ (tensorShift H s τ) y‖
        ≤ (1 + τ) ^ (-(1 : ℝ)) * (27 * (CK * AH * (C₁ * (Real.sqrt τ)⁻¹))) :=
          mul_le_mul hp hk (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _ = 27 * (CK * AH * C₁) * ((1 + τ) ^ (-(1 : ℝ)) * (Real.sqrt τ)⁻¹) := by ring
  have hadd : ∀ τ ∈ Ioi (0 : ℝ),
      (1 + τ) ^ (-β) • kernelConv τ (tensorShift (F + G) s τ) y =
        (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) y +
          (1 + τ) ^ (-β) • kernelConv τ (tensorShift G s τ) y := by
    intro τ hτ
    have e : tensorShift (F + G) s τ = tensorShift F s τ + tensorShift G s τ := rfl
    rw [← smul_add, e, kernelConv_add_of_bounded hKm hCK hτ y (hC₁ τ hτ y).1 _ _
      (tensorShift_measurable hFm s τ) (tensorShift_measurable hGm s τ) AF AG
      (fun z => hAF _ _) (fun z => hAG _ _)]
  unfold profileOp
  rw [← neg_add, ← integral_add (hout F AF hFm hAF) (hout G AG hGm hAG)]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi hadd

end Breakdown.FarField
