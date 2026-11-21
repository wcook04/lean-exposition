import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

namespace KernelConvL3Internal

theorem add_norm_rpow_eq {s : ℝ} (hs : 0 < s) (x : Space) (r : ℝ) :
    s ^ (-r) * (1 + ‖s⁻¹ • x‖) ^ (-r) = (‖x‖ + s) ^ (-r) := by
  rw [← Real.mul_rpow hs.le (by positivity), norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  congr 1
  field_simp
  ring

theorem integrable_add_norm_rpow_neg_six {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : Space => (‖x‖ + s) ^ (-6 : ℝ)) := by
  have h1 : Integrable (fun x : Space => (1 + ‖x‖) ^ (-6 : ℝ)) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  have h2 := (h1.comp_smul (inv_ne_zero hs.ne')).const_mul (s ^ (-6 : ℝ))
  refine h2.congr (Eventually.of_forall fun x => ?_)
  exact add_norm_rpow_eq hs x 6

theorem integral_add_norm_rpow_neg_six {s : ℝ} (hs : 0 < s) :
    ∫ x : Space, (‖x‖ + s) ^ (-6 : ℝ) = s ^ (-3 : ℝ) * ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Space)
    (fun x : Space => (1 + ‖x‖) ^ (-6 : ℝ)) hs.le
  rw [finrank_euclideanSpace_fin] at h
  calc ∫ x : Space, (‖x‖ + s) ^ (-6 : ℝ)
      = ∫ x : Space, s ^ (-6 : ℝ) * (1 + ‖s⁻¹ • x‖) ^ (-6 : ℝ) := by
        congr 1; ext x; exact (add_norm_rpow_eq hs x 6).symm
    _ = s ^ (-6 : ℝ) * (s ^ 3 * ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) := by
        rw [integral_const_mul, h, smul_eq_mul]
    _ = s ^ (-3 : ℝ) * ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ) := by
        rw [← mul_assoc]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_add hs]
        norm_num

theorem holder_weight_bound {τ : ℝ} (hτ : 0 < τ) (y : Space) {F : Space → Fin 3 → Fin 3 → ℝ}
    (hF : MemLp F 3 volume) :
    Integrable (fun z => (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) ∧
    ∫ z, (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖ ≤
      τ ^ (-1 : ℝ) * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ) *
        (eLpNorm F 3 volume).toReal := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hgm : AEStronglyMeasurable (fun z : Space => (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)) volume :=
    (by fun_prop : Measurable fun z : Space => (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)).aestronglyMeasurable
  have hg6 : ∀ z : Space, ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)) ^ (3 / 2 : ℝ) =
      (‖y - z‖ + Real.sqrt τ) ^ (-6 : ℝ) := by
    intro z
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  have hint6 : Integrable (fun z : Space => (‖y - z‖ + Real.sqrt τ) ^ (-6 : ℝ)) :=
    (integrable_add_norm_rpow_neg_six hs).comp_sub_left y
  have hgL : MemLp (fun z : Space => (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)) (ENNReal.ofReal (3 / 2))
      volume := by
    rw [← integrable_norm_rpow_iff hgm (by rw [Ne, ENNReal.ofReal_eq_zero]; norm_num)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num)]
    refine hint6.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [Real.norm_of_nonneg (by positivity), hg6]
  have hFn : MemLp (fun z => ‖F z‖) (ENNReal.ofReal 3) volume := by
    rw [show ENNReal.ofReal 3 = 3 by simp]
    exact hF.norm
  have := hpq.ennrealOfReal
  have hInt : Integrable (fun z => (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) :=
    hgL.integrable_mul hFn
  refine ⟨hInt, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun z => by positivity)
    (ae_of_all _ fun z => norm_nonneg (F z)) hgL hFn
  have hI0 : 0 ≤ ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ) := integral_nonneg fun x => by positivity
  have e1 : ∫ z : Space, ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)) ^ (3 / 2 : ℝ) =
      Real.sqrt τ ^ (-3 : ℝ) * ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ) := by
    simp_rw [hg6]
    have ht := integral_sub_left_eq_self (fun x : Space => (‖x‖ + Real.sqrt τ) ^ (-6 : ℝ))
      (volume : Measure Space) y
    rw [ht]
    exact integral_add_norm_rpow_neg_six hs
  have e2 : (Real.sqrt τ ^ (-3 : ℝ) * ∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (1 / (3 / 2) : ℝ) =
      τ ^ (-1 : ℝ) * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hI0, Real.sqrt_eq_rpow, ← Real.rpow_mul hτ.le,
      ← Real.rpow_mul hτ.le]
    norm_num
  have e3 : (∫ z, ‖F z‖ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = (eLpNorm F 3 volume).toReal := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _), one_div]
  calc ∫ z, (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖ ≤ _ := hH
    _ = _ := by rw [e1, e2, e3]

end KernelConvL3Internal

open KernelConvL3Internal in
theorem kernelConvL3Pointwise_of_bound :
    LerayKernelBound → LerayKernelMeasurable → KernelConvL3Pointwise := by
  rintro ⟨C, hC⟩ hM
  refine ⟨27 * C * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ), ?_⟩
  intro τ hτ F hF y
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 0 0 0 τ 0 hτ)
    have hp : 0 < (‖(0 : Space)‖ + Real.sqrt τ) ^ 4 := by positivity
    exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hp))
  obtain ⟨hInt, hBd⟩ := holder_weight_bound hτ y hF
  have hterm : ∀ i j k : Fin 3, ∀ z : Space, ‖lerayKernel i j k τ (y - z) * F z j k‖ ≤
      C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) := by
    intro i j k z
    have hK := hC i j k τ (y - z) hτ
    have hFjk : ‖F z j k‖ ≤ ‖F z‖ := (norm_le_pi_norm (F z j) k).trans (norm_le_pi_norm (F z) j)
    have hgz : C / (‖y - z‖ + Real.sqrt τ) ^ 4 = C * (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) := by
      rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
      norm_cast
    rw [norm_mul, Real.norm_eq_abs]
    calc |lerayKernel i j k τ (y - z)| * ‖F z j k‖
        ≤ (C * (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ)) * ‖F z‖ := by
          rw [← hgz]
          exact mul_le_mul hK hFjk (norm_nonneg _) (by positivity)
      _ = C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) := by ring
  have hsum : ∀ i : Fin 3, ∀ z : Space,
      ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k‖ ≤
        9 * C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) := by
    intro i z
    calc ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k‖
        ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖lerayKernel i j k τ (y - z) * F z j k‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm i j k z
      _ = 9 * C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hmeas : ∀ i : Fin 3, AEStronglyMeasurable
      (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) volume := by
    intro i
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((hM i j k).comp (measurable_const.prodMk
        (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact Continuous.comp_aestronglyMeasurable (g := fun v : Fin 3 → Fin 3 → ℝ => v j k)
        (by fun_prop) hF.1
  have hdom : Integrable (fun z : Space => 9 * C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖)) :=
    hInt.const_mul _
  have hiInt : ∀ i : Fin 3, Integrable
      (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) :=
    fun i => hdom.mono' (hmeas i) (ae_of_all _ (hsum i))
  refine ⟨hiInt, ?_⟩
  have hcoord : ∀ i : Fin 3,
      ‖(∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) • unitVector i‖ ≤
        9 * C * (τ ^ (-1 : ℝ) * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ) *
          (eLpNorm F 3 volume).toReal) := by
    intro i
    rw [norm_smul, unitVector, PiLp.norm_single, norm_one, mul_one]
    calc ‖∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k‖
        ≤ ∫ z, 9 * C * ((‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖) :=
          norm_integral_le_of_norm_le hdom (ae_of_all _ (hsum i))
      _ = 9 * C * ∫ z, (‖y - z‖ + Real.sqrt τ) ^ (-4 : ℝ) * ‖F z‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hBd (by positivity)
  unfold kernelConv
  calc ‖∑ i : Fin 3, (∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) •
        unitVector i‖
      ≤ ∑ i : Fin 3, ‖(∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) •
        unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 9 * C * (τ ^ (-1 : ℝ) * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ) *
          (eLpNorm F 3 volume).toReal) := Finset.sum_le_sum fun i _ => hcoord i
    _ = 27 * C * (∫ x : Space, (1 + ‖x‖) ^ (-6 : ℝ)) ^ (2 / 3 : ℝ) * τ ^ (-(1 : ℝ)) *
          (eLpNorm F 3 volume).toReal := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Breakdown.FarField
