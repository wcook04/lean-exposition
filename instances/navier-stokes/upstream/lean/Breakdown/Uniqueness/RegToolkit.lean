import Breakdown.Uniqueness.RegDefs
import Breakdown.Uniqueness.RegToolkitAuxSupBound
import Breakdown.Uniqueness.RegToolkitAuxTame

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma weight_ratio_sq_le (k : ℕ) (ξ : Space) :
    ((1 + ‖ξ‖) ^ k / Real.sqrt (hsWeight (k + 2) ξ)) ^ 2 ≤
      2 ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hq : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hw : 0 ≤ hsWeight (k + 2) ξ := by unfold hsWeight; positivity
  rw [div_pow, Real.sq_sqrt hw, show (-(4 : ℝ) / 2) = -2 by norm_num, Real.rpow_neg hq.le,
    Real.rpow_two]
  unfold hsWeight
  have hnum : ((1 + ‖ξ‖) ^ k) ^ 2 ≤ 2 ^ k * (1 + ‖ξ‖ ^ 2) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (‖ξ‖ - 1)]) k
  calc ((1 + ‖ξ‖) ^ k) ^ 2 / (1 + ‖ξ‖ ^ 2) ^ (k + 2)
      ≤ 2 ^ k * (1 + ‖ξ‖ ^ 2) ^ k / (1 + ‖ξ‖ ^ 2) ^ (k + 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 ^ k * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
        rw [pow_add]
        field_simp

private lemma weight_integrable (k : ℕ) :
    Integrable (fun ξ : Space => (2 : ℝ) ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2)) volume := by
  refine Integrable.const_mul (integrable_rpow_neg_one_add_norm_sq ?_) _
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  norm_num

private lemma memLp_two_of_lintegral_sq {g : Space → ℂ} (hg : AEStronglyMeasurable g volume)
    (h : ∫⁻ η, ‖g η‖ₑ ^ 2 < ⊤) : MemLp g 2 volume := by
  refine ⟨hg, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa using h

private lemma component_sq_le_weight (f : Space → CSpace) (η : Space) (j : Fin 3) :
    ‖f η j‖ₑ ^ 2 ≤ ENNReal.ofReal (hsWeight 1 η) * ‖f η‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by unfold hsWeight; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le (f η) j
  have h2 : ‖f η j‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (1 : ℝ) ≤ hsWeight 1 η := by unfold hsWeight; nlinarith [sq_nonneg ‖η‖]
  nlinarith [sq_nonneg ‖f η‖]

private lemma coord_component_sq_le_weight (f : Space → CSpace) (η : Space) (j : Fin 3) :
    ‖((η j : ℝ) : ℂ) * f η j‖ₑ ^ 2 ≤ ENNReal.ofReal (hsWeight 1 η) * ‖f η‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by unfold hsWeight; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le (f η) j
  have h1' : ‖η j‖ ≤ ‖η‖ := PiLp.norm_apply_le η j
  rw [norm_mul, Complex.norm_real, mul_pow]
  have h2 : ‖f η j‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' : ‖η j‖ ^ 2 ≤ ‖η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1' 2
  have h3 : ‖η j‖ ^ 2 * ‖f η j‖ ^ 2 ≤ ‖η‖ ^ 2 * ‖f η‖ ^ 2 :=
    mul_le_mul h2' h2 (by positivity) (by positivity)
  unfold hsWeight
  nlinarith [sq_nonneg ‖f η‖]

private lemma memLp_component {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (h3 : hsNormSq 1 f < ⊤) (j : Fin 3) : MemLp (fun η => f η j) 2 volume := by
  refine memLp_two_of_lintegral_sq ?_ (lt_of_le_of_lt (lintegral_mono fun η => ?_) h3)
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j |>.continuous.comp
      (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hm
  · exact component_sq_le_weight f η j

private lemma memLp_coord_component {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (h3 : hsNormSq 1 f < ⊤) (j : Fin 3) :
    MemLp (fun η => ((η j : ℝ) : ℂ) * f η j) 2 volume := by
  refine memLp_two_of_lintegral_sq ?_ (lt_of_le_of_lt (lintegral_mono fun η => ?_) h3)
  · refine AEStronglyMeasurable.mul ?_ (memLp_component hm h3 j).1
    exact (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j))).aestronglyMeasurable
  · exact coord_component_sq_le_weight f η j

theorem weightedFreqL1_le (k : ℕ) : ∃ C : ℝ, ∀ f : Space → CSpace,
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ ≤
      ENNReal.ofReal C * hsNormSq (k + 2) f ^ (1 / 2 : ℝ) := by
  set I := ∫ ξ : Space, (2 : ℝ) ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun ξ => by positivity
  refine ⟨Real.sqrt I, fun f => ?_⟩
  obtain ⟨G, hGm, hGle, hGeq⟩ := exists_measurable_le_lintegral_eq (μ := (volume : Measure Space))
    (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ)
  rw [hGeq]
  set s : Space → ℝ := fun ξ => Real.sqrt (hsWeight (k + 2) ξ) with hs
  set v : Space → ℝ := fun ξ => (1 + ‖ξ‖) ^ k with hv
  have hspos : ∀ ξ, 0 < s ξ := fun ξ => Real.sqrt_pos.2 (by simp only [hsWeight]; positivity)
  have hvpos : ∀ ξ, 0 < v ξ := fun ξ => by simp only [hv]; positivity
  have hsm : Measurable s := by
    simp only [hs, hsWeight]; fun_prop
  have hvm : Measurable v := by
    simp only [hv]; fun_prop
  have hF1m : Measurable fun ξ => G ξ * ENNReal.ofReal (s ξ / v ξ) :=
    hGm.mul (hsm.div hvm).ennreal_ofReal
  have hF2m : Measurable fun ξ => ENNReal.ofReal (v ξ / s ξ) := (hvm.div hsm).ennreal_ofReal
  have hsplit : ∀ ξ, G ξ = (G ξ * ENNReal.ofReal (s ξ / v ξ)) * ENNReal.ofReal (v ξ / s ξ) := by
    intro ξ
    have h1 : s ξ / v ξ * (v ξ / s ξ) = 1 := by
      field_simp [(hvpos ξ).ne', (hspos ξ).ne']
    rw [mul_assoc, ← ENNReal.ofReal_mul (div_pos (hspos ξ) (hvpos ξ)).le, h1, ENNReal.ofReal_one,
      mul_one]
  have hF1 : ∀ ξ, (G ξ * ENNReal.ofReal (s ξ / v ξ)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (hsWeight (k + 2) ξ) * ‖f ξ‖ₑ ^ 2 := by
    intro ξ
    rw [ENNReal.rpow_two]
    calc (G ξ * ENNReal.ofReal (s ξ / v ξ)) ^ 2
        ≤ (ENNReal.ofReal (v ξ) * ‖f ξ‖ₑ * ENNReal.ofReal (s ξ / v ξ)) ^ 2 := by
          gcongr; exact hGle ξ
      _ = ENNReal.ofReal (hsWeight (k + 2) ξ) * ‖f ξ‖ₑ ^ 2 := by
          rw [mul_right_comm, ← ENNReal.ofReal_mul (hvpos ξ).le, mul_div_cancel₀ _ (hvpos ξ).ne',
            mul_pow, ← ENNReal.ofReal_pow (hspos ξ).le, hs, Real.sq_sqrt (by
              simp only [hsWeight]; positivity)]
  have hF2 : ∀ ξ, ENNReal.ofReal (v ξ / s ξ) ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2)) := by
    intro ξ
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (div_pos (hvpos ξ) (hspos ξ)).le]
    exact ENNReal.ofReal_le_ofReal (weight_ratio_sq_le k ξ)
  calc ∫⁻ ξ, G ξ
      = ∫⁻ ξ, ((fun ξ => G ξ * ENNReal.ofReal (s ξ / v ξ)) *
          (fun ξ => ENNReal.ofReal (v ξ / s ξ))) ξ := by
        congr 1; funext ξ; exact hsplit ξ
    _ ≤ (∫⁻ ξ, (G ξ * ENNReal.ofReal (s ξ / v ξ)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ξ, ENNReal.ofReal (v ξ / s ξ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hF1m.aemeasurable
          hF2m.aemeasurable
    _ ≤ hsNormSq (k + 2) f ^ (1 / (2 : ℝ)) * ENNReal.ofReal I ^ (1 / (2 : ℝ)) := by
        gcongr
        · exact lintegral_mono hF1
        · rw [hIdef, ofReal_integral_eq_lintegral_ofReal (weight_integrable k)
            (Eventually.of_forall fun ξ => by positivity)]
          exact lintegral_mono hF2
    _ = ENNReal.ofReal (Real.sqrt I) * hsNormSq (k + 2) f ^ (1 / 2 : ℝ) := by
        rw [mul_comm, ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num), Real.sqrt_eq_rpow]

theorem freqL1Norm_le_hsNormSq : ∃ C : ℝ, ∀ f : Space → CSpace,
    freqL1Norm f ≤ ENNReal.ofReal C * hsNormSq 2 f ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le 0
  refine ⟨C, fun f => ?_⟩
  simpa [freqL1Norm] using hC f

theorem freqL1Norm_le_supBound : ∃ C : ℝ, ∀ f : Space → CSpace,
    freqL1Norm f ≤ ENNReal.ofReal C * homNormSq 1 f ^ (1 / 4 : ℝ) * homNormSq 2 f ^ (1 / 4 : ℝ) := by
  exact freqL1_le_supBound

theorem hsNormSq_advectionBilin_le (m : ℕ) : ∃ C : ℝ, ∀ f g : Space → CSpace,
    AEStronglyMeasurable f volume → AEStronglyMeasurable g volume →
      hsNormSq m (advectionBilin f g) ≤
        ENNReal.ofReal C * (freqL1Norm f ^ 2 * hsNormSq (m + 1) g + hsNormSq m f * gradFreqL1Norm g ^ 2) := by
  exact hsNormSq_advection_tame_bound m

theorem advectionSymbol_eq_div {f : Space → CSpace} (hf : IsSolenoidalSymbol f)
    (hm : AEStronglyMeasurable f volume) (h1 : freqL1Norm f < ⊤) (h2 : gradFreqL1Norm f < ⊤)
    (h3 : hsNormSq 1 f < ⊤) (ξ : Space) :
    advectionSymbol f ξ = WithLp.toLp 2 (fun i => 2 * (π : ℂ) * Complex.I *
      ∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ) := by
  have hsub := Measure.measurePreserving_sub_left volume ξ
  have hP : ∀ i j, Integrable (fun η => f η j * f (ξ - η) i) volume := fun i j =>
    (memLp_component hm h3 j).integrable_mul ((memLp_component hm h3 i).comp_measurePreserving hsub)
  have hQ : ∀ i j, Integrable (fun η => ((η j : ℝ) : ℂ) * f η j * f (ξ - η) i) volume := fun i j =>
    (memLp_coord_component hm h3 j).integrable_mul
      ((memLp_component hm h3 i).comp_measurePreserving hsub)
  ext i
  simp only [advectionSymbol, advectionBilin, convC]
  have key : ∀ j, ∫ η, f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) =
      2 * (π : ℂ) * Complex.I * (((ξ j : ℝ) : ℂ) * ∫ η, f η j * f (ξ - η) i) -
        2 * (π : ℂ) * Complex.I * ∫ η, ((η j : ℝ) : ℂ) * f η j * f (ξ - η) i := by
    intro j
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    · congr 1
      ext η
      simp only [PiLp.sub_apply, Complex.ofReal_sub]
      ring
    · exact ((hP i j).const_mul _).const_mul _
    · exact (hQ i j).const_mul _
  have hsum : ∑ j, ∫ η, ((η j : ℝ) : ℂ) * f η j * f (ξ - η) i = 0 := by
    rw [← integral_finsetSum _ (fun j _ => hQ i j)]
    have : (fun η => ∑ j, ((η j : ℝ) : ℂ) * f η j * f (ξ - η) i) = fun _ => 0 := by
      ext η
      rw [← Finset.sum_mul, (hf η).1, zero_mul]
    rw [this, integral_zero]
  simp only [key, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]

end Breakdown.SmoothFlow
