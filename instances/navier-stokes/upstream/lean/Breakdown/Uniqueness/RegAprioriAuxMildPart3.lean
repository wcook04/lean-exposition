import Breakdown.Uniqueness.RegAprioriAuxMildPart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem one_add_norm_pow_le (m : ℕ) (ξ η : Space) :
    (1 + ‖ξ‖) ^ m ≤ 2 ^ m * ((1 + ‖η‖) ^ m + (1 + ‖ξ - η‖) ^ m) := by
  have h1 : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    have := norm_add_le η (ξ - η)
    rwa [add_sub_cancel] at this
  have hM : 1 + ‖ξ‖ ≤ 2 * max (1 + ‖η‖) (1 + ‖ξ - η‖) := by
    have := le_max_left (1 + ‖η‖) (1 + ‖ξ - η‖)
    have := le_max_right (1 + ‖η‖) (1 + ‖ξ - η‖)
    linarith [norm_nonneg η, norm_nonneg (ξ - η)]
  have hp1 : (0 : ℝ) ≤ (1 + ‖η‖) ^ m := by positivity
  have hp2 : (0 : ℝ) ≤ (1 + ‖ξ - η‖) ^ m := by positivity
  calc (1 + ‖ξ‖) ^ m ≤ (2 * max (1 + ‖η‖) (1 + ‖ξ - η‖)) ^ m :=
        pow_le_pow_left₀ (by positivity) hM m
    _ = 2 ^ m * max (1 + ‖η‖) (1 + ‖ξ - η‖) ^ m := mul_pow _ _ _
    _ ≤ _ := by
      gcongr
      rcases le_total (1 + ‖η‖) (1 + ‖ξ - η‖) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith

private theorem hsWeight_le_sq (m : ℕ) (ξ : Space) : hsWeight m ξ ≤ ((1 + ‖ξ‖) ^ m) ^ 2 := by
  unfold hsWeight
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg ξ]) m

private theorem sq_le_hsWeight (m : ℕ) (ξ : Space) :
    ((1 + ‖ξ‖) ^ m) ^ 2 ≤ 2 ^ m * hsWeight m ξ := by
  unfold hsWeight
  rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]) m

private theorem lintegral_weight_conv_sq_le (m : ℕ) {a : Space → ℝ≥0∞} (ha : Measurable a) :
    ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * (∫⁻ η, a η * a (ξ - η)) ^ 2 ≤
      8 ^ (m + 1) * (∫⁻ η, a η) ^ 2 * ∫⁻ η, ENNReal.ofReal (hsWeight m η) * a η ^ 2 := by
  set s : Space → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ m) with hs_def
  have hs : Measurable s := by
    simp only [hs_def]
    fun_prop
  set v : Space → ℝ≥0∞ := fun η => s η * a η with hv_def
  have hv : Measurable v := hs.mul ha
  set W := ∫⁻ η, a η with hW
  have hsub : ∀ ξ, Measurable fun η : Space => ξ - η := fun ξ => measurable_const.sub measurable_id
  have hA : ∀ ξ, s ξ * ∫⁻ η, a η * a (ξ - η) ≤ 2 ^ (m + 1) * ∫⁻ η, v η * a (ξ - η) := by
    intro ξ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsym : ∫⁻ η, a η * v (ξ - η) = ∫⁻ η, v η * a (ξ - η) := by
      have := lintegral_sub_left_eq_self (μ := volume) (fun η => a η * v (ξ - η)) ξ
      simp only [sub_sub_cancel] at this
      rw [← this]
      refine lintegral_congr fun η => ?_
      ring
    calc ∫⁻ η, s ξ * (a η * a (ξ - η)) ≤
          ∫⁻ η, 2 ^ m * (v η * a (ξ - η)) + 2 ^ m * (a η * v (ξ - η)) := by
          refine lintegral_mono fun η => ?_
          have h := one_add_norm_pow_le m ξ η
          have h' : s ξ ≤ 2 ^ m * (s η + s (ξ - η)) := by
            simp only [hs_def]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              show (2 : ℝ≥0∞) ^ m = ENNReal.ofReal (2 ^ m) by simp,
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal h
          calc s ξ * (a η * a (ξ - η)) ≤ 2 ^ m * (s η + s (ξ - η)) * (a η * a (ξ - η)) := by
                gcongr
            _ = _ := by simp only [hv_def]; ring
      _ = 2 ^ m * (∫⁻ η, v η * a (ξ - η)) + 2 ^ m * ∫⁻ η, a η * v (ξ - η) := by
          have m1 : Measurable fun η => v η * a (ξ - η) := by fun_prop
          have m2 : Measurable fun η => a η * v (ξ - η) := by fun_prop
          rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1, lintegral_const_mul _ m2]
      _ = 2 ^ (m + 1) * ∫⁻ η, v η * a (ξ - η) := by
          rw [hsym]
          ring
  have hC : ∀ ξ, (∫⁻ η, v η * a (ξ - η)) ^ 2 ≤ W * ∫⁻ η, a (ξ - η) * v η ^ 2 := by
    intro ξ
    have hm1 : Measurable fun η => a (ξ - η) := ha.comp (hsub ξ)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      (hm1.pow_const (1 / 2 : ℝ)).aemeasurable ((hm1.pow_const (1 / 2 : ℝ)).mul hv).aemeasurable
    have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_mul]; norm_num
    have hhalf : ∀ x : ℝ≥0∞, x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
    simp only [Pi.mul_apply, ← mul_assoc, hhalf, hsq, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
      ENNReal.rpow_two] at h
    rw [lintegral_sub_left_eq_self a ξ] at h
    have e1 : ∫⁻ η, v η * a (ξ - η) = ∫⁻ η, a (ξ - η) * v η :=
      lintegral_congr fun η => mul_comm _ _
    calc (∫⁻ η, v η * a (ξ - η)) ^ 2 ≤ (W ^ (1 / 2 : ℝ) * (∫⁻ η, a (ξ - η) * v η ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [e1]
          gcongr ?_ ^ 2
      _ = W * ∫⁻ η, a (ξ - η) * v η ^ 2 := by
          rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
  have hD : ∫⁻ ξ, ∫⁻ η, a (ξ - η) * v η ^ 2 = W * ∫⁻ η, v η ^ 2 := by
    rw [lintegral_lintegral_swap]
    · rw [← lintegral_const_mul]
      · refine lintegral_congr fun η => ?_
        rw [lintegral_mul_const (v η ^ 2) (f := fun x => a (x - η)) (by fun_prop),
          lintegral_sub_right_eq_self a η]
      · exact hv.pow_const 2
    · exact ((ha.comp (measurable_fst.sub measurable_snd)).mul ((hv.comp measurable_snd).pow_const 2)).aemeasurable
  have hv2 : ∫⁻ η, v η ^ 2 ≤ 2 ^ m * ∫⁻ η, ENNReal.ofReal (hsWeight m η) * a η ^ 2 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
    refine lintegral_mono fun η => ?_
    simp only [hv_def, hs_def]
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
      show (2 : ℝ≥0∞) ^ m = ENNReal.ofReal (2 ^ m) by simp, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact sq_le_hsWeight m η
  calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * (∫⁻ η, a η * a (ξ - η)) ^ 2
        ≤ ∫⁻ ξ, 4 ^ (m + 1) * (W * ∫⁻ η, a (ξ - η) * v η ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        have hw : ENNReal.ofReal (hsWeight m ξ) ≤ s ξ ^ 2 := by
          simp only [hs_def]
          rw [← ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hsWeight_le_sq m ξ)
        calc ENNReal.ofReal (hsWeight m ξ) * (∫⁻ η, a η * a (ξ - η)) ^ 2
            ≤ (s ξ * ∫⁻ η, a η * a (ξ - η)) ^ 2 := by rw [mul_pow]; gcongr
          _ ≤ (2 ^ (m + 1) * ∫⁻ η, v η * a (ξ - η)) ^ 2 := by gcongr ?_ ^ 2; exact hA ξ
          _ = 4 ^ (m + 1) * (∫⁻ η, v η * a (ξ - η)) ^ 2 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
            norm_num
          _ ≤ _ := by gcongr; exact hC ξ
    _ = 4 ^ (m + 1) * (W * (W * ∫⁻ η, v η ^ 2)) := by
        have hG : Measurable fun ξ => ∫⁻ η, a (ξ - η) * v η ^ 2 :=
          ((ha.comp (measurable_fst.sub measurable_snd)).mul
            ((hv.comp measurable_snd).pow_const 2)).lintegral_prod_right'
        rw [lintegral_const_mul _ (hG.const_mul _), lintegral_const_mul _ hG, hD]
    _ ≤ 4 ^ (m + 1) * (W * (W * (2 ^ m * ∫⁻ η, ENNReal.ofReal (hsWeight m η) * a η ^ 2))) := by
        gcongr
    _ ≤ _ := by
        have h84 : (4 : ℝ≥0∞) ^ (m + 1) * 2 ^ m ≤ 8 ^ (m + 1) := by
          rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, mul_pow]
          gcongr
          · norm_num
          · omega
        calc _ = (4 ^ (m + 1) * 2 ^ m) * W ^ 2 * ∫⁻ η, ENNReal.ofReal (hsWeight m η) * a η ^ 2 := by
              ring
          _ ≤ _ := by gcongr

theorem convEnormSum_weighted_le (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space → CSpace,
    AEStronglyMeasurable f volume →
    (∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * convEnormSum f ξ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal C * freqL1Norm f * hsNormSq m f ^ (1 / 2 : ℝ) := by
  refine ⟨9 * 3 ^ (m + 1), by positivity, fun f hf => ?_⟩
  set g := hf.mk f
  have hg : Measurable fun η => ‖g η‖ₑ := hf.stronglyMeasurable_mk.measurable.enorm
  have hfg : f =ᵐ[volume] g := hf.ae_eq_mk
  have hpt : ∀ ξ, convEnormSum f ξ ≤ 9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
    intro ξ
    have hsh : (fun η => f (ξ - η)) =ᵐ[volume] fun η => g (ξ - η) :=
      (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq hfg
    have hij : ∀ i j : Fin 3, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ₑ ≤
        ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
      intro i j
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      calc ∫⁻ η, ‖f η j * f (ξ - η) i‖ₑ ≤ ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ := by
            refine lintegral_mono fun η => ?_
            rw [enorm_mul]
            exact mul_le_mul' (PiLp.enorm_apply_le _ _) (PiLp.enorm_apply_le _ _)
        _ = ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hfg, hsh] with η h1 h2
            rw [h1, h2]
    calc convEnormSum f ξ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = 9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
          ring
  have hW : freqL1Norm f = ∫⁻ η, ‖g η‖ₑ := by
    unfold freqL1Norm
    refine lintegral_congr_ae ?_
    filter_upwards [hfg] with η h
    rw [h]
  have hZ : hsNormSq m f = ∫⁻ η, ENNReal.ofReal (hsWeight m η) * ‖g η‖ₑ ^ 2 := by
    unfold hsNormSq
    refine lintegral_congr_ae ?_
    filter_upwards [hfg] with η h
    rw [h]
  have hbase := lintegral_weight_conv_sq_le m hg
  have hbound : ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * convEnormSum f ξ ^ 2 ≤
      (ENNReal.ofReal (9 * 3 ^ (m + 1)) * freqL1Norm f) ^ 2 * hsNormSq m f := by
    calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * convEnormSum f ξ ^ 2
        ≤ ∫⁻ ξ, 81 * (ENNReal.ofReal (hsWeight m ξ) *
            (∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2) := by
          refine lintegral_mono fun ξ => ?_
          calc ENNReal.ofReal (hsWeight m ξ) * convEnormSum f ξ ^ 2
              ≤ ENNReal.ofReal (hsWeight m ξ) * (9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2 := by
                gcongr
                exact hpt ξ
            _ = _ := by ring
      _ = 81 * ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * (∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2 :=
          lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 81 * (8 ^ (m + 1) * (∫⁻ η, ‖g η‖ₑ) ^ 2 *
            ∫⁻ η, ENNReal.ofReal (hsWeight m η) * ‖g η‖ₑ ^ 2) := by gcongr
      _ ≤ _ := by
          rw [hW, hZ, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
          have h89 : (8 : ℝ≥0∞) ^ (m + 1) ≤ 9 ^ (m + 1) := by
            gcongr
            norm_num
          calc 81 * (8 ^ (m + 1) * (∫⁻ η, ‖g η‖ₑ) ^ 2 *
                ∫⁻ η, ENNReal.ofReal (hsWeight m η) * ‖g η‖ₑ ^ 2)
              ≤ 81 * (9 ^ (m + 1) * (∫⁻ η, ‖g η‖ₑ) ^ 2 *
                ∫⁻ η, ENNReal.ofReal (hsWeight m η) * ‖g η‖ₑ ^ 2) := by gcongr
            _ = _ := by
              rw [show (9 : ℝ≥0∞) ^ (m + 1) = (3 ^ (m + 1)) ^ 2 by
                rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
              norm_num
              ring
  calc (∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * convEnormSum f ξ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal (9 * 3 ^ (m + 1)) * freqL1Norm f) ^ 2 * hsNormSq m f) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end Breakdown.SmoothFlow
