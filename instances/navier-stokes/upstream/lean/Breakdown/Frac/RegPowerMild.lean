import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegAprioriAuxMild

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem pm_powerHeat_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ powerHeatSymbol α τ ξ :=
  (Real.exp_pos _).le

private theorem pm_powerHeat_le_one (α : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Space) :
    powerHeatSymbol α τ ξ ≤ 1 := by
  unfold powerHeatSymbol
  rw [Real.exp_le_one_iff, neg_nonpos]
  have : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  positivity

private theorem pm_rpow_le_exp {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    s ^ p ≤ Real.exp s := by
  have h : s ^ p ≤ 1 + s := by
    rcases le_total s 1 with h | h
    · linarith [Real.rpow_le_one hs h hp0]
    · have h2 := Real.rpow_le_rpow_of_exponent_le h hp1
      rw [Real.rpow_one] at h2
      linarith
  linarith [Real.add_one_le_exp s]

private theorem pm_powerHeat_mul_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    powerHeatSymbol α τ ξ * (2 * π * ‖ξ‖) ≤ τ ^ (-(1 / (2 * α))) := by
  have hr : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have hα0 : 0 < 2 * α := by linarith
  have hp0 : 0 ≤ 1 / (2 * α) := by positivity
  have hp1 : 1 / (2 * α) ≤ 1 := by
    rw [div_le_one hα0]
    linarith
  have hs : 0 ≤ τ * (2 * π * ‖ξ‖) ^ (2 * α) := mul_nonneg hτ.le (Real.rpow_nonneg hr _)
  have key : (2 * π * ‖ξ‖) * τ ^ (1 / (2 * α)) =
      (τ * (2 * π * ‖ξ‖) ^ (2 * α)) ^ (1 / (2 * α)) := by
    rw [Real.mul_rpow hτ.le (Real.rpow_nonneg hr _), ← Real.rpow_mul hr,
      show 2 * α * (1 / (2 * α)) = 1 by field_simp, Real.rpow_one, mul_comm]
  have hτp : 0 < τ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hτ _
  rw [Real.rpow_neg hτ.le, ← one_div, le_div_iff₀ hτp]
  calc powerHeatSymbol α τ ξ * (2 * π * ‖ξ‖) * τ ^ (1 / (2 * α)) =
        Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) *
          (τ * (2 * π * ‖ξ‖) ^ (2 * α)) ^ (1 / (2 * α)) := by
        rw [mul_assoc, key]
        rfl
    _ ≤ Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) * Real.exp (τ * (2 * π * ‖ξ‖) ^ (2 * α)) := by
        gcongr
        exact pm_rpow_le_exp hs hp0 hp1
    _ = 1 := by rw [← Real.exp_add]; simp

private theorem pm_norm_sum_le (x : CSpace) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  calc ‖x‖ = ‖∑ i, EuclideanSpace.single i (x i)‖ := by
        congr 1
        ext j
        simp
    _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by simp [PiLp.norm_single]

private theorem pm_hsNormSq_mono {k m : ℕ} (hk : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f := by
  refine lintegral_mono fun ξ => ?_
  gcongr
  exact pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) hk

private theorem pm_freqVec_apply (ξ : Space) (i : Fin 3) : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

private theorem pm_inner_freqVec (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, pm_freqVec_apply, Complex.conj_ofReal, mul_comm]

private theorem pm_sum_sq_ofReal (ξ : Space) :
    ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  push_cast
  ring

private theorem pm_inner_freqVec_projC (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) (divFreeC ξ z) = 0 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 : freqVec 0 = 0 := by
      ext i
      simp [pm_freqVec_apply]
    rw [h0, inner_zero_left]
  have hn : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  unfold divFreeC
  rw [inner_sub_right, inner_smul_right, pm_inner_freqVec, pm_inner_freqVec]
  simp only [pm_freqVec_apply]
  rw [pm_sum_sq_ofReal]
  have hc : (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖ξ‖ ^ 2 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
  linear_combination (-(∑ k, ((ξ k : ℝ) : ℂ) * z k)) * hc

private theorem pm_norm_projC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ ≤ ‖z‖ := by
  set c : ℂ := (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i with hcdef
  have hz : divFreeC ξ z + c • freqVec ξ = z := by
    show z - c • freqVec ξ + c • freqVec ξ = z
    rw [sub_add_cancel]
  have horth : inner ℂ (divFreeC ξ z) (c • freqVec ξ) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, pm_inner_freqVec_projC, map_zero, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hz] at h
  have hsq : ‖divFreeC ξ z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [h, mul_self_nonneg ‖c • freqVec ξ‖]
  nlinarith [norm_nonneg (divFreeC ξ z), norm_nonneg z]

private theorem pm_enorm_advectionSymbol_le {f : Space → CSpace} (hf : IsSolenoidalSymbol f)
    (hm : AEStronglyMeasurable f volume) (h1 : freqL1Norm f < ⊤) (h2 : gradFreqL1Norm f < ⊤)
    (h3 : hsNormSq 1 f < ⊤) (ξ : Space) :
    ‖advectionSymbol f ξ‖ₑ ≤ ENNReal.ofReal (2 * π * ‖ξ‖) * convEnormSum f ξ := by
  rw [advectionSymbol_eq_div hf hm h1 h2 h3 ξ, ← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (q := 2 * π * ‖ξ‖ *
    ∑ i, ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖) ?_).trans (le_of_eq ?_)
  · refine (pm_norm_sum_le _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖2 * (π : ℂ) * Complex.I * ∑ j, ((ξ j : ℝ) : ℂ) *
            convC (fun η => f η j) (fun η => f η i) ξ‖ =
          2 * π * ‖∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          rw [norm_mul]
          simp [abs_of_pos pi_pos]
      _ ≤ 2 * π * ∑ j, ‖ξ‖ * ‖convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, Complex.norm_real]
          gcongr
          exact PiLp.norm_apply_le ξ j
      _ = 2 * π * ‖ξ‖ * ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  · rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simp only [ofReal_norm]

private theorem pm_enorm_mild_le {α : ℝ} {F : ℝ → Space → CSpace} {T t : ℝ}
    (hD : IsPowerMildSymbol α F 0 T) (ht : t ∈ Icc 0 T) (ξ : Space) :
    ‖F t ξ‖ₑ ≤ ‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
      ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖nonlinSymbol (F s) ξ‖ₑ := by
  rw [hD t ht ξ]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [enorm_smul]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (pm_powerHeat_nonneg _ _ _)]
    exact ENNReal.ofReal_le_one.mpr (pm_powerHeat_le_one α (by simpa using ht.1) ξ)
  · rw [intervalIntegral.integral_of_le ht.1]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine lintegral_mono fun s => ?_
    rw [enorm_smul, ← ofReal_norm (((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ)), Complex.norm_real,
      Real.norm_of_nonneg (pm_powerHeat_nonneg _ _ _)]

theorem powerEnormMild (α : ℝ) (hα : 1 < α) : PowerEnormMildStatement α := by
  intro m hm
  obtain ⟨C1, hC1⟩ := weightedFreqL1_le 1
  obtain ⟨C0, hC0⟩ := weightedFreqL1_le 0
  refine ⟨1, zero_le_one, fun T F t hF hD hS ht ξ => ?_⟩
  refine (pm_enorm_mild_le hD ht ξ).trans (add_le_add le_rfl ?_)
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  obtain ⟨hmeas, hfin⟩ := hF.1 s hsT
  have hτ : 0 < t - s := sub_pos.mpr hs.2
  have hmono : ∀ k, k ≤ m → hsNormSq k (F s) < ⊤ := fun k hk =>
    lt_of_le_of_lt (pm_hsNormSq_mono hk _) hfin
  have hW : freqL1Norm (F s) < ⊤ := by
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C0))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hmono 2 (by omega)).ne))
    refine le_trans (lintegral_mono fun ξ => ?_) (hC0 (F s))
    simp
  have hG : gradFreqL1Norm (F s) < ⊤ := by
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C1))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hmono 3 (by omega)).ne))
    refine le_trans (lintegral_mono fun ξ => ?_) (hC1 (F s))
    gcongr
    simp
  rw [one_mul, nonlinSymbol, enorm_neg]
  calc ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖divFreeC ξ (advectionSymbol (F s) ξ)‖ₑ ≤
        ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖advectionSymbol (F s) ξ‖ₑ := by
        gcongr
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (pm_norm_projC_le _ _)
    _ ≤ ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) *
        (ENNReal.ofReal (2 * π * ‖ξ‖) * convEnormSum (F s) ξ) := by
        gcongr
        exact pm_enorm_advectionSymbol_le (hS s hsT) hmeas hW hG (hmono 1 (by omega)) ξ
    _ = ENNReal.ofReal (powerHeatSymbol α (t - s) ξ * (2 * π * ‖ξ‖)) * convEnormSum (F s) ξ := by
        rw [ENNReal.ofReal_mul (pm_powerHeat_nonneg _ _ _), ← mul_assoc]
    _ ≤ _ := by
        gcongr
        exact pm_powerHeat_mul_le hα hτ ξ

private theorem pm_lintegral_weighted_const_mul_sq (w k : Space → ℝ≥0∞) (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    (∫⁻ ξ, w ξ * (A * k ξ) ^ 2) ^ (1 / 2 : ℝ) = A * (∫⁻ ξ, w ξ * k ξ ^ 2) ^ (1 / 2 : ℝ) := by
  have e : ∀ ξ, w ξ * (A * k ξ) ^ 2 = A ^ 2 * (w ξ * k ξ ^ 2) := fun ξ => by ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hA),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem powerHsMild_of (α : ℝ) (hα : 1 < α) (h1 : PowerEnormMildStatement α) :
    PowerHsMildStatement α := by
  intro m hm
  obtain ⟨c, hc0, hc⟩ := h1 m hm
  obtain ⟨CY, hCY0, hY⟩ := convEnormSum_weighted_le m
  refine ⟨c * CY, fun T F hF hD hS t ht => ?_⟩
  have hpt := hc T F t hF hD hS ht
  have hw : Measurable fun ξ : Space => ENNReal.ofReal (hsWeight m ξ) := by
    unfold hsWeight
    fun_prop
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have ha : AEMeasurable (fun ξ => ‖F 0 ξ‖ₑ) volume := (hF.1 0 h0).1.enorm
  have hk := aemeasurable_convEnormSum_curve hm hF ht
  have hg : AEMeasurable (Function.uncurry fun s ξ =>
      ENNReal.ofReal (c * (t - s) ^ (-(1 / (2 * α)))) * convEnormSum (F s) ξ)
      ((volume.restrict (Ioo 0 t)).prod volume) := by
    refine AEMeasurable.mul ?_ hk
    refine Measurable.aemeasurable ?_
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.sub measurable_fst).pow_const _)
  have h1' : hsNormSq m (F t) ≤ ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) *
      (‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
        ENNReal.ofReal (c * (t - s) ^ (-(1 / (2 * α)))) * convEnormSum (F s) ξ) ^ 2 := by
    refine lintegral_mono fun ξ => ?_
    gcongr
    exact hpt ξ
  refine (ENNReal.rpow_le_rpow h1' (by norm_num)).trans ?_
  refine (lintegral_weighted_add_lintegral_sq_le hw ha hg).trans ?_
  refine add_le_add le_rfl ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  rw [pm_lintegral_weighted_const_mul_sq _ _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (c * (t - s) ^ (-(1 / (2 * α)))) *
        (ENNReal.ofReal CY * freqL1Norm (F s) * hsNormSq m (F s) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact hY (F s) (hF.1 s hsT).1
    _ = _ := by
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0]
        ring

end Breakdown.SmoothFlow
