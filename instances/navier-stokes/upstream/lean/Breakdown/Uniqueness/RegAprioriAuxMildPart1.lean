import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def convEnormSum (f : Space → CSpace) (ξ : Space) : ℝ≥0∞ :=
  ∑ i, ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ₑ

private theorem heatSymbol_le_one {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Space) : heatSymbol τ ξ ≤ 1 := by
  unfold heatSymbol
  rw [Real.exp_le_one_iff, neg_nonpos]
  positivity

private theorem heatSymbol_nonneg' (τ : ℝ) (ξ : Space) : 0 ≤ heatSymbol τ ξ :=
  (Real.exp_pos _).le

private theorem heatSymbol_mul_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    heatSymbol τ ξ * (2 * π * ‖ξ‖) ≤ τ ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hpow : τ ^ (-(1 / 2 : ℝ)) = (Real.sqrt τ)⁻¹ := by
    rw [Real.rpow_neg hτ.le, Real.sqrt_eq_rpow]
  rw [hpow, inv_eq_one_div, le_div_iff₀ hs]
  have hy : 0 ≤ 2 * π * ‖ξ‖ * Real.sqrt τ := by positivity
  have hexp : heatSymbol τ ξ = Real.exp (-((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2)) := by
    unfold heatSymbol
    congr 1
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hτ.le]
    ring
  have h1 : 2 * π * ‖ξ‖ * Real.sqrt τ ≤ Real.exp ((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2) := by
    nlinarith [Real.add_one_le_exp ((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2),
      sq_nonneg (2 * π * ‖ξ‖ * Real.sqrt τ - 1)]
  calc heatSymbol τ ξ * (2 * π * ‖ξ‖) * Real.sqrt τ =
        Real.exp (-((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2)) * (2 * π * ‖ξ‖ * Real.sqrt τ) := by
        rw [hexp]
        ring
    _ ≤ Real.exp (-((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2)) *
        Real.exp ((2 * π * ‖ξ‖ * Real.sqrt τ) ^ 2) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

private theorem norm_sum_le_of_l2 (x : CSpace) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  calc ‖x‖ = ‖∑ i, EuclideanSpace.single i (x i)‖ := by
        congr 1
        ext j
        simp
    _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by simp [PiLp.norm_single]

private theorem hsNormSq_mono {k m : ℕ} (hk : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f := by
  refine lintegral_mono fun ξ => ?_
  gcongr
  exact pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) hk

private theorem freqVec_apply' (ξ : Space) (i : Fin 3) : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

private theorem inner_freqVec' (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, freqVec_apply', Complex.conj_ofReal, mul_comm]

private theorem sum_sq_ofReal (ξ : Space) :
    ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  push_cast
  ring

private theorem inner_freqVec_divFreeC (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) (divFreeC ξ z) = 0 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 : freqVec 0 = 0 := by
      ext i
      simp [freqVec_apply']
    rw [h0, inner_zero_left]
  have hn : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  unfold divFreeC
  rw [inner_sub_right, inner_smul_right, inner_freqVec', inner_freqVec']
  simp only [freqVec_apply']
  rw [sum_sq_ofReal]
  have hc : (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖ξ‖ ^ 2 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
  linear_combination (-(∑ k, ((ξ k : ℝ) : ℂ) * z k)) * hc

private theorem norm_divFreeC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ ≤ ‖z‖ := by
  set c : ℂ := (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i with hcdef
  have hz : divFreeC ξ z + c • freqVec ξ = z := by
    show z - c • freqVec ξ + c • freqVec ξ = z
    rw [sub_add_cancel]
  have horth : inner ℂ (divFreeC ξ z) (c • freqVec ξ) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, inner_freqVec_divFreeC, map_zero, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hz] at h
  have hsq : ‖divFreeC ξ z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [h, mul_self_nonneg ‖c • freqVec ξ‖]
  nlinarith [norm_nonneg (divFreeC ξ z), norm_nonneg z]


private theorem enorm_advectionSymbol_le {f : Space → CSpace} (hf : IsSolenoidalSymbol f)
    (hm : AEStronglyMeasurable f volume) (h1 : freqL1Norm f < ⊤) (h2 : gradFreqL1Norm f < ⊤)
    (h3 : hsNormSq 1 f < ⊤) (ξ : Space) :
    ‖advectionSymbol f ξ‖ₑ ≤ ENNReal.ofReal (2 * π * ‖ξ‖) * convEnormSum f ξ := by
  rw [advectionSymbol_eq_div hf hm h1 h2 h3 ξ, ← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (q := 2 * π * ‖ξ‖ *
    ∑ i, ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖) ?_).trans (le_of_eq ?_)
  · refine (norm_sum_le_of_l2 _).trans ?_
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

private theorem enorm_varConst_le {F : ℝ → Space → CSpace} {T t : ℝ} (hD : IsVarConstSymbol F 0 T)
    (ht : t ∈ Icc 0 T) (ξ : Space) :
    ‖F t ξ‖ₑ ≤ ‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
      ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖nonlinSymbol (F s) ξ‖ₑ := by
  rw [hD t ht ξ]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [enorm_smul]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg' _ _)]
    exact ENNReal.ofReal_le_one.mpr (heatSymbol_le_one (by simpa using ht.1) ξ)
  · rw [intervalIntegral.integral_of_le ht.1]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine lintegral_mono fun s => ?_
    rw [enorm_smul, ← ofReal_norm (((heatSymbol (t - s) ξ : ℝ) : ℂ)), Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg' _ _)]

theorem enorm_mild_le (m : ℕ) (hm : 3 ≤ m) : ∃ c : ℝ, 0 ≤ c ∧
    ∀ (T : ℝ) (F : ℝ → Space → CSpace) (t : ℝ), IsHsCurve m F 0 T → IsVarConstSymbol F 0 T →
      (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → t ∈ Icc 0 T → ∀ ξ,
      ‖F t ξ‖ₑ ≤ ‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
        ENNReal.ofReal (c * (t - s) ^ (-(1 / 2 : ℝ))) * convEnormSum (F s) ξ := by
  obtain ⟨C1, hC1⟩ := weightedFreqL1_le 1
  obtain ⟨C0, hC0⟩ := weightedFreqL1_le 0
  refine ⟨1, zero_le_one, fun T F t hF hD hS ht ξ => ?_⟩
  refine (enorm_varConst_le hD ht ξ).trans (add_le_add le_rfl ?_)
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  obtain ⟨hmeas, hfin⟩ := hF.1 s hsT
  have hτ : 0 < t - s := sub_pos.mpr hs.2
  have hmono : ∀ k, k ≤ m → hsNormSq k (F s) < ⊤ := fun k hk =>
    lt_of_le_of_lt (hsNormSq_mono hk _) hfin
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
  calc ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖divFreeC ξ (advectionSymbol (F s) ξ)‖ₑ ≤
        ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖advectionSymbol (F s) ξ‖ₑ := by
        gcongr
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_divFreeC_le _ _)
    _ ≤ ENNReal.ofReal (heatSymbol (t - s) ξ) *
        (ENNReal.ofReal (2 * π * ‖ξ‖) * convEnormSum (F s) ξ) := by
        gcongr
        exact enorm_advectionSymbol_le (hS s hsT) hmeas hW hG (hmono 1 (by omega)) ξ
    _ = ENNReal.ofReal (heatSymbol (t - s) ξ * (2 * π * ‖ξ‖)) * convEnormSum (F s) ξ := by
        rw [ENNReal.ofReal_mul (heatSymbol_nonneg' _ _), ← mul_assoc]
    _ ≤ _ := by
        gcongr
        exact heatSymbol_mul_le hτ ξ

end Breakdown.SmoothFlow
