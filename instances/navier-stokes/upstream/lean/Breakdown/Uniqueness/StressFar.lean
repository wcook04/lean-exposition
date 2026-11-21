import Breakdown.Uniqueness.StressSplit
import Breakdown.Uniqueness.ProductBound
import Breakdown.Uniqueness.CutoffBounds
import Breakdown.Uniqueness.FundSolKernel
import Breakdown.Uniqueness.StressFarAux3

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem far_stress_le : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      |∫ x, ∑ i, ∑ j, w x i * w x j *
          (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) *
            ((radialCutoff r y ^ 3 - radialCutoff r x ^ 3) * cutoffFlux r w y))| ≤
        c * (A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) + A ^ 3 * r ^ (-(5 / 2) : ℝ)) := by
  obtain ⟨c₁, hc₁⟩ := abs_radialCutoff_sub_le
  obtain ⟨c₂, hc₂⟩ := norm_fderiv_radialCutoff_le
  set d₁ := max c₁ 0 with hd₁
  set d₂ := max c₂ 0 with hd₂
  have hd₁0 : 0 ≤ d₁ := le_max_right _ _
  have hd₂0 : 0 ≤ d₂ := le_max_right _ _
  set k₁ : ℝ := (20 * π / 3) ^ (5 / 6 : ℝ) with hk₁
  set k₃ : ℝ := (4 * π / 3) ^ (1 / 2 : ℝ) with hk₃
  have hk₁0 : 0 ≤ k₁ := by positivity
  have hk₃0 : 0 ≤ k₃ := by positivity
  refine ⟨36 * (3 * d₁ * k₁ * d₂ + k₃ * d₂), ?_⟩
  intro A w hw r hr1
  have hr : 0 < r := by linarith
  have hA := hw.nonneg
  set η := radialCutoff r with hη
  set γ := cutoffFlux r w with hγ
  set S := cutoffSixthNorm r w with hS
  have hηc : Continuous η := (contDiff_radialCutoff hr).continuous
  have hwc : Continuous w := hw.smooth.continuous
  have hγc : Continuous γ :=
    ((contDiff_radialCutoff hr).continuous_fderiv (by simp)).clm_apply hwc
  have hslope : ∀ x y, |η x - η y| ≤ d₁ * ‖x - y‖ / r := by
    intro x y
    refine (hc₁ r hr x y).trans ?_
    gcongr
    exact le_max_left _ _
  have hg : ∀ y, |γ y| ≤ d₂ / r * ‖w y‖ := by
    intro y
    have h1 : |γ y| ≤ ‖fderiv ℝ (radialCutoff r) y‖ * ‖w y‖ := by
      rw [← Real.norm_eq_abs]
      exact ContinuousLinearMap.le_opNorm _ _
    refine h1.trans ?_
    gcongr
    exact (hc₂ r hr y).trans (by gcongr; exact le_max_left _ _)
  have hint : Integrable (fun x => (η x ^ 2 * ‖w x‖) ^ 6) volume := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine (hasCompactSupport_radialCutoff hr).mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [η, h0]
  have hI0 : 0 ≤ ∫ x, (η x ^ 2 * ‖w x‖) ^ 6 := integral_nonneg fun x => by positivity
  have hS0 : 0 ≤ S := Real.rpow_nonneg hI0 _
  have hS6 : ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖w x‖) ^ (6 : ℝ) ≤ ENNReal.ofReal (S ^ 6) := by
    apply le_of_eq
    have e1 : ∀ x, ENNReal.ofReal (η x ^ 2 * ‖w x‖) ^ (6 : ℝ) =
        ENNReal.ofReal ((η x ^ 2 * ‖w x‖) ^ 6) := fun x =>
      Internal.FarStress.ofReal_rpow_six_eq (by positivity)
    simp only [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
    congr 1
    rw [hS, cutoffSixthNorm, ← Real.rpow_natCast, ← Real.rpow_mul hI0]
    norm_num
  have hbase := Internal.FarStress.far_base_le (e := η) (g := γ) hr hA hd₁0 hS0 hwc hηc hγc
    (radialCutoff_nonneg r) (radialCutoff_le_one r) hslope hg hw.energy hS6 hd₂0
  set H : Space → ℝ≥0∞ := fun x =>
    ∫⁻ y, ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |η y ^ 3 - η x ^ 3|) * ENNReal.ofReal |γ y| with hH
  have hpt : ∀ x, ‖∑ i, ∑ j, w x i * w x j *
      (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * ((η y ^ 3 - η x ^ 3) * γ y))‖ₑ ≤
      36 * (ENNReal.ofReal (‖w x‖ ^ 2) * H x) := by
    intro x
    have hterm : ∀ i j, ‖w x i * w x j *
        (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * ((η y ^ 3 - η x ^ 3) * γ y))‖ₑ ≤
        4 * (ENNReal.ofReal (‖w x‖ ^ 2) * H x) := by
      intro i j
      have hI : ‖∫ y, FundSol.kernelSecondDeriv i j (x - y) * ((η y ^ 3 - η x ^ 3) * γ y)‖ₑ ≤ H x := by
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul, abs_mul, ← mul_assoc]
        gcongr
        exact FundSol.abs_kernelSecondDeriv_le i j (x - y)
      have hw2 : ‖w x i * w x j‖ₑ ≤ ENNReal.ofReal (‖w x‖ ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul, sq]
        exact mul_le_mul (PiLp.norm_apply_le (w x) i) (PiLp.norm_apply_le (w x) j)
          (abs_nonneg _) (norm_nonneg _)
      rw [enorm_mul (a := w x i * w x j), enorm_mul (a := (4 : ℝ))]
      have h4 : ‖(4 : ℝ)‖ₑ = 4 := by
        rw [Real.enorm_eq_ofReal_abs]
        norm_num
      rw [h4]
      calc ‖w x i * w x j‖ₑ * (4 * ‖∫ y, FundSol.kernelSecondDeriv i j (x - y) *
            ((η y ^ 3 - η x ^ 3) * γ y)‖ₑ) ≤ ENNReal.ofReal (‖w x‖ ^ 2) * (4 * H x) := by
            gcongr
        _ = 4 * (ENNReal.ofReal (‖w x‖ ^ 2) * H x) := by ring
    refine (enorm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => enorm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring_nf
    rfl
  set R : ℝ := A ^ 2 * (3 / 2 * d₁ / r * ((20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
      (d₂ * S / r)) + (4 * π / 3 * r⁻¹ ^ 3) ^ (1 / 2 : ℝ) * (d₂ * A / r)) +
      3 / 2 * d₁ / r * (S * A * (20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) * (d₂ * A / r))
    with hR
  have hR0 : 0 ≤ R := by positivity
  have hconv : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) * H x ≤ ENNReal.ofReal R := by
    refine hbase.trans (le_of_eq ?_)
    rw [hR]
    simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul,
      ← ENNReal.ofReal_rpow_of_nonneg]
  have hlin : ∫⁻ x, ‖∑ i, ∑ j, w x i * w x j *
      (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * ((η y ^ 3 - η x ^ 3) * γ y))‖ₑ ≤
      ENNReal.ofReal (36 * R) := by
    calc _ ≤ ∫⁻ x, 36 * (ENNReal.ofReal (‖w x‖ ^ 2) * H x) := lintegral_mono fun x => hpt x
      _ = 36 * ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) * H x := lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 36 * ENNReal.ofReal R := by gcongr
      _ = ENNReal.ofReal (36 * R) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hmain : |∫ x, ∑ i, ∑ j, w x i * w x j *
      (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * ((η y ^ 3 - η x ^ 3) * γ y))| ≤ 36 * R := by
    rw [← Real.norm_eq_abs, ← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_norm]
    exact (enorm_integral_le_lintegral_enorm _).trans hlin
  refine hmain.trans ?_
  set t : ℝ := r ^ (1 / 2 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hr _
  have htr : t ^ 2 = r := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hP1 : (20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) = k₁ * t := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr.le]
    norm_num
    rw [hk₁, ht]
  have hP3 : (4 * π / 3 * r⁻¹ ^ 3) ^ (1 / 2 : ℝ) = k₃ * (t ^ 3)⁻¹ := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← htr, ← Real.sqrt_eq_rpow]
    rw [show ((t ^ 2)⁻¹ ^ 3 : ℝ) = ((t ^ 3)⁻¹) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hm32 : r ^ (-(3 / 2) : ℝ) = (t ^ 3)⁻¹ := by
    rw [Real.rpow_neg hr.le, ht, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hm52 : r ^ (-(5 / 2) : ℝ) = (t ^ 5)⁻¹ := by
    rw [Real.rpow_neg hr.le, ht, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hReq : 36 * R = 36 * (3 * d₁ * k₁ * d₂) * (A ^ 2 * S * (t ^ 3)⁻¹) +
      36 * (k₃ * d₂) * (A ^ 3 * (t ^ 5)⁻¹) := by
    rw [hR, hP1, hP3, ← htr]
    field_simp
    ring
  rw [hReq, hm32, hm52]
  have hX : 0 ≤ A ^ 2 * S * (t ^ 3)⁻¹ := by positivity
  have hY : 0 ≤ A ^ 3 * (t ^ 5)⁻¹ := by positivity
  have hα : 0 ≤ 36 * (3 * d₁ * k₁ * d₂) := by positivity
  have hβ : 0 ≤ 36 * (k₃ * d₂) := by positivity
  nlinarith [mul_nonneg hα hY, mul_nonneg hβ hX]

end Breakdown
