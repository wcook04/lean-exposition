import Breakdown.Uniqueness.RegPersistAuxDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem pow_mul_exp_neg_le {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    v ^ n * Real.exp (-v) ≤ (n.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := v) hv n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

private theorem heat_gain_base {T τ x : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T) (hx : 0 ≤ x) :
    x ^ 2 * (1 + x) * Real.exp (-(16 * π ^ 2 * τ * x)) * τ ^ 3 ≤ 2 * |T| + 7 := by
  have hK : 1 ≤ 16 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hy : 0 ≤ τ * x := mul_nonneg hτ.le hx
  have hyv : τ * x ≤ 16 * π ^ 2 * τ * x := by nlinarith
  have hv : 0 ≤ 16 * π ^ 2 * τ * x := le_trans hy hyv
  have hE : 0 < Real.exp (-(16 * π ^ 2 * τ * x)) := Real.exp_pos _
  have e2 := pow_mul_exp_neg_le hv 2
  have e3 := pow_mul_exp_neg_le hv 3
  norm_num [Nat.factorial] at e2 e3
  have h2 : (τ * x) ^ 2 ≤ (16 * π ^ 2 * τ * x) ^ 2 := pow_le_pow_left₀ hy hyv 2
  have h3 : (τ * x) ^ 3 ≤ (16 * π ^ 2 * τ * x) ^ 3 := pow_le_pow_left₀ hy hyv 3
  have hA : (τ * x) ^ 2 * Real.exp (-(16 * π ^ 2 * τ * x)) ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_right h2 hE.le) e2
  have hB : (τ * x) ^ 3 * Real.exp (-(16 * π ^ 2 * τ * x)) ≤ 6 :=
    le_trans (mul_le_mul_of_nonneg_right h3 hE.le) e3
  have heq : x ^ 2 * (1 + x) * Real.exp (-(16 * π ^ 2 * τ * x)) * τ ^ 3 =
      τ * ((τ * x) ^ 2 * Real.exp (-(16 * π ^ 2 * τ * x))) +
        (τ * x) ^ 3 * Real.exp (-(16 * π ^ 2 * τ * x)) := by ring
  rw [heq]
  have hTa : τ ≤ |T| := hτT.trans (le_abs_self T)
  have hτA := mul_le_mul_of_nonneg_left hA hτ.le
  nlinarith

theorem heatSymbol_gain_le (T : ℝ) : ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ ξ : Space,
    ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * heatSymbol τ ξ ^ 2 ≤ C * τ ^ (-(3 / 2) : ℝ) := by
  refine ⟨2 * |T| + 7, fun τ hτ hτT ξ => ?_⟩
  have hP : ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hQ : (τ ^ (-(3 / 2) : ℝ)) ^ 2 = (τ ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le,
      show (-(3 / 2) : ℝ) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτ.le,
      Real.rpow_natCast]
  have hH : (heatSymbol τ ξ ^ 2) ^ 2 = Real.exp (-(16 * π ^ 2 * τ * ‖ξ‖ ^ 2)) := by
    unfold heatSymbol
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hL0 : 0 ≤ ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * heatSymbol τ ξ ^ 2 := by positivity
  have hR0 : 0 ≤ (2 * |T| + 7) * τ ^ (-(3 / 2) : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hτ.le _)
  rw [← pow_le_pow_iff_left₀ hL0 hR0 two_ne_zero, mul_pow, mul_pow, mul_pow, hP, hQ, hH,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (‖ξ‖ ^ 2) ^ 2 * (1 + ‖ξ‖ ^ 2) * Real.exp (-(16 * π ^ 2 * τ * ‖ξ‖ ^ 2)) * τ ^ 3
      ≤ 2 * |T| + 7 := heat_gain_base hτ hτT (by positivity)
    _ ≤ (2 * |T| + 7) ^ 2 := by nlinarith [abs_nonneg T]

end Breakdown.SmoothFlow
