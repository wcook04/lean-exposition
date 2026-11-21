import Breakdown.Frac.StTorusForce
import Breakdown.Torus.ForceSmoothing

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace FracForceSmoothing.Internal

theorem rpow_le_one_add {y p : ℝ} (hy : 0 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : y ^ p ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_le_one hy h hp0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hp1
    rw [Real.rpow_one] at this
    linarith

theorem rpow_mul_exp_le {y p : ℝ} (hy : 0 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    y ^ p * Real.exp (-(2 * y)) ≤ 1 := by
  have h1 := rpow_le_one_add hy hp0 hp1
  have h2 : 1 + y ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y)
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  linarith

theorem sq_mul_exp_le {α τ r : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hr : 0 ≤ r) :
    r ^ 2 * Real.exp (-(2 * (r ^ (2 * α) * τ))) ≤ τ ^ (-(1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hy : 0 ≤ r ^ (2 * α) * τ := by positivity
  have hp0 : 0 ≤ 1 / α := by positivity
  have hp1 : 1 / α ≤ 1 := by rw [div_le_one hα0]; linarith
  have hyp : (r ^ (2 * α) * τ) ^ (1 / α) = r ^ 2 * τ ^ (1 / α) := by
    rw [Real.mul_rpow (by positivity) hτ.le, ← Real.rpow_mul hr]
    congr 1
    rw [show 2 * α * (1 / α) = ((2 : ℕ) : ℝ) by field_simp; norm_num, Real.rpow_natCast]
  have key := rpow_mul_exp_le hy hp0 hp1
  rw [hyp] at key
  have ht : 0 < τ ^ (1 / α) := Real.rpow_pos_of_pos hτ _
  calc r ^ 2 * Real.exp (-(2 * (r ^ (2 * α) * τ)))
      = (r ^ 2 * τ ^ (1 / α) * Real.exp (-(2 * (r ^ (2 * α) * τ)))) * (τ ^ (1 / α))⁻¹ := by
        field_simp
    _ ≤ 1 * (τ ^ (1 / α))⁻¹ := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr ht.le)
    _ = τ ^ (-(1 / α)) := by rw [one_mul, Real.rpow_neg hτ.le]

theorem weight_factor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k * fracLatticeFactor α τ k ^ 2 ≤ 2 * τ ^ (-(1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hr0 : 0 ≤ 2 * π * ‖freq k‖ := by positivity
  have hw : weight k = 1 + (2 * π * ‖freq k‖) ^ 2 := by unfold weight; ring
  have hf : fracLatticeFactor α τ k ^ 2 =
      Real.exp (-(2 * ((2 * π * ‖freq k‖) ^ (2 * α) * τ))) := by
    unfold fracLatticeFactor
    rw [max_eq_left hτ.le, sq, ← Real.exp_add]
    congr 1
    ring
  have hE : Real.exp (-(2 * ((2 * π * ‖freq k‖) ^ (2 * α) * τ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  have hz : -(1 / α) ≤ 0 := by
    have : 0 ≤ 1 / α := by positivity
    linarith
  have h1 : 1 ≤ τ ^ (-(1 / α)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 hz
  have h2 := sq_mul_exp_le hα hτ hr0
  rw [hw, hf, add_mul, one_mul]
  linarith

theorem weight_mul_sq_coeff (u : V) (k : Lattice) :
    weight k * ‖coeff u k‖ ^ 2 = ‖(u : Seq) k‖ ^ 2 := by
  unfold coeff
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs,
    abs_of_pos (Breakdown.Periodic.Internal.sqrt_weight_pos k), inv_pow,
    Real.sq_sqrt (Breakdown.Periodic.Internal.weight_pos k).le, ← mul_assoc,
    mul_inv_cancel₀ (Breakdown.Periodic.Internal.weight_pos k).ne', one_mul]

end FracForceSmoothing.Internal

open FracForceSmoothing.Internal in
theorem fracForceSmoothing_of (α : ℝ) (h1 : 1 < α) (hH : FracTorusHeatAlgebra α)
    (hF : FracTorusForceAlgebra α) : FracForceSmoothing α := by
  refine ⟨3, by norm_num, fun τ hτ hτ1 F hFc hp => ?_⟩
  have hS := ForceSmoothing.Internal.hasSum_sq hFc hp
  have hI : 0 ≤ ∫ x in cell, ‖F x‖ ^ 2 := hS.nonneg fun k => sq_nonneg _
  have hα0 : 0 < α := by linarith
  have hA : 0 ≤ τ ^ (-(1 / α)) := (Real.rpow_pos_of_pos hτ _).le
  have htp : (τ ^ (-(1 / (2 * α)))) ^ 2 = τ ^ (-(1 / α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    push_cast
    field_simp
  have hB : 0 ≤ 3 * τ ^ (-(1 / (2 * α))) * Real.sqrt (∫ x in cell, ‖F x‖ ^ 2) := by positivity
  have hb : ∀ k, weight k * ‖coeff (fracTorusForce α τ F) k‖ ^ 2 ≤
      8 * τ ^ (-(1 / α)) * ‖freqTrCoef F k‖ ^ 2 := by
    intro k
    have hfac : 0 ≤ fracLatticeFactor α τ k := (Real.exp_pos _).le
    have hl := Breakdown.Periodic.Internal.norm_divFree_le k (freqTrCoef F k)
    have hwf := weight_factor_le h1 hτ hτ1 k
    rw [hF.1 τ F k]
    unfold fracTorusForceCoef
    rw [if_pos hτ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
    calc weight k * (fracLatticeFactor α τ k * ‖divFree k (freqTrCoef F k)‖) ^ 2
        = (weight k * fracLatticeFactor α τ k ^ 2) * ‖divFree k (freqTrCoef F k)‖ ^ 2 := by ring
      _ ≤ (2 * τ ^ (-(1 / α))) * (2 * ‖freqTrCoef F k‖) ^ 2 :=
          mul_le_mul hwf (pow_le_pow_left₀ (norm_nonneg _) hl 2) (by positivity) (by positivity)
      _ = 8 * τ ^ (-(1 / α)) * ‖freqTrCoef F k‖ ^ 2 := by ring
  have hsum : Summable fun k => weight k * ‖coeff (fracTorusForce α τ F) k‖ ^ 2 := by
    have e : (fun k => weight k * ‖coeff (fracTorusForce α τ F) k‖ ^ 2) =
        fun k => ‖((fracTorusForce α τ F : V) : Seq) k‖ ^ 2 := by
      funext k
      exact weight_mul_sq_coeff _ k
    rw [e]
    exact Breakdown.Periodic.Internal.summable_sq _
  have hle : ‖fracTorusForce α τ F‖ ^ 2 ≤
      (3 * τ ^ (-(1 / (2 * α))) * Real.sqrt (∫ x in cell, ‖F x‖ ^ 2)) ^ 2 := by
    rw [norm_sq_eq_tsum, mul_pow, mul_pow, htp, Real.sq_sqrt hI]
    calc ∑' k, weight k * ‖coeff (fracTorusForce α τ F) k‖ ^ 2
        ≤ ∑' k, 8 * τ ^ (-(1 / α)) * ‖freqTrCoef F k‖ ^ 2 :=
          Summable.tsum_le_tsum hb hsum (hS.summable.mul_left _)
      _ = 8 * τ ^ (-(1 / α)) * ∫ x in cell, ‖F x‖ ^ 2 := by rw [tsum_mul_left, hS.tsum_eq]
      _ ≤ 3 ^ 2 * τ ^ (-(1 / α)) * ∫ x in cell, ‖F x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hA) hI
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp hle

end Breakdown.Periodic
