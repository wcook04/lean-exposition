import Breakdown.Frac.StSpaceReg

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow.PowerInternal

private theorem integral_exp_neg_mul_le {k h : ℝ} (hk : 0 < k) :
    ∫ u in (0 : ℝ)..h, Real.exp ((-k) * u) = (1 - Real.exp (-(k * h))) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by linarith : (-k) ≠ 0),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring_nf

private theorem rate_min_bound {α x h : ℝ} (hα : 1 < α) (hx : 0 < x) (hh : 0 < h) :
    x * min h (1 / (2 * π * x) ^ (2 * α)) ≤
      (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - 1 / (2 * α)) := by
  set γ := 1 / (2 * α) with hγ
  have hα2 : 0 < 2 * α := by linarith
  have hhγ : 0 < h ^ γ := Real.rpow_pos_of_pos hh γ
  have hhβ : 0 ≤ h ^ (1 - γ) := Real.rpow_nonneg hh.le _
  have hsplit : h ^ γ * h ^ (1 - γ) = h := by
    rw [← Real.rpow_add hh]
    simp
  have hc0 : 0 ≤ (2 * π) ^ (-(2 * α)) := Real.rpow_nonneg (by positivity) _
  rcases le_or_gt (x * h ^ γ) 1 with hc | hc
  · calc x * min h (1 / (2 * π * x) ^ (2 * α)) ≤ x * h := by
          gcongr
          exact min_le_left _ _
      _ = (x * h ^ γ) * h ^ (1 - γ) := by rw [mul_assoc, hsplit]
      _ ≤ 1 * h ^ (1 - γ) := by gcongr
      _ ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - γ) := by nlinarith
  · have hk : (2 * π * x) ^ (2 * α) = (2 * π) ^ (2 * α) * x ^ (2 * α) :=
      Real.mul_rpow (by positivity) hx.le
    have hxk : x * (1 / (2 * π * x) ^ (2 * α)) = (2 * π) ^ (-(2 * α)) * x ^ (1 - 2 * α) := by
      rw [hk, Real.rpow_neg (by positivity), Real.rpow_sub hx, Real.rpow_one]
      ring
    have hpow : 1 ≤ (x * h ^ γ) ^ (2 * α - 1) := Real.one_le_rpow hc.le (by linarith)
    have hexp : (x * h ^ γ) ^ (2 * α - 1) = x ^ (2 * α - 1) * h ^ (1 - γ) := by
      rw [Real.mul_rpow hx.le hhγ.le, ← Real.rpow_mul hh.le]
      congr 2
      rw [hγ]
      field_simp
    have hxpos : 0 < x ^ (2 * α - 1) := Real.rpow_pos_of_pos hx _
    have hinv : x ^ (1 - 2 * α) = (x ^ (2 * α - 1))⁻¹ := by
      rw [← Real.rpow_neg hx.le]
      congr 1
      ring
    have hxb : x ^ (1 - 2 * α) ≤ h ^ (1 - γ) := by
      rw [hinv]
      calc (x ^ (2 * α - 1))⁻¹ ≤ (x ^ (2 * α - 1))⁻¹ * (x ^ (2 * α - 1) * h ^ (1 - γ)) := by
            rw [← hexp]
            exact le_mul_of_one_le_right (inv_nonneg.2 hxpos.le) hpow
        _ = h ^ (1 - γ) := by field_simp
    calc x * min h (1 / (2 * π * x) ^ (2 * α)) ≤ x * (1 / (2 * π * x) ^ (2 * α)) := by
          gcongr
          exact min_le_right _ _
      _ = (2 * π) ^ (-(2 * α)) * x ^ (1 - 2 * α) := hxk
      _ ≤ (2 * π) ^ (-(2 * α)) * h ^ (1 - γ) := by gcongr
      _ ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - γ) := by nlinarith

end Breakdown.SmoothFlow.PowerInternal

namespace Breakdown.SmoothFlow

open Breakdown.SmoothFlow.PowerInternal

theorem powerHeatBasic (α : ℝ) (hα : 1 < α) : PowerHeatBasicStatement α := by
  refine ⟨fun t ξ => Real.exp_nonneg _, fun t ξ => by unfold powerHeatSymbol; fun_prop, ?_⟩
  refine ⟨1 + (2 * π) ^ (-(2 * α)), by positivity, fun T t hTt ξ => ?_⟩
  have hsub : ∫ s in T..t, powerHeatSymbol α (t - s) ξ =
      ∫ u in (0 : ℝ)..(t - T), powerHeatSymbol α u ξ := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => powerHeatSymbol α u ξ) t]
    simp
  rw [hsub]
  set h := t - T with hh
  have h0 : 0 ≤ h := by rw [hh]; linarith
  have hC0 : 0 ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - 1 / (2 * α)) := by positivity
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz] at hC0 ⊢
    rw [intervalIntegral.integral_same, mul_zero]
    linarith
  rcases eq_or_lt_of_le (norm_nonneg ξ) with hxz | hxp
  · have hone : ∀ u, powerHeatSymbol α u ξ = 1 := fun u => by
      unfold powerHeatSymbol
      rw [← hxz, mul_zero, Real.zero_rpow (by linarith : (2 * α) ≠ 0)]
      simp
    simp only [hone, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [← hxz]
    linarith
  · obtain ⟨k, hk⟩ : ∃ k, k = (2 * π * ‖ξ‖) ^ (2 * α) := ⟨_, rfl⟩
    have hkp : 0 < k := by rw [hk]; positivity
    have hform : ∀ u, powerHeatSymbol α u ξ = Real.exp ((-k) * u) := fun u => by
      rw [hk]
      unfold powerHeatSymbol
      congr 1
      ring
    simp only [hform]
    rw [integral_exp_neg_mul_le hkp]
    set I := (1 - Real.exp (-(k * h))) / k with hI
    have hI1 : I ≤ h := by
      rw [hI, div_le_iff₀ hkp]
      have := Real.add_one_le_exp (-(k * h))
      linarith
    have hI2 : I ≤ 1 / k := by
      rw [hI]
      gcongr
      have := Real.exp_pos (-(k * h))
      linarith
    have hI2' : I ≤ 1 / (2 * π * ‖ξ‖) ^ (2 * α) := by rw [← hk]; exact hI2
    have hxI : ‖ξ‖ * I ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - 1 / (2 * α)) :=
      (mul_le_mul_of_nonneg_left (le_min hI1 hI2') hxp.le).trans (rate_min_bound hα hxp hpos)
    have hexpand : (1 + ‖ξ‖) * I = I + ‖ξ‖ * I := by ring
    rw [hexpand]
    linarith

end Breakdown.SmoothFlow
