import Breakdown.Frac.StSpaceReg

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow.PowerInternal

theorem gainRpowLeMulExp {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    s ^ q ≤ q ^ q * Real.exp s := by
  have h1 : s / q ≤ Real.exp (s / q) := by
    have := Real.add_one_le_exp (s / q); linarith
  have h2 : (s / q) ^ q ≤ Real.exp (s / q) ^ q :=
    Real.rpow_le_rpow (div_nonneg hs hq.le) h1 hq.le
  rw [← Real.exp_mul, div_mul_cancel₀ s hq.ne', Real.div_rpow hs hq.le] at h2
  have hqq : 0 < q ^ q := Real.rpow_pos_of_pos hq q
  rw [div_le_iff₀ hqq] at h2
  calc s ^ q ≤ Real.exp s * q ^ q := h2
    _ = q ^ q * Real.exp s := mul_comm _ _

theorem gainCubeMulExpLe {α q τ a : ℝ} (hq : 0 < q) (h3 : 2 * α * q = 3) (hτ : 0 < τ)
    (ha : 0 ≤ a) :
    a ^ 3 * Real.exp (-(τ * a ^ (2 * α))) ≤ q ^ q * τ ^ (-q) := by
  have hs : 0 ≤ τ * a ^ (2 * α) := mul_nonneg hτ.le (Real.rpow_nonneg ha _)
  have key := gainRpowLeMulExp hs hq
  have hpow : (τ * a ^ (2 * α)) ^ q = τ ^ q * a ^ 3 := by
    rw [Real.mul_rpow hτ.le (Real.rpow_nonneg ha _), ← Real.rpow_mul ha, h3]
    congr 1
    exact_mod_cast Real.rpow_natCast a 3
  rw [hpow] at key
  have hτq : 0 < τ ^ q := Real.rpow_pos_of_pos hτ q
  have he : 0 < Real.exp (-(τ * a ^ (2 * α))) := Real.exp_pos _
  have hexp : Real.exp (τ * a ^ (2 * α)) * Real.exp (-(τ * a ^ (2 * α))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.rpow_neg hτ.le, le_mul_inv_iff₀ hτq]
  calc a ^ 3 * Real.exp (-(τ * a ^ (2 * α))) * τ ^ q
      = (τ ^ q * a ^ 3) * Real.exp (-(τ * a ^ (2 * α))) := by ring
    _ ≤ (q ^ q * Real.exp (τ * a ^ (2 * α))) * Real.exp (-(τ * a ^ (2 * α))) :=
        mul_le_mul_of_nonneg_right key he.le
    _ = q ^ q := by rw [mul_assoc, hexp, mul_one]

end Breakdown.SmoothFlow.PowerInternal

namespace Breakdown.SmoothFlow

open Breakdown.SmoothFlow.PowerInternal

theorem powerHeatGain (α : ℝ) (hα : 1 < α) : PowerHeatGainStatement α := by
  intro T
  set q := 3 / (2 * α) with hqdef
  have hα0 : 0 < α := by linarith
  have hq : 0 < q := by positivity
  have h3 : 2 * α * q = 3 := by rw [hqdef]; field_simp
  refine ⟨T ^ q + 2 * q ^ q, ?_⟩
  intro τ hτ hτT ξ
  set x := ‖ξ‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg ξ
  set a := 2 * π * x with ha
  have ha0 : 0 ≤ a := by positivity
  have hxa : x ≤ a := by
    have := Real.pi_gt_three
    rw [ha]; nlinarith
  set E := Real.exp (-(τ * a ^ (2 * α))) with hE
  have hsym : powerHeatSymbol α τ ξ = E := rfl
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hτ.le (Real.rpow_nonneg ha0 _)
  have hE2 : E ^ 2 ≤ E := by nlinarith
  have hsq : (1 + x ^ 2) ^ (1 / 2 : ℝ) ≤ 1 + x := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (1 + x ^ 2) ≤ Real.sqrt ((1 + x) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + x := Real.sqrt_sq (by linarith)
  have hpoly : x ^ 2 * (1 + x) ≤ 1 + 2 * x ^ 3 := by
    rcases le_total x 1 with h | h
    · have : x ^ 2 ≤ 1 := pow_le_one₀ hx0 h
      nlinarith [pow_nonneg hx0 3]
    · nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 h)]
  have hx3 : x ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hx0 hxa 3
  have hcube : a ^ 3 * E ≤ q ^ q * τ ^ (-q) := gainCubeMulExpLe hq h3 hτ ha0
  have hT1 : 1 ≤ T ^ q * τ ^ (-q) := by
    have hT : 0 < T := lt_of_lt_of_le hτ hτT
    rw [Real.rpow_neg hτ.le, ← div_eq_mul_inv, ← Real.div_rpow hT.le hτ.le]
    exact Real.one_le_rpow (by rw [le_div_iff₀ hτ]; linarith) hq.le
  have h1 : x ^ 2 * (1 + x ^ 2) ^ (1 / 2 : ℝ) * E ^ 2 ≤ x ^ 2 * (1 + x) * E := by
    calc x ^ 2 * (1 + x ^ 2) ^ (1 / 2 : ℝ) * E ^ 2 ≤ x ^ 2 * (1 + x) * E ^ 2 := by gcongr
      _ ≤ x ^ 2 * (1 + x) * E := mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hP : x ^ 2 * (1 + x) * E ≤ (1 + 2 * x ^ 3) * E := mul_le_mul_of_nonneg_right hpoly hE0.le
  have hxE : x ^ 3 * E ≤ a ^ 3 * E := mul_le_mul_of_nonneg_right hx3 hE0.le
  rw [hsym]
  calc x ^ 2 * (1 + x ^ 2) ^ (1 / 2 : ℝ) * E ^ 2 ≤ x ^ 2 * (1 + x) * E := h1
    _ ≤ (T ^ q + 2 * q ^ q) * τ ^ (-q) := by nlinarith

end Breakdown.SmoothFlow
