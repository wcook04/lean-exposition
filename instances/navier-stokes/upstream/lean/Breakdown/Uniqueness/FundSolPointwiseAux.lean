import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric

noncomputable section

namespace Breakdown.FundSol.Internal

def radialCut (n : ℕ) (r t : ℝ) : ℝ := if t < r then t⁻¹ ^ n else 0

def ballPow (n : ℕ) (r : ℝ) (z : Space) : ℝ := radialCut n r ‖z‖

theorem ballPow_nonneg (n : ℕ) (r : ℝ) (z : Space) : 0 ≤ ballPow n r z := by
  unfold ballPow radialCut
  split_ifs <;> positivity

theorem ballPow_of_lt {n : ℕ} {r : ℝ} {z : Space} (h : ‖z‖ < r) : ballPow n r z = ‖z‖⁻¹ ^ n := by
  simp [ballPow, radialCut, h]

theorem ballPow_of_le {n : ℕ} {r : ℝ} {z : Space} (h : r ≤ ‖z‖) : ballPow n r z = 0 := by
  simp [ballPow, radialCut, not_lt.2 h]

theorem radial_eqOn {n : ℕ} (hn : n ≤ 2) (r : ℝ) :
    EqOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • radialCut n r y)
      ((Iio r).indicator (fun y => y ^ (2 - n))) (Ioi 0) := by
  intro y hy
  have hy' : (0 : ℝ) < y := hy
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, radialCut, indicator, mem_Iio]
  split_ifs with h
  · have : y ^ 2 = y ^ (2 - n) * y ^ n := by rw [← pow_add]; congr 1; omega
    rw [this, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy'.ne'), mul_one]
  · simp

theorem integrable_ballPow {n : ℕ} (hn : n ≤ 2) (r : ℝ) : Integrable (ballPow n r) := by
  unfold ballPow
  rw [integrable_fun_norm_addHaar volume (f := radialCut n r)]
  rw [integrableOn_congr_fun (radial_eqOn hn r) measurableSet_Ioi]
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio]
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
  rcases le_or_gt r 0 with hr | hr
  · have : Iio r ∩ Ioi (0 : ℝ) = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2]
    rw [this]; simp
  · have : Iio r ∩ Ioi (0 : ℝ) ⊆ Icc 0 r := fun y hy => ⟨le_of_lt hy.2, le_of_lt hy.1⟩
    exact ((continuous_pow (2 - n)).integrableOn_Icc).mono_set this

theorem integral_ballPow {n : ℕ} (hn : n ≤ 2) {r : ℝ} (hr : 0 < r) :
    ∫ z, ballPow n r z = Module.finrank ℝ Space * volume.real (ball (0 : Space) 1) *
      (r ^ (2 - n + 1) / ((2 - n : ℕ) + 1)) := by
  unfold ballPow
  rw [integral_fun_norm_addHaar volume (radialCut n r)]
  rw [setIntegral_congr_fun measurableSet_Ioi (radial_eqOn hn r)]
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le, integral_pow]
  simp [nsmul_eq_mul, smul_eq_mul, mul_assoc]

theorem integral_ballPow_zero {r : ℝ} (hr : 0 < r) :
    ∫ z, ballPow 0 r z = volume.real (ball (0 : Space) 1) * r ^ 3 := by
  rw [integral_ballPow (by norm_num) hr]
  simp [finrank_euclideanSpace_fin]
  ring

theorem integral_ballPow_one {r : ℝ} (hr : 0 < r) :
    ∫ z, ballPow 1 r z = 3 / 2 * volume.real (ball (0 : Space) 1) * r ^ 2 := by
  rw [integral_ballPow (by norm_num) hr]
  simp [finrank_euclideanSpace_fin]
  ring

theorem integral_ballPow_two {r : ℝ} (hr : 0 < r) :
    ∫ z, ballPow 2 r z = 3 * volume.real (ball (0 : Space) 1) * r := by
  rw [integral_ballPow (by norm_num) hr]
  simp [finrank_euclideanSpace_fin]

theorem inv_pow_three_mul (t : ℝ) : t⁻¹ ^ 3 * t = t⁻¹ ^ 2 := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · field_simp

end Breakdown.FundSol.Internal
