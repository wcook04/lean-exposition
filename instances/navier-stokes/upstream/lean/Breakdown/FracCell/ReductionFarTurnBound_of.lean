import Breakdown.FracCell.ReductionFarDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

private theorem normSq_eq_parts (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem turnAdjInv_vecSq_mul (k : ℝ) (hk : 1 < |k|) (w : Fin 3 → ℂ) :
    vecSq (turnAdjInv k w) * (|k| - 1) ^ 2 ≤ vecSq w := by
  set a := |k| with ha_def
  have ha0 : 0 < a - 1 := by linarith
  have hk2 : k ^ 2 = a ^ 2 := (sq_abs k).symm
  have hkne : k ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha_def
    linarith
  have hden : (1 - k ^ 2) ^ 2 = ((a - 1) * (a + 1)) ^ 2 := by rw [hk2]; ring
  have hdenpos : 0 < (1 - k ^ 2) ^ 2 := by
    rw [hden]
    have : 0 < (a - 1) * (a + 1) := by nlinarith
    positivity
  have hc : ((1 : ℂ) / (1 - (k : ℂ) ^ 2)) = (((1 / (1 - k ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  set x0 := (w 0).re
  set y0 := (w 0).im
  set x1 := (w 1).re
  set y1 := (w 1).im
  have h0 : ‖turnAdjInv k w 0‖ ^ 2 = (1 / (1 - k ^ 2)) ^ 2 * ((k * y0 - x1) ^ 2 + (-(k * x0) - y1) ^ 2) := by
    simp only [turnAdjInv, Matrix.cons_val_zero]
    rw [hc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, normSq_eq_parts]
    congr 1
    simp [x0, y0, x1, y1]
  have h1 : ‖turnAdjInv k w 1‖ ^ 2 = (1 / (1 - k ^ 2)) ^ 2 * ((x0 + k * y1) ^ 2 + (y0 - k * x1) ^ 2) := by
    simp only [turnAdjInv, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, normSq_eq_parts]
    congr 1
    simp [x0, y0, x1, y1]
  have h2 : ‖turnAdjInv k w 2‖ ^ 2 = ‖w 2‖ ^ 2 / k ^ 2 := by
    simp only [turnAdjInv]
    simp [div_pow]
  have hw0 : ‖w 0‖ ^ 2 = x0 ^ 2 + y0 ^ 2 := normSq_eq_parts _
  have hw1 : ‖w 1‖ ^ 2 = x1 ^ 2 + y1 ^ 2 := normSq_eq_parts _
  have hB : (k * y0 - x1) ^ 2 + (-(k * x0) - y1) ^ 2 + ((x0 + k * y1) ^ 2 + (y0 - k * x1) ^ 2)
      ≤ (a + 1) ^ 2 * (x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2)) := by
    have hexp : (k * y0 - x1) ^ 2 + (-(k * x0) - y1) ^ 2 + ((x0 + k * y1) ^ 2 + (y0 - k * x1) ^ 2)
        = (k ^ 2 + 1) * (x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2)) + 4 * k * (x0 * y1 - y0 * x1) := by ring
    have hcross : 4 * k * (x0 * y1 - y0 * x1) ≤ 2 * a * (x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2)) := by
      have hq1 : 0 ≤ (x0 - y1) ^ 2 + (y0 + x1) ^ 2 := by positivity
      have hq2 : 0 ≤ (x0 + y1) ^ 2 + (y0 - x1) ^ 2 := by positivity
      rcases abs_cases k with ⟨hak, hk0⟩ | ⟨hak, hk0⟩
      · rw [ha_def, hak]; nlinarith
      · rw [ha_def, hak]; nlinarith
    rw [hexp, hk2]
    nlinarith
  have hmain01 : (‖turnAdjInv k w 0‖ ^ 2 + ‖turnAdjInv k w 1‖ ^ 2) * (a - 1) ^ 2
      ≤ ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
    rw [h0, h1, hw0, hw1]
    have hid : (1 / (1 - k ^ 2)) ^ 2 * (a + 1) ^ 2 * (a - 1) ^ 2 = 1 := by
      rw [div_pow, one_pow, hden]
      field_simp
    have hsq : 0 ≤ (1 / (1 - k ^ 2)) ^ 2 * (a - 1) ^ 2 := by positivity
    calc ((1 / (1 - k ^ 2)) ^ 2 * ((k * y0 - x1) ^ 2 + (-(k * x0) - y1) ^ 2)
          + (1 / (1 - k ^ 2)) ^ 2 * ((x0 + k * y1) ^ 2 + (y0 - k * x1) ^ 2)) * (a - 1) ^ 2
        = ((1 / (1 - k ^ 2)) ^ 2 * (a - 1) ^ 2) * ((k * y0 - x1) ^ 2 + (-(k * x0) - y1) ^ 2
          + ((x0 + k * y1) ^ 2 + (y0 - k * x1) ^ 2)) := by ring
      _ ≤ ((1 / (1 - k ^ 2)) ^ 2 * (a - 1) ^ 2) * ((a + 1) ^ 2 * (x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2))) :=
          mul_le_mul_of_nonneg_left hB hsq
      _ = ((1 / (1 - k ^ 2)) ^ 2 * (a + 1) ^ 2 * (a - 1) ^ 2) * (x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2)) := by ring
      _ = x0 ^ 2 + y0 ^ 2 + (x1 ^ 2 + y1 ^ 2) := by rw [hid, one_mul]
  have hmain2 : ‖turnAdjInv k w 2‖ ^ 2 * (a - 1) ^ 2 ≤ ‖w 2‖ ^ 2 := by
    rw [h2, hk2]
    have hapos : 0 < a ^ 2 := pow_pos (by linarith) 2
    have hle : (a - 1) ^ 2 ≤ a ^ 2 := by
      have hd : a ^ 2 - (a - 1) ^ 2 = 2 * a - 1 := by ring
      linarith
    calc ‖w 2‖ ^ 2 / a ^ 2 * (a - 1) ^ 2 = ‖w 2‖ ^ 2 * ((a - 1) ^ 2 / a ^ 2) := by ring
      _ ≤ ‖w 2‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hapos).mpr hle) (sq_nonneg _)
      _ = ‖w 2‖ ^ 2 := mul_one _
  unfold vecSq
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  calc (‖turnAdjInv k w 0‖ ^ 2 + ‖turnAdjInv k w 1‖ ^ 2 + ‖turnAdjInv k w 2‖ ^ 2) * (a - 1) ^ 2
      = (‖turnAdjInv k w 0‖ ^ 2 + ‖turnAdjInv k w 1‖ ^ 2) * (a - 1) ^ 2
        + ‖turnAdjInv k w 2‖ ^ 2 * (a - 1) ^ 2 := by ring
    _ ≤ ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 + ‖w 2‖ ^ 2 := by linarith [hmain01, hmain2]

theorem turnBound_of : TurnBoundStatement := by
  intro k N c S W F hm hband hT n hn w
  rw [hband, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hn
  obtain ⟨-, hout⟩ := hn
  have hn1 : ((W.J : ℤ) + 1) ≤ |n| := by
    by_contra h
    push Not at h
    exact hout ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩
  have hn1r : ((W.J + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hn1
  have hmr : (3 : ℝ) ≤ c.order := by exact_mod_cast hm
  have hJ : (1 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos W.J
  have hq : 3 ≤ ((W.J + 1 : ℕ) : ℝ) * c.order := by nlinarith
  have hkabs : ((W.J + 1 : ℕ) : ℝ) * c.order ≤ |azimuth c.order n| := by
    unfold azimuth
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right hn1r (Nat.cast_nonneg _)
  have hk1 : 1 < |azimuth c.order n| := by linarith
  have hkey := turnAdjInv_vecSq_mul (azimuth c.order n) hk1 w
  have hpos : 0 < |azimuth c.order n| - 1 := by linarith
  have hqpos : 0 < ((W.J + 1 : ℕ) : ℝ) * c.order - 1 := by linarith
  have hinv : 1 / (|azimuth c.order n| - 1) ≤ F.turnBound := by
    refine le_trans ?_ hT
    exact one_div_le_one_div_of_le hqpos (by linarith)
  have hinv0 : 0 ≤ 1 / (|azimuth c.order n| - 1) := by positivity
  have hsq : (1 / (|azimuth c.order n| - 1)) ^ 2 ≤ F.turnBound ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
  have hw0 : 0 ≤ vecSq w := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : vecSq (turnAdjInv (azimuth c.order n) w) ≤ (1 / (|azimuth c.order n| - 1)) ^ 2 * vecSq w := by
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    exact hkey
  exact hv.trans (mul_le_mul_of_nonneg_right hsq hw0)

end Reduction

end CellCert

end Breakdown
