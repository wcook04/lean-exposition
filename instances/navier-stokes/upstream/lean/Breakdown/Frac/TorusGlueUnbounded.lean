import Breakdown.Frac.StTorusStep
import Breakdown.Torus.GlueUnbounded

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace FracInternal.GlueUnbounded

open Internal.Unbounded

theorem dilExponent_pos {α : ℝ} (hα : 1 < α) : 0 < dilExponent α := by
  unfold dilExponent
  have h4 : 0 < 4 * α := by linarith
  have : 3 / (4 * α) < 1 := by
    rw [div_lt_one h4]
    linarith
  linarith

theorem fracGluePieces_stepStart (α : ℝ) {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam)) (n : ℕ) (h : (0 : ℝ) ≤ 1 - lam) :
    fracGluePieces α T lam u (stepStart T lam n) =
      (stepScale T lam n) ^ (-dilExponent α) • u n ⟨0, left_mem_Icc.2 h⟩ := by
  unfold fracGluePieces
  rw [stepNumber_stepStart hT hl hl1 n, sub_self, zero_div]
  unfold extendPiece
  rw [dif_pos h, IccExtend_left]

end FracInternal.GlueUnbounded

open Internal.Unbounded FracInternal.GlueUnbounded in
theorem fracGlueUnbounded (α : ℝ) (hα : 1 < α) : FracGlueUnbounded α := by
  intro T lam θ c₀ Z u ub z hT hl hl1 hθ hθ1 hc hub hz hu hbdd
  obtain ⟨B, hB⟩ := hbdd
  have h1 : Tendsto (fun n : ℕ => θ ^ n * Z) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const Z
  have h2 : Tendsto (fun n : ℕ => stepScale T lam n ^ (-dilExponent α)) atTop atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 (dilExponent_pos hα))).comp (tendsto_stepScale hT hl hl1)
  obtain ⟨n, hn1, hn2⟩ :=
    ((h1.eventually (Iio_mem_nhds (half_pos hc))).and
      (h2.eventually_ge_atTop (2 / c₀ * (B + 1)))).exists
  have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
  set x : Icc (0 : ℝ) (1 - lam) := ⟨0, left_mem_Icc.2 h0⟩ with hx
  have hmem := hB (mem_image_of_mem _ (stepStart_mem hT hl hl1 n))
  rw [fracGluePieces_stepStart α hT hl hl1 u n h0, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (stepScale_pos hT hl n) _)] at hmem
  have key : ‖ub n x‖ ≤ ‖u n x‖ + θ ^ n * Z := by
    have e : ub n x = u n x - θ ^ n • z n x := by
      rw [hu n]
      simp
    calc ‖ub n x‖ = ‖u n x - θ ^ n • z n x‖ := by rw [e]
      _ ≤ ‖u n x‖ + ‖θ ^ n • z n x‖ := norm_sub_le _ _
      _ ≤ ‖u n x‖ + θ ^ n * Z := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hθ n)]
        gcongr
        exact ((z n).norm_coe_le_norm x).trans (hz n)
  have hlow : c₀ / 2 ≤ ‖u n x‖ := by
    have := hub n x
    have hn1' : θ ^ n * Z < c₀ / 2 := hn1
    linarith
  have hpos : 0 ≤ stepScale T lam n ^ (-dilExponent α) :=
    (Real.rpow_pos_of_pos (stepScale_pos hT hl n) _).le
  have : B + 1 ≤ stepScale T lam n ^ (-dilExponent α) * ‖u n x‖ := by
    calc B + 1 = 2 / c₀ * (B + 1) * (c₀ / 2) := by field_simp
      _ ≤ stepScale T lam n ^ (-dilExponent α) * ‖u n x‖ :=
        mul_le_mul hn2 hlow (by linarith) hpos
  linarith

end Breakdown.Periodic
