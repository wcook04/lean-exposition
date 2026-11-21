import Breakdown.Torus.StatementsSteps

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace Internal.Unbounded

theorem stepNumber_stepStart {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) (n : ℕ) :
    stepNumber T lam (stepStart T lam n) = n := by
  have hq : (T - stepStart T lam n) / T = lam ^ n := by
    unfold stepStart stepScale
    field_simp
    ring
  have hlog : Real.log lam ≠ 0 := ne_of_lt (Real.log_neg hl hl1)
  unfold stepNumber
  rw [hq, Real.log_pow, mul_div_assoc, div_self hlog, mul_one, Nat.floor_natCast]

theorem gluePieces_stepStart {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam)) (n : ℕ) (h : (0 : ℝ) ≤ 1 - lam) :
    gluePieces T lam u (stepStart T lam n) =
      (stepScale T lam n) ^ (-(1 / 4 : ℝ)) • u n ⟨0, left_mem_Icc.2 h⟩ := by
  unfold gluePieces
  rw [stepNumber_stepStart hT hl hl1 n, sub_self, zero_div]
  unfold extendPiece
  rw [dif_pos h, IccExtend_left]

theorem stepStart_mem {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) (n : ℕ) :
    stepStart T lam n ∈ Ico 0 T := by
  have hp := stepScale_pos hT hl n
  have hle : stepScale T lam n ≤ T := by
    unfold stepScale
    exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
  unfold stepStart
  constructor <;> linarith

theorem tendsto_stepScale {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) :
    Tendsto (fun n : ℕ => stepScale T lam n) atTop (𝓝[>] 0) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun n => stepScale_pos hT hl n)⟩
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hl.le hl1).const_mul T
  simpa [stepScale] using this

end Internal.Unbounded

open Internal.Unbounded in
theorem glueUnbounded : GlueUnbounded := by
  intro T lam θ c₀ Z u ub z hT hl hl1 hθ hθ1 hc hub hz hu hbdd
  obtain ⟨B, hB⟩ := hbdd
  have h1 : Tendsto (fun n : ℕ => θ ^ n * Z) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const Z
  have h2 : Tendsto (fun n : ℕ => stepScale T lam n ^ (-(1 / 4 : ℝ))) atTop atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by norm_num)).comp (tendsto_stepScale hT hl hl1)
  obtain ⟨n, hn1, hn2⟩ :=
    ((h1.eventually (Iio_mem_nhds (half_pos hc))).and
      (h2.eventually_ge_atTop (2 / c₀ * (B + 1)))).exists
  have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
  set x : Icc (0 : ℝ) (1 - lam) := ⟨0, left_mem_Icc.2 h0⟩ with hx
  have hmem := hB (mem_image_of_mem _ (stepStart_mem hT hl hl1 n))
  rw [gluePieces_stepStart hT hl hl1 u n h0, norm_smul, Real.norm_eq_abs,
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
  have hpos : 0 ≤ stepScale T lam n ^ (-(1 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos (stepScale_pos hT hl n) _).le
  have : B + 1 ≤ stepScale T lam n ^ (-(1 / 4 : ℝ)) * ‖u n x‖ := by
    calc B + 1 = 2 / c₀ * (B + 1) * (c₀ / 2) := by field_simp
      _ ≤ stepScale T lam n ^ (-(1 / 4 : ℝ)) * ‖u n x‖ :=
        mul_le_mul hn2 hlow (by linarith) hpos
  linarith

end Breakdown.Periodic
