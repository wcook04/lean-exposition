import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem abs_integral_le_energy_mul {f : Space → ℝ} {w : Space → Space} {A C : ℝ}
    (hC : 0 ≤ C) (hE : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (h : ∀ x, |f x| ≤ C * ‖w x‖ ^ 2) : |∫ x, f x| ≤ C * A ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm f).trans
    (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (sq_nonneg A)) ?_)
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (‖w x‖ ^ 2) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact h x)
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (A ^ 2) := by gcongr
    _ = ENNReal.ofReal (C * A ^ 2) := (ENNReal.ofReal_mul hC).symm

private theorem integrable_cutoffPow_mul_sq {r : ℝ} (hr : 0 < r) {w : Space → Space}
    (hw : Continuous w) : Integrable (fun x => cutoffPow r x * ‖w x‖ ^ 2) := by
  have hc : Continuous fun x => cutoffPow r x * ‖w x‖ ^ 2 := by
    unfold cutoffPow
    exact ((contDiff_radialCutoff hr).continuous.pow 4).mul (hw.norm.pow 2)
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => ?_
  have : 2 * r ≤ ‖x‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  simp [cutoffPow, radialCutoff_eq_zero hr this]

theorem sumSecondPartials_term_le : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x| ≤ c * A ^ 2 / r := by
  obtain ⟨c₃, hc₃⟩ := abs_scalarSumSecondPartials_cutoffPow_le
  refine ⟨|c₃|, fun A w hw r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hCr : 0 ≤ |c₃| / r := div_nonneg (abs_nonneg _) hr0.le
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hpt : ∀ x, |‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x| ≤ |c₃| / r * ‖w x‖ ^ 2 := by
    intro x
    have hΔ : |FundSol.scalarSumSecondPartials (cutoffPow r) x| ≤ |c₃| / r :=
      calc _ ≤ c₃ / r ^ 2 := hc₃ r hr0 x
        _ ≤ |c₃| / r ^ 2 := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |c₃| / r := div_le_div_of_nonneg_left (abs_nonneg _) hr0 hrr
    calc _ = |FundSol.scalarSumSecondPartials (cutoffPow r) x| * ‖w x‖ ^ 2 := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hΔ (sq_nonneg _)
  have key := abs_integral_le_energy_mul hCr hw.energy hpt
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have he : |c₃| / r * A ^ 2 = |c₃| * A ^ 2 / r := by ring
  have h0 : 0 ≤ |∫ x, ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x| := abs_nonneg _
  linarith

theorem transport_term_le : ∃ c : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
    IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
      |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)| ≤
        c * U₀ * A ^ 2 / r := by
  obtain ⟨c₁, hc₁⟩ := norm_gradient_cutoffPow_le
  refine ⟨|c₁|, fun A U₀ U₁ u w hd r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hU₀ : 0 ≤ U₀ := (norm_nonneg _).trans (hd.bound_u 0)
  have hCr : 0 ≤ U₀ * (|c₁| / r) := mul_nonneg hU₀ (div_nonneg (abs_nonneg _) hr0.le)
  have hpt : ∀ x, |‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)| ≤
      U₀ * (|c₁| / r) * ‖w x‖ ^ 2 := by
    intro x
    have h3 : 0 ≤ radialCutoff r x ^ 3 := pow_nonneg (radialCutoff_nonneg r x) 3
    have h31 : radialCutoff r x ^ 3 ≤ 1 := pow_le_one₀ (radialCutoff_nonneg r x) (radialCutoff_le_one r x)
    have hg : ‖gradientAt (cutoffPow r) x‖ ≤ |c₁| / r :=
      calc _ ≤ c₁ / r * radialCutoff r x ^ 3 := hc₁ r hr0 x
        _ ≤ |c₁| / r * radialCutoff r x ^ 3 :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hr0.le) h3
        _ ≤ |c₁| / r * 1 :=
            mul_le_mul_of_nonneg_left h31 (div_nonneg (abs_nonneg _) hr0.le)
        _ = |c₁| / r := mul_one _
    have hi : |inner ℝ (u x) (gradientAt (cutoffPow r) x)| ≤ U₀ * (|c₁| / r) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hd.bound_u x) hg (norm_nonneg _) hU₀)
    calc _ = |inner ℝ (u x) (gradientAt (cutoffPow r) x)| * ‖w x‖ ^ 2 := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  have key := abs_integral_le_energy_mul hCr hd.field.energy hpt
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have he : U₀ * (|c₁| / r) * A ^ 2 = |c₁| * U₀ * A ^ 2 / r := by ring
  have h0 : 0 ≤ |∫ x, ‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)| := abs_nonneg _
  linarith

theorem stretching_term_le : ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
    IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 0 < r →
      |∫ x, cutoffPow r x * inner ℝ (w x) (fderiv ℝ u x (w x))| ≤ 2 * U₁ * cutoffEnergy r w := by
  intro A U₀ U₁ u w hd r hr
  have hint := integrable_cutoffPow_mul_sq hr hd.field.smooth.continuous
  have hpt : ∀ x, ‖cutoffPow r x * inner ℝ (w x) (fderiv ℝ u x (w x))‖ ≤
      U₁ * (cutoffPow r x * ‖w x‖ ^ 2) := by
    intro x
    have hη : 0 ≤ cutoffPow r x := pow_nonneg (radialCutoff_nonneg r x) 4
    have hd1 : ‖fderiv ℝ u x (w x)‖ ≤ U₁ * ‖w x‖ :=
      ((fderiv ℝ u x).le_opNorm (w x)).trans
        (mul_le_mul_of_nonneg_right (hd.bound_du x) (norm_nonneg _))
    have hi : |inner ℝ (w x) (fderiv ℝ u x (w x))| ≤ U₁ * ‖w x‖ ^ 2 :=
      calc _ ≤ ‖w x‖ * ‖fderiv ℝ u x (w x)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖w x‖ * (U₁ * ‖w x‖) := mul_le_mul_of_nonneg_left hd1 (norm_nonneg _)
        _ = U₁ * ‖w x‖ ^ 2 := by ring
    calc _ = cutoffPow r x * |inner ℝ (w x) (fderiv ℝ u x (w x))| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hη]
      _ ≤ cutoffPow r x * (U₁ * ‖w x‖ ^ 2) := mul_le_mul_of_nonneg_left hi hη
      _ = U₁ * (cutoffPow r x * ‖w x‖ ^ 2) := by ring
  rw [cutoffEnergy, ← Real.norm_eq_abs]
  calc _ ≤ ∫ x, U₁ * (cutoffPow r x * ‖w x‖ ^ 2) :=
        norm_integral_le_of_norm_le (hint.const_mul U₁) (ae_of_all _ hpt)
    _ = U₁ * ∫ x, cutoffPow r x * ‖w x‖ ^ 2 := integral_const_mul _ _
    _ = 2 * U₁ * ((1 / 2) * ∫ x, cutoffPow r x * ‖w x‖ ^ 2) := by ring

end Breakdown
