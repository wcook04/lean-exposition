import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem hasCompactSupport_of_vanish_far {r : ℝ} (F : Space → ℝ)
    (hF : ∀ x, 2 * r ≤ ‖x‖ → F x = 0) : HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
    have : 2 * r ≤ ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    exact hF x this

private theorem integrable_sq_of_energy {A : ℝ} {w : Space → Space}
    (hw : IsFiniteEnergyField A w) : Integrable (fun x => ‖w x‖ ^ 2) := by
  have hc : Continuous (fun x => ‖w x‖ ^ 2) := hw.smooth.continuous.norm.pow 2
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => show (0 : ℝ) ≤ ‖w x‖ ^ 2 by positivity)]
  exact lt_of_le_of_lt hw.energy ENNReal.ofReal_lt_top

private theorem integral_sq_le_of_energy {A : ℝ} {w : Space → Space}
    (hw : IsFiniteEnergyField A w) : ∫ x, ‖w x‖ ^ 2 ≤ A ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => show (0 : ℝ) ≤ ‖w x‖ ^ 2 by positivity)
    (integrable_sq_of_energy hw).aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (A ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw.energy
    _ = A ^ 2 := ENNReal.toReal_ofReal (by positivity)

private theorem memLp_rpow_norm {A : ℝ} {w : Space → Space} (hw : IsFiniteEnergyField A w) :
    MemLp (fun x => ‖w x‖ ^ (3 / 2 : ℝ)) (ENNReal.ofReal (4 / 3)) := by
  have hc : Continuous (fun x => ‖w x‖ ^ (3 / 2 : ℝ)) :=
    hw.smooth.continuous.norm.rpow_const (fun _ => Or.inr (by norm_num))
  rw [← integrable_norm_rpow_iff hc.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top]
  refine (integrable_sq_of_energy hw).congr (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_mul (norm_nonneg _),
    show (3 / 2 : ℝ) * (4 / 3) = 2 by norm_num, Real.rpow_two]

private theorem memLp_cutoff_rpow {r : ℝ} (hr : 0 < r) {A : ℝ} {w : Space → Space}
    (hw : IsFiniteEnergyField A w) :
    MemLp (fun x => (radialCutoff r x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ)) (ENNReal.ofReal 4) := by
  have hc : Continuous (fun x => (radialCutoff r x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ)) :=
    (((contDiff_radialCutoff hr).continuous.pow 2).mul hw.smooth.continuous.norm).rpow_const
      (fun _ => Or.inr (by norm_num))
  refine hc.memLp_of_hasCompactSupport (hasCompactSupport_of_vanish_far (r := r) _ fun x hx => ?_)
  simp [radialCutoff_eq_zero hr hx]

private theorem lpProd_step {r : ℝ} (hr : 0 < r) {A : ℝ} {w : Space → Space}
    (hw : IsFiniteEnergyField A w) :
    ∫ x, radialCutoff r x ^ 3 * ‖w x‖ ^ 3 ≤
      cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ fun x => show (0 : ℝ) ≤ (radialCutoff r x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ) by
      have := radialCutoff_nonneg r x
      positivity)
    (ae_of_all _ fun x => show (0 : ℝ) ≤ ‖w x‖ ^ (3 / 2 : ℝ) by positivity)
    (memLp_cutoff_rpow hr hw) (memLp_rpow_norm hw)
  have e1 : ∀ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ) * ‖w x‖ ^ (3 / 2 : ℝ) =
      radialCutoff r x ^ 3 * ‖w x‖ ^ 3 := by
    intro x
    have h0 := radialCutoff_nonneg r x
    have hn := norm_nonneg (w x)
    rw [← Real.mul_rpow (by positivity) hn,
      show radialCutoff r x ^ 2 * ‖w x‖ * ‖w x‖ = (radialCutoff r x * ‖w x‖) ^ (2 : ℝ) by
        rw [Real.rpow_two]; ring,
      ← Real.rpow_mul (by positivity), show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    ring
  have e2 : ∀ x, ((radialCutoff r x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ)) ^ (4 : ℝ) =
      (radialCutoff r x ^ 2 * ‖w x‖) ^ 6 := by
    intro x
    have h0 := radialCutoff_nonneg r x
    rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * 4 = ((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have e3 : ∀ x, (‖w x‖ ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) = ‖w x‖ ^ 2 := by
    intro x
    rw [← Real.rpow_mul (norm_nonneg _), show (3 / 2 : ℝ) * (4 / 3) = 2 by norm_num,
      Real.rpow_two]
  simp only [e1, e2, e3] at h
  have hI : 0 ≤ ∫ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ 6 := integral_nonneg fun x => by
    have := radialCutoff_nonneg r x
    positivity
  have hJ : 0 ≤ ∫ x, ‖w x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hS : cutoffSixthNorm r w ^ (3 / 2 : ℝ) =
      (∫ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ 6) ^ (1 / 4 : ℝ) := by
    unfold cutoffSixthNorm
    rw [← Real.rpow_mul hI]
    norm_num
  have hA : (∫ x, ‖w x‖ ^ 2) ^ (1 / (4 / 3) : ℝ) ≤ A ^ (3 / 2 : ℝ) := by
    calc _ ≤ (A ^ 2) ^ (1 / (4 / 3) : ℝ) :=
          Real.rpow_le_rpow hJ (integral_sq_le_of_energy hw) (by norm_num)
      _ = A ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hw.nonneg]
          norm_num
  rw [hS]
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hI _)

theorem cubic_term_le : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x)| ≤
        c * cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
  obtain ⟨c, hc⟩ := norm_gradient_cutoffPow_le
  refine ⟨max c 0 / 2, fun A w hw r hr1 => ?_⟩
  have hr : 0 < r := by linarith
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hg : ∀ x, ‖gradientAt (cutoffPow r) x‖ ≤ max c 0 / r * radialCutoff r x ^ 3 := fun x =>
    (hc r hr x).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) hr.le)
      (pow_nonneg (radialCutoff_nonneg r x) 3))
  have hint : Integrable (fun x => max c 0 / r * (radialCutoff r x ^ 3 * ‖w x‖ ^ 3)) := by
    refine Integrable.const_mul ?_ _
    refine Continuous.integrable_of_hasCompactSupport
      (((contDiff_radialCutoff hr).continuous.pow 3).mul (hw.smooth.continuous.norm.pow 3))
      (hasCompactSupport_of_vanish_far (r := r) _ fun x hx => ?_)
    simp [radialCutoff_eq_zero hr hx]
  have hpt : ∀ x, ‖‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x)‖ ≤
      max c 0 / r * (radialCutoff r x ^ 3 * ‖w x‖ ^ 3) := by
    intro x
    rw [norm_mul, norm_pow, norm_norm]
    calc _ ≤ ‖w x‖ ^ 2 * (‖w x‖ * ‖gradientAt (cutoffPow r) x‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)
      _ ≤ ‖w x‖ ^ 2 * (‖w x‖ * (max c 0 / r * radialCutoff r x ^ 3)) := by
          gcongr
          exact hg x
      _ = _ := by ring
  have hbound := norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
  rw [integral_const_mul] at hbound
  have hH := lpProd_step hr hw
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
  calc (1 / 2) * ‖∫ x, ‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x)‖
      ≤ (1 / 2) * (max c 0 / r * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ))) := by
        gcongr
        exact hbound.trans (mul_le_mul_of_nonneg_left hH (div_nonneg hc0 hr.le))
    _ = _ := by ring

end Breakdown
