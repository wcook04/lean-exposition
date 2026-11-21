import TorusEuler.InductiveStageConstruction

/-! Lower bounds for the physical slabs in the terminal note. -/

namespace TorusEuler.InductiveEulerParameters

/-- The endpoint slab of a child has length at least the negative
one-eighth power of its parent frequency. -/
theorem parent_rpow_le_slab (P : InductiveEulerParameters)
    (hBase : Real.exp 1 ≤ P.frequency 0) {n : ℕ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    P.frequency n ^ (-1 / 8 : ℝ) ≤ P.slab (n + 1) t₀ := by
  have hOne : 1 ≤ P.frequency 0 :=
    (Real.one_le_exp (by norm_num : 0 ≤ (1 : ℝ))).trans hBase
  have hm := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hOne P.frequency_step
  have hGain : 1 ≤ 4 * Real.log (P.frequency (n + 3)) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hBase.trans (hm (Nat.zero_le (n + 3))))
    rw [Real.log_exp] at h
    linarith
  have hf : 0 ≤ P.frequency n := zero_le_one.trans (hOne.trans (hm (Nat.zero_le n)))
  have hR := Real.rpow_nonneg hf (-1 / 8 : ℝ)
  have hHalf : P.frequency n ^ (-1 / 8 : ℝ) ≤ inductionHalfLength P.frequency n :=
    le_mul_of_one_le_right hR (one_le_pow₀ hGain)
  rw [P.slab_succ]
  linarith only [hR, ht₀, hHalf]

/-- The inverse slab power in time-jet extraction is a fixed power of the
parent frequency at every fixed time order. -/
theorem slab_inverse_pow_le_parent_rpow (P : InductiveEulerParameters)
    (hBase : Real.exp 1 ≤ P.frequency 0) {n : ℕ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (q : ℕ) :
    (P.slab (n + 1) t₀)⁻¹ ^ q ≤ P.frequency n ^ ((q : ℝ) / 8) := by
  have hOne : 1 ≤ P.frequency 0 :=
    (Real.one_le_exp (by norm_num : 0 ≤ (1 : ℝ))).trans hBase
  have hm := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hOne P.frequency_step
  have hf : 0 < P.frequency n := zero_lt_one.trans_le (hOne.trans (hm (Nat.zero_le n)))
  have hLower := P.parent_rpow_le_slab hBase ht₀ (n := n)
  have hPos := (Real.rpow_pos_of_pos hf (-1 / 8 : ℝ)).trans_le hLower
  calc
    _ ≤ ((P.frequency n ^ (-1 / 8 : ℝ))⁻¹) ^ q :=
      pow_le_pow_left₀ (inv_nonneg.mpr hPos.le) (inv_anti₀ (Real.rpow_pos_of_pos hf _) hLower) _
    _ = (P.frequency n ^ (1 / 8 : ℝ)) ^ q := by
      rw [show (-1 / 8 : ℝ) = -(1 / 8 : ℝ) by ring, Real.rpow_neg hf.le, inv_inv]
    _ = _ := by
      rw [← Real.rpow_mul_natCast hf.le]
      congr 1
      ring

end TorusEuler.InductiveEulerParameters
