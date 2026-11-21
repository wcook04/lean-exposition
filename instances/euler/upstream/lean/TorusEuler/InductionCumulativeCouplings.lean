import TorusEuler.InductionScales
import TorusEuler.PhysicalAmplificationCrossing

/-!
The cumulative first-coupling bound in item 3 of Theorem 7.1. Index zero
denotes the first wave and the coupling at its initial activation.
-/

namespace TorusEuler

open MovingWaveVector Set

/-- The ratio `ε_(i+1)` prescribed for the older wave at transition `i`.
Transition zero starts wave two, so its gain is `L₂ = 4 log λ₃`. -/
noncomputable def scheduledCrossingRatio (freq : ℕ → ℝ) (i : ℕ) : ℝ :=
  couplingRatioOfGain (4 * Real.log (freq (i + 3)))

/-- A crossing of the actual growing physical wave supplies the successive
couplings. The three compatibility equalities identify the stage data with
the older first coupling, the prescribed older ratio and the new coupling. -/
def IsScheduledPhysicalCrossing (older newer olderRatio nextRatio : ℝ) : Prop :=
  ∃ (I : Set ℝ) (t₀ T scale peak : ℝ) (w : PhysicalAmplification I t₀)
    (d : w.GrowingCrossing T scale peak nextRatio),
      w.firstCoupling = older ∧ w.ratio = olderRatio ∧
      w.physicalNu d.waveVector d.amplitude d.crossing = newer

/-- The signed first coupling of a constructed crossing is positive, and its
relative logarithmic increment has the bound following (2.10). -/
theorem IsScheduledPhysicalCrossing.coupling_step {older newer olderRatio nextRatio : ℝ}
    (h : IsScheduledPhysicalCrossing older newer olderRatio nextRatio) :
    0 < older ∧ 0 < newer ∧ |Real.log (newer / older)| ≤ 2 * olderRatio := by
  obtain ⟨I, t₀, T, scale, peak, w, d, hold, hratio, hnew⟩ := h
  have hOld : 0 < w.firstCoupling := w.first_coupling_positive
  have hNew : 0 < w.physicalNu d.waveVector d.amplitude d.crossing :=
    (div_pos (mul_pos hOld w.ratio_pos) (by norm_num)).trans_le
      (d.first_coupling_lower d.crossing d.crossing_in_slab)
  rw [← hold, ← hnew, ← hratio]
  exact ⟨hOld, hNew, d.crossing_coupling_log⟩

/-- The finite induction uses only the crossings already constructed. Extend
the coupling by its last value and the ratio by zero to use the cumulative
estimate without hypotheses on any later stage. -/
theorem firstCoupling_prefix_bounds (ν ε : ℕ → ℝ) (n : ℕ)
    (hν : ∀ i ≤ n, 0 < ν i) (hε : ∀ i ≤ n, 0 ≤ ε i)
    (hratio : ∀ i < n, ε (i + 1) ≤ ε i / 32)
    (hlocal : ∀ i < n, |Real.log (ν (i + 1) / ν i)| ≤ 2 * ε i)
    (hstart : ν 0 = 2 * Real.pi) (hsmall : 4 * ε 0 ≤ Real.log 2) :
    ∀ j ≤ n, |Real.log (ν j / (2 * Real.pi))| ≤ 4 * ε 0 ∧
      Real.pi ≤ ν j ∧ ν j ≤ 4 * Real.pi := by
  let ν' i := ν (min i n)
  let ε' i := if i ≤ n then ε i else 0
  have hν' (i : ℕ) : 0 < ν' i := hν _ (min_le_right _ _)
  have hε' (i : ℕ) : 0 ≤ ε' i := by
    by_cases hi : i ≤ n
    · simpa only [ε', ite_eq_left hi] using hε i hi
    · simp only [ε', ite_eq_right hi, le_refl]
  have hratio' (i : ℕ) : ε' (i + 1) ≤ ε' i / 32 := by
    by_cases hi : i < n
    · simpa only [ε', ite_eq_left (Nat.le_of_lt hi), ite_eq_left (Nat.succ_le_of_lt hi)] using hratio i hi
    · have hi' : ¬ i + 1 ≤ n := by omega
      change (if i + 1 ≤ n then ε (i + 1) else 0) ≤ ε' i / 32
      rw [ite_eq_right hi']
      exact div_nonneg (hε' i) (by norm_num)
  have hlocal' (i : ℕ) : |Real.log (ν' (i + 1) / ν' i)| ≤ 2 * ε' i := by
    by_cases hi : i < n
    · simpa only [ν', min_eq_left (Nat.le_of_lt hi), min_eq_left (Nat.succ_le_of_lt hi),
        ε', ite_eq_left (Nat.le_of_lt hi)] using hlocal i hi
    · have hn : n ≤ i := by omega
      simp only [ν', min_eq_right hn, min_eq_right (show n ≤ i + 1 by omega),
        div_self (hν n le_rfl).ne', Real.log_one, abs_zero]
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hε' i)
  have hstart' : ν' 0 = 2 * Real.pi := by simpa only [ν', min_eq_left (Nat.zero_le n)] using hstart
  have hsmall' : 4 * ε' 0 ≤ Real.log 2 := by
    simpa only [ε', ite_eq_left (Nat.zero_le n)] using hsmall
  intro j hj
  have hlog := firstCoupling_cumulative_log_bound ν' ε' hν' hε' hratio' hlocal' j
  have hpi := firstCoupling_pi_bounds ν' ε' hν' hε' hratio' hlocal' hstart' hsmall' j
  rw [hstart'] at hlog
  exact ⟨by simpa only [ν', min_eq_left hj, ε', ite_eq_left (Nat.zero_le n)] using hlog,
    by simpa only [ν', min_eq_left hj] using hpi⟩

/-- The schedule (1.14) gives the geometric bound (7.9) and the initial
ratio bound from the base frequency. -/
theorem frequencySchedule_crossing_ratios {b : ℕ} {q : ℕ → ℕ} {freq : ℕ → ℝ}
    {B : ℕ → ℝ} (hb : 1 ≤ b) (hN : 1 < freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) :
    (∀ i, 0 < scheduledCrossingRatio freq i ∧
      scheduledCrossingRatio freq (i + 1) ≤ scheduledCrossingRatio freq i / 32) ∧
      (∀ i, scheduledCrossingRatio freq i ≤ (1 / 32 : ℝ) ^ i * scheduledCrossingRatio freq 0) ∧
      scheduledCrossingRatio freq 0 ≤ (Real.log (freq 0) ^ 2)⁻¹ := by
  let gain (i : ℕ) := 4 * Real.log (freq (i + 1))
  have hmono := frequencySchedule_frequency_mono b q freq hb hN.le hFreq
  have hfreqPos (i : ℕ) : 1 < freq i := hN.trans_le (hmono (Nat.zero_le i))
  have hGain (i : ℕ) : 0 < gain i := mul_pos (by norm_num) (Real.log_pos (hfreqPos _))
  have hRatios (i : ℕ) : 0 < scheduledCrossingRatio freq i ∧
      scheduledCrossingRatio freq (i + 1) ≤ scheduledCrossingRatio freq i / 32 := by
    have hStep := (frequencySchedule_gain_ratio b q freq gain (i + 2) hb
      (hMax (i + 2)).1.1 (hfreqPos _) (hFreq (i + 3)) (fun _ => rfl)).2
    change 0 < couplingRatioOfGain (gain (i + 2)) ∧
      couplingRatioOfGain (gain (i + 3)) ≤ couplingRatioOfGain (gain (i + 2)) / 32
    exact ⟨inv_pos.mpr (pow_pos (hGain _) _),
      (couplingRatioOfGain_step (hGain (i + 2)) hStep).2.1⟩
  refine ⟨hRatios, ?_, ?_⟩
  · intro i
    induction i with
    | zero => simp only [pow_zero, one_mul, le_refl]
    | succ i hi =>
      calc
        _ ≤ scheduledCrossingRatio freq i / 32 := (hRatios i).2
        _ ≤ ((1 / 32 : ℝ) ^ i * scheduledCrossingRatio freq 0) / 32 :=
          div_le_div_of_nonneg_right hi (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  · have hlog₀ : 0 < Real.log (freq 0) := Real.log_pos hN
    have hlog : Real.log (freq 0) ≤ Real.log (freq 3) :=
      Real.log_le_log (zero_lt_one.trans hN) (hmono (Nat.zero_le _))
    have hL : Real.log (freq 0) ≤ gain 2 := by unfold gain; linarith
    change (gain 2 ^ 2)⁻¹ ≤ (Real.log (freq 0) ^ 2)⁻¹
    exact (inv_le_inv₀ (pow_pos (hGain 2) _) (pow_pos hlog₀ _)).mpr
      (pow_le_pow_left₀ hlog₀.le hL _)

/-- The actual growing crossings and the prescribed schedule keep the first
coupling in the interval in (7.3), uniformly for every constructed finite
prefix. The threshold `exp 4` is a sufficient bound on the base frequency. -/
theorem frequencySchedule_physical_coupling_prefix_bounds
    {b : ℕ} {q : ℕ → ℕ} {freq ν : ℕ → ℝ} {B : ℕ → ℝ} (n : ℕ)
    (hb : 1 ≤ b) (hLarge : Real.exp 4 ≤ freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hstart : ν 0 = 2 * Real.pi)
    (hCross : ∀ i < n, IsScheduledPhysicalCrossing (ν i) (ν (i + 1))
      (scheduledCrossingRatio freq i) (scheduledCrossingRatio freq (i + 1))) :
    ∀ j ≤ n, |Real.log (ν j / (2 * Real.pi))| ≤ 4 * scheduledCrossingRatio freq 0 ∧
      4 * scheduledCrossingRatio freq 0 ≤ 4 * (Real.log (freq 0) ^ 2)⁻¹ ∧
      Real.pi ≤ ν j ∧ ν j ≤ 4 * Real.pi := by
  have hN : 1 < freq 0 := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hLarge
  have hLog : 4 ≤ Real.log (freq 0) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 4) hLarge
  obtain ⟨hRatios, _, hFirst⟩ := frequencySchedule_crossing_ratios hb hN hFreq hMax
  have hLogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hInv : (Real.log (freq 0) ^ 2)⁻¹ ≤ 1 / 16 := by
    rw [one_div]
    apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
    exact (show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num) ▸
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hLog (2 : ℕ)
  have hsmall : 4 * scheduledCrossingRatio freq 0 ≤ Real.log 2 := by
    linarith only [hLogTwo, hFirst.trans hInv]
  have hν (i : ℕ) (hi : i ≤ n) : 0 < ν i := by
    cases i with
    | zero => rw [hstart]; positivity
    | succ i => exact (hCross i (by omega)).coupling_step.2.1
  have hPrefix := firstCoupling_prefix_bounds ν (scheduledCrossingRatio freq) n hν
    (fun i _ => (hRatios i).1.le) (fun i _ => (hRatios i).2)
    (fun i hi => (hCross i hi).coupling_step.2.2) hstart hsmall
  intro j hj
  obtain ⟨hl, hLower, hUpper⟩ := hPrefix j hj
  exact ⟨hl, mul_le_mul_of_nonneg_left hFirst (by norm_num), hLower, hUpper⟩

end TorusEuler
