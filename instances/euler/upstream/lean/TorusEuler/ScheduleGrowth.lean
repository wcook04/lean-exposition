import TorusEuler.ScheduleExistence
import Mathlib.Analysis.SpecificLimits.Basic

namespace TorusEuler

open Filter

/-- The frequency recurrence (1.14) dominates a geometric progression. -/
theorem frequencySchedule_frequency_tendsto_atTop (b : ℕ) (q : ℕ → ℕ) (freq : ℕ → ℝ)
    (hb : 1 ≤ b) (hInit : 1 < freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) :
    Tendsto freq atTop atTop := by
  have hMono := frequencySchedule_frequency_mono b q freq hb hInit.le hFreq
  have hBase (i : ℕ) : freq 0 ≤ freq i := hMono (Nat.zero_le i)
  have hLower (i : ℕ) : freq 0 ^ i ≤ freq i := by
    induction i with
    | zero => simpa using hInit.le
    | succ i hi =>
      have hExponent : 2 ≤ frequencyExponent b (q (i + 1)) := by
        calc
          2 ≤ 320 * 1 * 1 := by decide
          _ ≤ frequencyExponent b (q (i + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)
      calc
        freq 0 ^ (i + 1) = freq 0 ^ i * freq 0 := pow_succ _ _
        _ ≤ freq i * freq i :=
          mul_le_mul hi (hBase i) (by positivity) (zero_le_one.trans (hInit.le.trans (hBase i)))
        _ = freq i ^ 2 := (sq _).symm
        _ ≤ freq (i + 1) := by
          rw [hFreq]
          exact pow_le_pow_right₀ (hInit.le.trans (hBase i)) hExponent
  exact tendsto_atTop_mono hLower (tendsto_pow_atTop_atTop_of_one_lt hInit)

/-- Appendix C's order divergence. Once the order reaches a given value, the next
threshold is eventually met and the order can increase again. -/
theorem frequencySchedule_order_tendsto_atTop (B freq : ℕ → ℝ) (q : ℕ → ℕ)
    (hqInit : q 1 = 1) (hInit : B 1 ≤ freq 0) (hFreqMono : Monotone freq)
    (hFreqGrowth : Tendsto freq atTop atTop)
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) :
    Tendsto q atTop atTop := by
  have hOrderMono : Monotone (fun i : ℕ => q (i + 1)) :=
    monotone_nat_of_le_succ fun i =>
      (frequencySchedule_order_steps B freq q hqInit hInit hFreqMono hMax i).1
  apply (tendsto_add_atTop_iff_nat 1).1
  apply hOrderMono.tendsto_atTop_atTop
  intro s
  induction s with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ s hs =>
    obtain ⟨i, hi⟩ := hs
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hFreqGrowth.eventually_ge_atTop (B (s + 1)))
    let j := max i k
    have hOrder : s ≤ q (j + 1) := hi.trans (hOrderMono (le_max_left i k))
    by_cases hReached : s + 1 ≤ q (j + 1)
    · exact ⟨j, hReached⟩
    have hCurrent : q (j + 1) = s := by omega
    have hThreshold : B (q (j + 1) + 1) ≤ freq j := by
      rw [hCurrent]
      exact hk j (le_max_right i k)
    have hAdvance := (frequencySchedule_order_advance_iff (hMax j)).2 hThreshold
    exact ⟨j + 1, by rw [hAdvance, hCurrent]⟩

/-- Equations (1.13)–(1.14) give a schedule satisfying all the conclusions of Lemma 1.3.
    The infinite sequences use the paper's one-based order and zero-based frequency indices. -/
theorem exists_frequencySchedule_satisfying_slow_orders (b : ℕ) (B : ℕ → ℝ) (N : ℝ)
    (hb : 1 ≤ b) (hInit : B 1 ≤ N)
    (hBPos : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s →
      4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) :
    ∃ (q : ℕ → ℕ) (freq : ℕ → ℝ),
      q 1 = 1 ∧ freq 0 = N ∧
      (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) ∧
      (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) ∧
      Tendsto freq atTop atTop ∧ Tendsto q atTop atTop ∧
      (∀ i, q (i + 1) ≤ q (i + 2) ∧ q (i + 2) ≤ q (i + 1) + 1) ∧
      (∀ i, 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2) := by
  have hb' : 0 < b := hb
  have hLog : 0 < Real.log (B 1) := lt_of_lt_of_le
    (by unfold frequencyExponent; positivity) (hFloor 1 le_rfl)
  have hN : 1 < N := ((Real.log_pos_iff (hBPos 1 le_rfl).le).1 hLog).trans_le hInit
  obtain ⟨q, freq, hq, hf, hFreq, hMax⟩ := frequencySchedule_exists b B N hb hN.le hInit
  have hInit' : B 1 ≤ freq 0 := hf ▸ hInit
  have hN' : 1 < freq 0 := hf ▸ hN
  have hMono := frequencySchedule_frequency_mono b q freq hb hN'.le hFreq
  have hGrowth := frequencySchedule_frequency_tendsto_atTop b q freq hb hN' hFreq
  exact ⟨q, freq, hq, hf, hFreq, hMax, hGrowth,
    frequencySchedule_order_tendsto_atTop B freq q hq hInit' hMono hGrowth hMax,
    frequencySchedule_order_steps B freq q hq hInit' hMono hMax,
    frequencySchedule_log_bound_of_maxima b q B freq (fun j => 4 * Real.log (freq (j + 1)))
      hb hq hInit' hFreq (fun _ => rfl) hMax hBPos hFloor⟩

end TorusEuler
