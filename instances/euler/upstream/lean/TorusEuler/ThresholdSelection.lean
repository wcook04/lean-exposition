import TorusEuler.ScheduleGrowth
import TorusEuler.InductionBudget

/-! The fixed-order thresholds in (1.13) and their use in the step estimates of §7. -/

namespace TorusEuler

open scoped BigOperators

private noncomputable def fixedOrderCostSum {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ k : ι, ∑ m ∈ Finset.range (7 * frequencyExponent b s + 1),
    ∑ p ∈ Finset.range (7 * frequencyExponent b s + 1), |cost k m p|

/-- A positive majorant for a finite family of order- and depth-dependent
constants, with the logarithmic floor of (1.13). -/
noncomputable def fixedOrderThreshold {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (s : ℕ) : ℝ :=
  max (Real.exp (4 * (frequencyExponent b (s + 1) : ℝ) ^ 3)) (fixedOrderCostSum b cost s)

theorem fixedOrderThreshold_pos {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (s : ℕ) : 0 < fixedOrderThreshold b cost s :=
  (Real.exp_pos _).trans_le (le_max_left _ _)

theorem fixedOrderThreshold_log_floor {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (s : ℕ) :
    4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (fixedOrderThreshold b cost s) := by
  have h := Real.log_le_log (Real.exp_pos (4 * (frequencyExponent b (s + 1) : ℝ) ^ 3))
    (show Real.exp (4 * (frequencyExponent b (s + 1) : ℝ) ^ 3) ≤ fixedOrderThreshold b cost s
      from le_max_left _ _)
  rwa [Real.log_exp] at h

theorem fixedOrderThreshold_mono {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) : Monotone (fixedOrderThreshold b cost) := by
  intro s t hst
  have hK := frequencyExponent_mono b hst
  have hR : Finset.range (7 * frequencyExponent b s + 1) ⊆
      Finset.range (7 * frequencyExponent b t + 1) :=
    Finset.range_mono (by omega)
  have hK' : (frequencyExponent b (s + 1) : ℝ) ≤ frequencyExponent b (t + 1) := by
    exact_mod_cast frequencyExponent_mono b (Nat.add_le_add_right hst 1)
  refine max_le_max (Real.exp_le_exp.mpr ?_) ?_
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hK' 3) (by norm_num)
  · unfold fixedOrderCostSum
    apply Finset.sum_le_sum
    intro k _
    calc
      _ ≤ ∑ m ∈ Finset.range (7 * frequencyExponent b s + 1),
          ∑ p ∈ Finset.range (7 * frequencyExponent b t + 1), |cost k m p| := by
        exact Finset.sum_le_sum fun _ _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hR fun _ _ _ => abs_nonneg _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hR fun _ _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- All constants at differentiation order and expansion depth at most `7K(s)`
are bounded simultaneously, including the order-zero estimates. -/
theorem abs_fixedOrderCost_le_threshold {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (k : ι) {s m p : ℕ}
    (hm : m ≤ 7 * frequencyExponent b s) (hp : p ≤ 7 * frequencyExponent b s) :
    |cost k m p| ≤ fixedOrderThreshold b cost s := by
  let range := Finset.range (7 * frequencyExponent b s + 1)
  have hm' : m ∈ range := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hp' : p ∈ range := Finset.mem_range.mpr (Nat.lt_succ_of_le hp)
  calc
    _ ≤ ∑ r ∈ range, |cost k m r| :=
      Finset.single_le_sum (fun r _ => abs_nonneg (cost k m r)) hp'
    _ ≤ ∑ n ∈ range, ∑ r ∈ range, |cost k n r| :=
      Finset.single_le_sum (fun n _ => Finset.sum_nonneg fun r _ => abs_nonneg (cost k n r)) hm'
    _ ≤ fixedOrderCostSum b cost s :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun n _ =>
        Finset.sum_nonneg fun r _ => abs_nonneg (cost j n r)) (Finset.mem_univ k)
    _ ≤ _ := le_max_right _ _

open Filter in
/-- The schedule of Appendix C with the explicit thresholds (1.13), including
simultaneous domination of all fixed-order costs by the current base frequency. -/
theorem exists_frequencySchedule_with_fixedOrderCosts {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (N : ℝ)
    (hb : 1 ≤ b) (hN : fixedOrderThreshold b cost 1 ≤ N) :
    ∃ (q : ℕ → ℕ) (freq : ℕ → ℝ),
      q 1 = 1 ∧ freq 0 = N ∧
      (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) ∧
      (∀ i, IsGreatest
        {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ fixedOrderThreshold b cost s ≤ freq i} (q (i + 2))) ∧
      Tendsto freq atTop atTop ∧ Tendsto q atTop atTop ∧
      (∀ i, q (i + 1) ≤ q (i + 2) ∧ q (i + 2) ≤ q (i + 1) + 1) ∧
      (∀ i, 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2) ∧
      ∀ i k m p, m ≤ 7 * frequencyExponent b (q (i + 2)) →
        p ≤ 7 * frequencyExponent b (q (i + 2)) → |cost k m p| ≤ freq i := by
  obtain ⟨q, freq, hq, hf, hFreq, hMax, hGrow, hOrders, hSteps, hLog⟩ :=
    exists_frequencySchedule_satisfying_slow_orders b (fixedOrderThreshold b cost) N hb hN
      (fun s _ => fixedOrderThreshold_pos b cost s)
      (fun s _ => fixedOrderThreshold_log_floor b cost s)
  exact ⟨q, freq, hq, hf, hFreq, hMax, hGrow, hOrders, hSteps, hLog,
    fun i k _ _ hm hp => (abs_fixedOrderCost_le_threshold b cost k hm hp).trans (hMax i).1.2.2⟩

/-- The step constant is absorbed at the powers used in (7.8) and (7.11). -/
theorem frequencySchedule_step_constant_budget {μ B : ℝ} {b q : ℕ}
    (hb : 1 ≤ b) (hμ : 1 ≤ μ) (hB : B ≤ μ) :
    let D := μ ^ 9
    let freq := μ ^ frequencyExponent b q
    B * D ^ b ≤ μ ^ (10 * b) ∧
      μ ^ (10 * b) ≤ freq ^ (1 / 32 : ℝ) ∧
      (B * D ^ b) * μ ≤ freq ^ (1 / 16 : ℝ) := by
  have hbase : B * (μ ^ 9) ^ b ≤ μ ^ (10 * b) := by
    calc
      _ ≤ μ * (μ ^ 9) ^ b := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = μ ^ (1 + 9 * b) := by rw [pow_add μ 1, pow_one, pow_mul μ 9]
      _ ≤ _ := pow_le_pow_right₀ hμ (by omega)
  have hexp : 10 * b ≤ ((frequencyExponent b q : ℕ) : ℝ) * (1 / 32 : ℝ) := by
    unfold frequencyExponent
    push_cast
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ b by positivity) (show (0 : ℝ) ≤ q by positivity)]
  have hfreq : μ ^ (10 * b) ≤ (μ ^ frequencyExponent b q) ^ (1 / 32 : ℝ) := by
    rw [← Real.rpow_natCast μ (10 * b), ← Real.rpow_natCast μ (frequencyExponent b q),
      ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hμ (by push_cast; exact hexp)
  refine ⟨hbase, hfreq, ?_⟩
  calc
    _ ≤ μ ^ (10 * b) * μ := mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = μ ^ (10 * b + 1) := (pow_succ μ _).symm
    _ ≤ μ ^ (20 * b) := pow_le_pow_right₀ hμ (by omega)
    _ ≤ _ := by
      rw [← Real.rpow_natCast μ (20 * b), ← Real.rpow_natCast μ (frequencyExponent b q),
        ← Real.rpow_mul (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le hμ
      push_cast
      linarith

/-- The actual maximum in (1.14) supplies every fixed-order constant at the
chosen depth and the scale budgets in the proof of Theorem 7.1. -/
theorem frequencySchedule_fixedOrder_budget {ι : Type*} [Fintype ι]
    {b : ℕ} (cost : ι → ℕ → ℕ → ℝ) {q : ℕ → ℕ} {freq : ℕ → ℝ}
    (hb : 1 ≤ b) (hN : 1 ≤ freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMax : ∀ i, IsGreatest
      {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ fixedOrderThreshold b cost s ≤ freq i} (q (i + 2)))
    (i : ℕ) :
    let s := q (i + 2)
    let P := 6 * frequencyExponent b s
    let μ := freq i
    let D := μ ^ 9
    let waveFreq := freq (i + 1)
    P + 1 ≤ 7 * frequencyExponent b s ∧
      (∀ k m p, m ≤ P + 1 → p ≤ P + 1 → |cost k m p| ≤ μ) ∧
      fixedOrderThreshold b cost s * D ^ b ≤ waveFreq ^ (1 / 32 : ℝ) ∧
      (fixedOrderThreshold b cost s * D ^ b) * μ ≤ waveFreq ^ (1 / 16 : ℝ) := by
  have hK : 1 ≤ frequencyExponent b (q (i + 2)) := by
    have hb' : 0 < b := hb
    change 0 < frequencyExponent b (q (i + 2))
    unfold frequencyExponent
    positivity
  have hP : 6 * frequencyExponent b (q (i + 2)) + 1 ≤ 7 * frequencyExponent b (q (i + 2)) := by
    omega
  have hB := (hMax i).1.2.2
  have hμ := hN.trans (frequencySchedule_frequency_mono b q freq hb hN hFreq (Nat.zero_le i))
  obtain ⟨h₁, h₂, h₃⟩ := frequencySchedule_step_constant_budget (q := q (i + 1)) hb hμ hB
  rw [← hFreq i] at h₂ h₃
  exact ⟨hP, fun k m p hm hp => (abs_fixedOrderCost_le_threshold b cost k (hm.trans hP)
    (hp.trans hP)).trans hB, h₁.trans h₂, h₃⟩

/-- The cutoff-tail absorption in (7.12), with depth `P = 6 K(qNext)` and cutoff
frequency `waveFreq ^ 5`. The prefactor accounts for the squared bound on
`1 + ‖V‖`. -/
theorem frequencySchedule_cutoff_tail_budget {μ : ℝ} {b q qNext : ℕ}
    (hb : 1 ≤ b) (hμ : 2 ≤ μ) :
    let waveFreq := μ ^ frequencyExponent b q
    let next := waveFreq ^ frequencyExponent b qNext
    let P := 6 * frequencyExponent b qNext
    9 * μ * waveFreq ^ (5 * (2 - (P : ℝ)) + 4 * ((P : ℝ) + 1)) ≤ next ^ (-5 : ℝ) := by
  let waveFreq := μ ^ frequencyExponent b q
  let next := waveFreq ^ frequencyExponent b qNext
  let P := 6 * frequencyExponent b qNext
  have hK (s : ℕ) : 320 ≤ frequencyExponent b s := by
    change 320 * 1 * 1 ≤ 320 * b * (s + 1)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)
  have hμ₀ : 0 ≤ μ := by linarith
  have hμ₁ : 1 ≤ μ := by linarith
  have hWaveFreq₁ : 1 ≤ waveFreq := one_le_pow₀ hμ₁
  have hWaveFreq₀ : 0 < waveFreq := zero_lt_one.trans_le hWaveFreq₁
  have hWaveFreq : 9 * μ ≤ waveFreq := by
    calc
      _ ≤ μ ^ (4 : ℕ) * μ := mul_le_mul_of_nonneg_right
        ((by norm_num : (9 : ℝ) ≤ 2 ^ (4 : ℕ)).trans
          (pow_le_pow_left₀ (by norm_num) hμ 4)) hμ₀
      _ = μ ^ (5 : ℕ) := (pow_succ μ 4).symm
      _ ≤ _ := pow_le_pow_right₀ hμ₁ ((by decide : 5 ≤ 320).trans (hK q))
  have hP : (P : ℝ) = 6 * (frequencyExponent b qNext : ℝ) := by
    norm_cast
  have hK' : (15 : ℝ) ≤ frequencyExponent b qNext := by
    exact_mod_cast (show 15 ≤ 320 from by decide).trans (hK qNext)
  change _ ≤ next ^ (-5 : ℝ)
  calc
    _ ≤ waveFreq * waveFreq ^ (5 * (2 - (P : ℝ)) + 4 * ((P : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hWaveFreq (Real.rpow_nonneg hWaveFreq₀.le _)
    _ = waveFreq ^ (1 : ℝ) * waveFreq ^ (5 * (2 - (P : ℝ)) + 4 * ((P : ℝ) + 1)) := by
      rw [Real.rpow_one]
    _ = waveFreq ^ (15 - (P : ℝ)) := by
      rw [← Real.rpow_add hWaveFreq₀]
      congr 1
      ring
    _ ≤ waveFreq ^ ((frequencyExponent b qNext : ℝ) * (-5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hWaveFreq₁ (by linarith)
    _ = next ^ (-5 : ℝ) := by
      rw [Real.rpow_mul hWaveFreq₀.le, Real.rpow_natCast]

end TorusEuler
