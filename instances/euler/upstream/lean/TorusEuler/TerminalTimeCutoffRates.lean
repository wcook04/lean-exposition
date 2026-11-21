import TorusEuler.InductiveStepNumericalBudgets
import TorusEuler.ScheduleGrowth

/-! Frequency absorption for the differentiated cutoff in the terminal smoothness note. -/

open Filter

namespace TorusEuler

private theorem cutoffPower_eq_rpow {freq : ℝ} (hf : 0 < freq) (m depth : ℕ) :
    (freq ^ (5 : ℕ)) ^ ((m : ℤ) - depth) = freq ^ (5 * ((m : ℝ) - depth)) := by
  rw [← Real.rpow_intCast, ← Real.rpow_natCast freq, ← Real.rpow_mul hf.le]
  push_cast
  norm_num

/-- The cutoff tail absorbs any fixed mixed derivative cost once the
depth is large, at the prescribed cutoff radius. -/
theorem terminalTime_cutoff_tail_rate {freq C exponent : ℝ} {m depth : ℕ}
    (hf : 2 ≤ freq) (hC : C ≤ freq)
    (hDepth : 5 * (m : ℝ) + 5 + exponent ≤ 3 * depth) :
    C * (freq ^ (5 : ℕ)) ^ ((m : ℤ) - depth) * freq ^ (2 * ((depth : ℝ) + 1) + exponent) ≤
      (1 / 2 : ℝ) * freq ^ (-1 : ℝ) := by
  have hf₀ : 0 < freq := zero_lt_two.trans_le hf
  have h₁ : 1 ≤ freq := one_le_two.trans hf
  calc
    _ ≤ freq * (freq ^ (5 : ℕ)) ^ ((m : ℤ) - depth) * freq ^ (2 * ((depth : ℝ) + 1) + exponent) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by positivity)
    _ = freq ^ (5 * (m : ℝ) - 3 * depth + 3 + exponent) := by
      rw [cutoffPower_eq_rpow hf₀]
      conv_lhs => lhs; lhs; rw [← Real.rpow_one freq]
      rw [← Real.rpow_add hf₀, ← Real.rpow_add hf₀]
      congr 1
      ring
    _ ≤ freq ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h₁ (by linarith only [hDepth])
    _ = freq ^ (-1 : ℝ) * freq ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hf₀]
      congr 1
      norm_num
    _ ≤ (1 / 2 : ℝ) * freq ^ (-1 : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [Real.rpow_neg_one]
      exact (inv_anti₀ (show (0 : ℝ) < 2 by norm_num) hf).trans_eq (by norm_num)

/-- Multiplication by the uniform order-zero cutoff constant costs one
fixed power of the scheduled frequency. -/
theorem terminalTime_cutoff_velocity_rate {freq C exponent : ℝ}
    (hf : 2 ≤ freq) (hC : C ≤ freq) :
    C * freq ^ (2 + exponent) ≤ freq ^ (exponent + 3) := by
  have hf₀ : 0 < freq := zero_lt_two.trans_le hf
  calc
    _ ≤ freq * freq ^ (2 + exponent) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one freq]
      rw [← Real.rpow_add hf₀]
      congr 1
      ring

/-- The differentiated residual bound absorbs both the projected residual
and the quadratic cutoff error. -/
theorem terminalTime_cutoff_residual_rate {freq next C R exponent : ℝ} {k : ℕ}
    (hf : 2 ≤ freq) (hExp : 0 ≤ exponent) (hC : C ≤ freq) (hR : R ≤ freq)
    (hNext : next = freq ^ k) (hk : 16 + 2 * exponent ≤ (k : ℝ)) :
    R * (freq ^ exponent * next ^ (-4 : ℝ)) +
      C * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - (6 * k : ℕ)) *
        (freq ^ (2 * (((6 * k : ℕ) : ℝ) + 1) + exponent)) ^ (2 : ℕ)) ≤
      next ^ (-5 / 2 : ℝ) := by
  have hf₀ : 0 < freq := zero_lt_two.trans_le hf
  have h₁ : 1 ≤ freq := one_le_two.trans hf
  have hk₁ : 2 ≤ k := by
    by_contra hn
    have h : (k : ℝ) < 2 := by exact_mod_cast (Nat.lt_of_not_ge hn)
    linarith only [h, hk, hExp]
  have hn : 4 ≤ next := by
    rw [hNext]
    have hf₂ : 4 ≤ freq ^ (2 : ℕ) := by
      simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using pow_le_pow_left₀ (by norm_num) hf 2
    exact hf₂.trans (pow_le_pow_right₀ h₁ hk₁)
  have hn₀ : 0 < next := by linarith only [hn]
  have hFirst : R * (freq ^ exponent * next ^ (-4 : ℝ)) ≤ next ^ (-3 : ℝ) := by
    calc
      _ ≤ freq * (freq ^ exponent * next ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right hR (by positivity)
      _ = freq ^ (exponent + 1) * next ^ (-4 : ℝ) := by
        rw [← mul_assoc, mul_comm freq]
        conv_lhs => lhs; rhs; rw [← Real.rpow_one freq]
        rw [← Real.rpow_add hf₀]
      _ ≤ next * next ^ (-4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hNext, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h₁ (by linarith only [hk, hExp])
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one next]
        rw [← Real.rpow_add hn₀]
        congr 1
        norm_num
  let depth : ℕ := 6 * k
  have hDepth : (depth : ℝ) = 6 * (k : ℝ) := by
    dsimp [depth]
    push_cast
    rfl
  have hSecond : C * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - depth) *
        (freq ^ (2 * ((depth : ℝ) + 1) + exponent)) ^ (2 : ℕ)) ≤ next ^ (-3 : ℝ) := by
    calc
      _ ≤ freq * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - depth) *
          (freq ^ (2 * ((depth : ℝ) + 1) + exponent)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = freq ^ (15 - (depth : ℝ) + 2 * exponent) := by
        rw [show (freq ^ (5 : ℕ)) ^ ((2 : ℤ) - depth) = freq ^ (5 * (2 - (depth : ℝ))) by
          simpa only [Nat.cast_ofNat] using cutoffPower_eq_rpow hf₀ 2 depth]
        rw [← Real.rpow_natCast (freq ^ (_ : ℝ)), ← Real.rpow_mul hf₀.le]
        conv_lhs => lhs; rw [← Real.rpow_one freq]
        rw [← Real.rpow_add hf₀, ← Real.rpow_add hf₀]
        push_cast
        congr 1
        ring
      _ ≤ freq ^ ((k : ℝ) * (-3)) :=
        Real.rpow_le_rpow_of_exponent_le h₁ (by rw [hDepth]; linarith only [hk, hExp])
      _ = _ := by rw [hNext, ← Real.rpow_natCast, ← Real.rpow_mul hf₀.le]
  have hTwo : 2 ≤ next ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 1 hn₀.le]
    simpa only [Real.rpow_one] using Real.le_sqrt_of_sq_le (show (2 : ℝ) ^ 2 ≤ next by norm_num; exact hn)
  calc
    _ ≤ next ^ (-3 : ℝ) + next ^ (-3 : ℝ) := add_le_add hFirst hSecond
    _ = 2 * next ^ (-3 : ℝ) := (two_mul _).symm
    _ ≤ next ^ (1 / 2 : ℝ) * next ^ (-3 : ℝ) := mul_le_mul_of_nonneg_right hTwo (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hn₀]
      congr 1
      norm_num

/-- Any fixed time order and fixed spatial order are eventually admissible
for the two differentiated cutoff absorptions, along the prescribed schedule. -/
theorem terminalTime_cutoff_depth_eventually
    (P : InductiveEulerParameters) (hInit : 1 < P.frequency 0) (m : ℕ) (exponent : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      5 * (m : ℝ) + 5 + exponent ≤ 3 * P.stepDepth j ∧
        16 + 2 * exponent ≤ (frequencyExponent P.exponentParameter (P.order (j + 2)) : ℝ) := by
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hInit.le P.frequency_step
  have hFreq := frequencySchedule_frequency_tendsto_atTop P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hInit P.frequency_step
  have hOrder := frequencySchedule_order_tendsto_atTop P.threshold P.frequency P.order P.initial_order
    P.initial_threshold hMono hFreq P.order_maximum
  obtain ⟨M, hM⟩ := exists_nat_gt (max (5 * (m : ℝ) + 5 + exponent) (16 + 2 * exponent))
  have hEventually := ((tendsto_add_atTop_iff_nat 2).2 hOrder).eventually_ge_atTop M
  filter_upwards [hEventually] with j hj
  let k := frequencyExponent P.exponentParameter (P.order (j + 2))
  have hK : P.order (j + 2) ≤ k := by
    unfold k frequencyExponent
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by
      have hb := P.exponentParameter_ge
      positivity))
  have hMk : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj.trans hK
  refine ⟨?_, (le_max_right _ _).trans (hM.le.trans hMk)⟩
  have hh := (le_max_left (5 * (m : ℝ) + 5 + exponent) (16 + 2 * exponent)).trans (hM.le.trans hMk)
  change 5 * (m : ℝ) + 5 + exponent ≤ 3 * ((6 * k : ℕ) : ℝ)
  push_cast
  linarith only [hh, show (0 : ℝ) ≤ k by positivity]

end TorusEuler
