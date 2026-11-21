import TorusEuler.FrequencySchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Frequency absorption at variable derivative orders and the endpoint half
lengths in §7.
-/

open Filter

namespace TorusEuler

private theorem threeHundredTwenty_le_frequencyExponent {b q : ℕ} (hb : 1 ≤ b) :
    320 ≤ frequencyExponent b q := by
  change 320 * 1 * 1 ≤ 320 * b * (q + 1)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)

private theorem parentScale_power_budget {μ C : ℝ} {b n : ℕ}
    (hμ : 1 ≤ μ) (hC : C ≤ μ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    C * (μ ^ 9) ^ (b * n) ≤ μ ^ (10 * b * n) := by
  have hbn : 1 ≤ b * n := by
    simpa using Nat.mul_le_mul hb hn
  calc
    C * (μ ^ 9) ^ (b * n) ≤ μ * (μ ^ 9) ^ (b * n) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = μ ^ (1 + 9 * (b * n)) := by
      rw [pow_add μ 1, pow_one, pow_mul μ 9]
    _ ≤ μ ^ (10 * b * n) := by
      apply pow_le_pow_right₀ hμ
      rw [Nat.mul_assoc]
      omega

/-- The constant in the low-order mean estimate of §7 is absorbed for
every spatial order `m ≤ q_j`. -/
theorem frequencySchedule_lowOrder_mean_budget {μ C : ℝ} {b q m : ℕ}
    (hμ : 1 ≤ μ) (hC : C ≤ μ) (hb : 1 ≤ b) (hm : m ≤ q) :
    C * (μ ^ 9) ^ (b * (m + 2)) ≤
      (μ ^ frequencyExponent b q) ^ (1 / 16 : ℝ) := by
  refine (parentScale_power_budget hμ hC hb (by omega : 1 ≤ m + 2)).trans ?_
  rw [← Real.rpow_natCast μ (10 * b * (m + 2)),
    ← Real.rpow_natCast μ (frequencyExponent b q), ← Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le hμ
  push_cast [frequencyExponent]
  have hmq : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hq : (0 : ℝ) ≤ q := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show (m : ℝ) + 2 ≤ 2 * (q + 1) by linarith) (show (0 : ℝ) ≤ b by positivity)
  nlinarith only [hmul]

/-- The factor at the full depth `P` in the §7 high-norm estimate. -/
theorem frequencySchedule_fullOrder_wave_budget {μ C : ℝ} {b q P : ℕ}
    (hμ : 1 ≤ μ) (hC : C ≤ μ) (hb : 1 ≤ b) :
    C * (μ ^ 9) ^ (b * (P + 2)) ≤
      (μ ^ frequencyExponent b q) ^ (((P : ℝ) + 2) / 32) := by
  refine (parentScale_power_budget hμ hC hb (by omega : 1 ≤ P + 2)).trans ?_
  rw [← Real.rpow_natCast μ (10 * b * (P + 2)),
    ← Real.rpow_natCast μ (frequencyExponent b q), ← Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le hμ
  push_cast [frequencyExponent]
  have hq : (0 : ℝ) ≤ q := by positivity
  have hmul := mul_nonneg hq (show 0 ≤ (b : ℝ) * (P + 2) from by positivity)
  nlinarith only [hmul]

/-- The larger wave exponent in the §7 full-depth estimate fits below
the power used for the truncation tail. -/
theorem frequencySchedule_fullOrder_wave_exponent (P : ℕ) :
    3 * (P : ℝ) / 2 + 1 / 4 + ((P : ℝ) + 2) / 32 ≤ 2 * ((P : ℝ) + 1) := by
  have : 0 ≤ (P : ℝ) := by positivity
  linarith

/-- The parent Bernstein cost through order `P` fits in the new frequency. -/
theorem frequencySchedule_fullOrder_parent_budget {μ C : ℝ} {b q P : ℕ}
    (hμ : 1 ≤ μ) (hC : C ≤ μ) (hb : 1 ≤ b) :
    C * μ ^ (5 * (P + 1) + 1) ≤ (μ ^ frequencyExponent b q) ^ (P + 2) := by
  have hK : 6 ≤ frequencyExponent b q :=
    (by decide : 6 ≤ 320).trans (threeHundredTwenty_le_frequencyExponent hb)
  calc
    C * μ ^ (5 * (P + 1) + 1) ≤ μ * μ ^ (5 * (P + 1) + 1) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = μ ^ (1 + (5 * (P + 1) + 1)) := by rw [pow_add μ 1, pow_one]
    _ ≤ μ ^ (frequencyExponent b q * (P + 2)) := by
      apply pow_le_pow_right₀ hμ
      exact (show 1 + (5 * (P + 1) + 1) ≤ 6 * (P + 2) by omega).trans
        (Nat.mul_le_mul_right _ hK)
    _ = _ := pow_mul _ _ _

/-- Multiplying by the variable derivative cost of the cutoff still
leaves the fourth inverse power of the next frequency. -/
theorem frequencySchedule_lowOrder_tail_budget {freq : ℝ} {b q qNext m : ℕ}
    (hfreq : 1 ≤ freq) (hb : 1 ≤ b) (hm : m ≤ q) (hq : q ≤ qNext) :
    freq ^ (5 * m) * (freq ^ frequencyExponent b qNext) ^ (-5 : ℝ) ≤
      (freq ^ frequencyExponent b qNext) ^ (-4 : ℝ) := by
  let next := freq ^ frequencyExponent b qNext
  have hnext : 0 < next := pow_pos (zero_lt_one.trans_le hfreq) _
  have hK : 5 * m ≤ frequencyExponent b qNext := by
    have hmq := hm.trans hq
    calc
      5 * m ≤ 320 * 1 * (qNext + 1) := by omega
      _ ≤ frequencyExponent b qNext := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
  change freq ^ (5 * m) * next ^ (-5 : ℝ) ≤ next ^ (-4 : ℝ)
  calc
    _ ≤ next * next ^ (-5 : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hfreq hK) (Real.rpow_nonneg hnext.le _)
    _ = next ^ (1 : ℝ) * next ^ (-5 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hnext]; norm_num

/-- The scalar absorption at the end of the expansion residual estimate. -/
theorem frequencySchedule_residual_budget {freq : ℝ} {b qNext : ℕ}
    (hfreq : 2 ≤ freq) (hb : 1 ≤ b) :
    2 * freq ^ (2 + 1 / 16 : ℝ) * (freq ^ frequencyExponent b qNext) ^ (-4 : ℝ) ≤
      (freq ^ frequencyExponent b qNext) ^ (-7 / 2 : ℝ) := by
  let next := freq ^ frequencyExponent b qNext
  have hf : 0 < freq := by linarith
  have hnext : 0 < next := pow_pos hf _
  have hK : 7 ≤ frequencyExponent b qNext :=
    (by decide : 7 ≤ 320).trans (threeHundredTwenty_le_frequencyExponent hb)
  have hhalf : freq ^ (3 + 1 / 16 : ℝ) ≤ next ^ (1 / 2 : ℝ) := by
    dsimp [next]
    rw [← Real.rpow_natCast freq (frequencyExponent b qNext), ← Real.rpow_mul hf.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hk : (7 : ℝ) ≤ (frequencyExponent b qNext : ℝ) := by exact_mod_cast hK
    linarith
  have hcoef : 2 * freq ^ (2 + 1 / 16 : ℝ) ≤ freq ^ (3 + 1 / 16 : ℝ) := by
    calc
      _ ≤ freq * freq ^ (2 + 1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right hfreq (Real.rpow_nonneg hf.le _)
      _ = freq ^ (1 : ℝ) * freq ^ (2 + 1 / 16 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hf]; norm_num
  change _ * next ^ (-4 : ℝ) ≤ next ^ (-7 / 2 : ℝ)
  calc
    _ ≤ next ^ (1 / 2 : ℝ) * next ^ (-4 : ℝ) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hhalf) (Real.rpow_nonneg hnext.le _)
    _ = _ := by rw [← Real.rpow_add hnext]; norm_num

/-- The half length of the wave-`i+1` endpoint interval. The frequency
index `i` is one less than the wave index. -/
noncomputable def inductionHalfLength (freq : ℕ → ℝ) (i : ℕ) : ℝ :=
  freq i ^ (-1 / 8 : ℝ) * (4 * Real.log (freq (i + 3))) ^ 3

private theorem eventually_log_six_le_rpow :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (6 : ℕ) ≤ x ^ (1 / 16 : ℝ) := by
  filter_upwards
    [(isLittleO_log_rpow_rpow_atTop 6 (show (0 : ℝ) < 1 / 16 by norm_num)).eventuallyLE,
      eventually_ge_atTop (0 : ℝ)] with x hx hx₀
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hx
  rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hx₀ _)] at hx

/-- The actual schedule (1.14) gives the two lifetime inequalities (7.7)
uniformly once its initial frequency exceeds a common threshold. -/
theorem frequencySchedule_halfLength_bounds :
    ∃ N₀ : ℝ, ∀ (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ),
      1 ≤ b → q 1 = 1 → B 1 ≤ freq 0 → N₀ ≤ freq 0 →
      (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
      (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) →
      (∀ s, 1 ≤ s → 0 < B s) →
      (∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
      ∀ i, 0 < inductionHalfLength freq i ∧
        inductionHalfLength freq i ≤ freq i ^ (-1 / 16 : ℝ) ∧
        4 * inductionHalfLength freq (i + 1) ≤ inductionHalfLength freq i := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 eventually_log_six_le_rpow
  refine ⟨max R (max ((4 : ℝ) ^ 8) (Real.exp 1)), ?_⟩
  intro b q B freq hb hq hInit hLarge hFreq hMax hBPos hFloor
  have hexp₀ : Real.exp 1 ≤ freq 0 :=
    (le_max_right ((4 : ℝ) ^ 8) (Real.exp 1)).trans ((le_max_right _ _).trans hLarge)
  have hone₀ : 1 ≤ freq 0 := by
    calc
      1 ≤ Real.exp 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (zero_le_one : (0 : ℝ) ≤ 1)
      _ ≤ freq 0 := hexp₀
  have hmono := frequencySchedule_frequency_mono b q freq hb hone₀ hFreq
  have hbot (i : ℕ) : freq 0 ≤ freq i := hmono (Nat.zero_le i)
  have hfreq (i : ℕ) : 1 ≤ freq i := hone₀.trans (hbot i)
  have hpos (i : ℕ) : 0 < freq i := zero_lt_one.trans_le (hfreq i)
  have hlog (i : ℕ) : 1 ≤ Real.log (freq i) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hexp₀.trans (hbot i))
    rwa [Real.log_exp] at h
  have hbudget (i : ℕ) : 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2 :=
    frequencySchedule_log_bound_of_maxima b q B freq (fun j => 4 * Real.log (freq (j + 1)))
      hb hq hInit hFreq (fun _ => rfl) hMax hBPos hFloor i
  have hupper (i : ℕ) : inductionHalfLength freq i ≤ freq i ^ (-1 / 16 : ℝ) := by
    have hlog6 := hR _ ((le_max_left R _).trans (hLarge.trans (hbot i)))
    have hg : (4 * Real.log (freq (i + 3))) ^ 3 ≤ (Real.log (freq i)) ^ 6 := by
      rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul]
      exact pow_le_pow_left₀ (by linarith [hlog (i + 3)]) (hbudget i) 3
    unfold inductionHalfLength
    calc
      _ ≤ freq i ^ (-1 / 8 : ℝ) * freq i ^ (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left (hg.trans hlog6) (Real.rpow_nonneg (hpos i).le _)
      _ = _ := by rw [← Real.rpow_add (hpos i)]; norm_num
  intro i
  have hgain : 1 ≤ (4 * Real.log (freq (i + 3))) ^ 3 :=
    one_le_pow₀ (by linarith [hlog (i + 3)])
  refine ⟨mul_pos (Real.rpow_pos_of_pos (hpos i) _) (zero_lt_one.trans_le hgain), hupper i, ?_⟩
  have hK : 4 ≤ frequencyExponent b (q (i + 1)) :=
    (by decide : 4 ≤ 320).trans (threeHundredTwenty_le_frequencyExponent hb)
  have hgap : freq i ^ (4 : ℕ) ≤ freq (i + 1) := by
    rw [hFreq]
    exact pow_le_pow_right₀ (hfreq i) hK
  have hcut : 4 ≤ freq i ^ (1 / 8 : ℝ) := by
    have hbase : (4 : ℝ) ^ (8 : ℕ) ≤ freq i :=
      (le_max_left _ (Real.exp 1)).trans ((le_max_right R _).trans (hLarge.trans (hbot i)))
    have h := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  calc
    _ ≤ 4 * freq (i + 1) ^ (-1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left (hupper (i + 1)) (by norm_num)
    _ ≤ 4 * (freq i ^ (4 : ℕ)) ^ (-1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (pow_pos (hpos i) _) hgap (by norm_num)) (by norm_num)
    _ = 4 * freq i ^ (-1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos i).le]
      norm_num
    _ ≤ freq i ^ (1 / 8 : ℝ) * freq i ^ (-1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg (hpos i).le _)
    _ = freq i ^ (-1 / 8 : ℝ) := by rw [← Real.rpow_add (hpos i)]; norm_num
    _ ≤ inductionHalfLength freq i := le_mul_of_one_le_right (Real.rpow_nonneg (hpos i).le _) hgain

end TorusEuler
