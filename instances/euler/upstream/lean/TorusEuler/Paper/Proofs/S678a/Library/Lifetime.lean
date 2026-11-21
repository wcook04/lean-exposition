import TorusEuler.InductiveStageConstruction
import TorusEuler.Theorem11FromInductiveStages
import TorusEuler.Paper.Proofs.S678a.Library.Common

/-! # The lifetime bounds (7.7) with (1.15) taken from Lemma 1.3 (package S678a)

Own glue of row 7.1 (sections/08b_induction.tex:229-236). -/

open Filter

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- Copy of the library's private `threeHundredTwenty_le_frequencyExponent`: `320 ≤ K(q)` for `b ≥ 1`. -/
theorem threeHundredTwenty_le_frequencyExponent {b q : ℕ} (hb : 1 ≤ b) :
    320 ≤ frequencyExponent b q := by
  change 320 * 1 * 1 ≤ 320 * b * (q + 1)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)

/-- Copy of the library's private `eventually_log_six_le_rpow`: `(log x)^6 ≤ x^{1/16}` for large `x`. -/
theorem eventually_log_six_le_rpow :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (6 : ℕ) ≤ x ^ (1 / 16 : ℝ) := by
  filter_upwards
    [(isLittleO_log_rpow_rpow_atTop 6 (show (0 : ℝ) < 1 / 16 by norm_num)).eventuallyLE,
      eventually_ge_atTop (0 : ℝ)] with x hx hx₀
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hx
  rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hx₀ _)] at hx

/-- Copy of `frequencySchedule_halfLength_bounds` (InductionBudget.lean:151, own content of row 7.1:
the lifetime inequalities (7.7), sections/08b_induction.tex:229-236 and the last paragraph) in which
the logarithmic inequality (1.15) is a hypothesis (`hbudget`, to be supplied from `h1_3`) instead of a
call of `frequencySchedule_log_bound_of_maxima`, content of Lemma 1.3. -/
theorem halfLength_bounds_of_budget :
    ∃ N₀ : ℝ, ∀ (b : ℕ) (q : ℕ → ℕ) (freq : ℕ → ℝ),
      1 ≤ b → N₀ ≤ freq 0 →
      (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
      (∀ i, 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2) →
      ∀ i, 0 < inductionHalfLength freq i ∧
        inductionHalfLength freq i ≤ freq i ^ (-1 / 16 : ℝ) ∧
        4 * inductionHalfLength freq (i + 1) ≤ inductionHalfLength freq i := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 eventually_log_six_le_rpow
  refine ⟨max R (max ((4 : ℝ) ^ 8) (Real.exp 1)), ?_⟩
  intro b q freq hb hLarge hFreq hbudget
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


/-- Copy of `exists_lifetime_threshold` (InductiveStageConstruction.lean:63) with (1.15) from `h1_3`
(`Lib.S678a.lemma13_schedule`) in place of the library schedule lemmas that carry Lemma 1.3: a large
initial frequency gives the lifetime bounds (7.7) of every parameter record. -/
theorem exists_lifetime_threshold_of_lemma13 (h1_3 : Statement.lemma_1_3) :
    ∃ N : ℝ, ∀ P : InductiveEulerParameters, N ≤ P.frequency 0 → P.LifetimeBounds := by
  obtain ⟨N, hN⟩ := halfLength_bounds_of_budget
  refine ⟨max N ((4 : ℝ) ^ (16 : ℕ)), fun P hP => ?_⟩
  have h := hN P.exponentParameter P.order P.frequency P.exponentParameter_ge
    ((le_max_left _ _).trans hP) P.frequency_step (Lib.S678a.lemma13_schedule h1_3 P).2
  exact ⟨inductionHalfLength_zero_le_quarter ((le_max_right _ _).trans hP) (h 0).2.1, h⟩

end

end TorusEuler.Paper.Lib.S678a
