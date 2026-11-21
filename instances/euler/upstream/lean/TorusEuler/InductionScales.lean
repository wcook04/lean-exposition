import TorusEuler.FrequencySchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The profile scale, crossing clock and cumulative coupling estimates used in
the finite induction of §7.
-/

namespace TorusEuler

/-- The profile width lies in the range of Lemma 3.1. Its product with
the normalized seed scale is the leading velocity scale in §5. -/
theorem profileWidth_and_seedScale {freq : ℝ} (hfreq : 1 ≤ freq) :
    let h := freq ^ (-1 / 2 : ℝ)
    (0 < h ∧ h ≤ 1) ∧ freq ^ (-3 / 4 : ℝ) * h = freq ^ (-5 / 4 : ℝ) := by
  have hpos : 0 < freq := zero_lt_one.trans_le hfreq
  dsimp only
  refine ⟨⟨Real.rpow_pos_of_pos hpos _, Real.rpow_le_one_of_one_le_of_nonpos hfreq (by norm_num)⟩, ?_⟩
  rw [← Real.rpow_add hpos]
  congr 1
  norm_num

/-- The exact ratio of successive logarithmic gains used at the next activation. -/
theorem frequencySchedule_gain_ratio
    (b : ℕ) (q : ℕ → ℕ) (freq L : ℕ → ℝ) (i : ℕ)
    (hb : 1 ≤ b) (hq : 1 ≤ q (i + 2)) (hpos : 1 < freq (i + 1))
    (hfreq : freq (i + 2) = freq (i + 1) ^ frequencyExponent b (q (i + 2)))
    (hL : ∀ j, L j = 4 * Real.log (freq (j + 1))) :
    L (i + 1) / L i = (frequencyExponent b (q (i + 2)) : ℝ) ∧ 640 * L i ≤ L (i + 1) := by
  have hLpos : 0 < L i := by
    rw [hL i]
    exact mul_pos (by norm_num) (Real.log_pos hpos)
  have hstep : L (i + 1) = (frequencyExponent b (q (i + 2)) : ℝ) * L i := by
    rw [hL (i + 1), hL i, hfreq, Real.log_pow]
    ring
  have hK : 640 ≤ frequencyExponent b (q (i + 2)) := by
    unfold frequencyExponent
    change 320 * 1 * 2 ≤ 320 * b * (q (i + 2) + 1)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (by omega)
  constructor
  · rw [hstep, mul_div_cancel_right₀ _ hLpos.ne']
  · rw [hstep]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hLpos.le

/-- The prescribed coupling ratio is the reciprocal of the squared gain. -/
noncomputable def couplingRatioOfGain (L : ℝ) : ℝ := (L ^ 2)⁻¹

/-- The ratio bound and crossing clock used to place the next activation
before the midpoint of the current interval. -/
theorem couplingRatioOfGain_step {L LNext : ℝ} (hL : 0 < L) (hstep : 640 * L ≤ LNext) :
    couplingRatioOfGain LNext =
        (L / LNext) ^ 2 * couplingRatioOfGain L ∧
      couplingRatioOfGain LNext ≤ couplingRatioOfGain L / 32 ∧
      (couplingRatioOfGain L * couplingRatioOfGain LNext) ^ (-1 / 2 : ℝ) =
        L * LNext ∧ L * LNext ≤ LNext ^ 2 := by
  have hNext : 0 < LNext := lt_of_lt_of_le (by positivity : 0 < 640 * L) hstep
  have hmono : L ≤ LNext := by linarith
  have hformula : couplingRatioOfGain LNext = (L / LNext) ^ 2 * couplingRatioOfGain L := by
    unfold couplingRatioOfGain
    field_simp [hL.ne', hNext.ne']
  refine ⟨hformula, ?_, ?_, ?_⟩
  · have hratio : L / LNext ≤ 1 / 640 := by
      apply (div_le_iff₀ hNext).2
      linarith
    have hsq : (L / LNext) ^ 2 ≤ 1 / 32 :=
      (pow_le_pow_left₀ (div_nonneg hL.le hNext.le) hratio 2).trans (by norm_num)
    rw [hformula]
    calc
      _ ≤ (1 / 32) * couplingRatioOfGain L :=
        mul_le_mul_of_nonneg_right hsq (by unfold couplingRatioOfGain; positivity)
      _ = _ := by ring
  · have hnonneg : 0 ≤ couplingRatioOfGain L * couplingRatioOfGain LNext := by
      unfold couplingRatioOfGain
      positivity
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hnonneg, ← Real.sqrt_eq_rpow]
    unfold couplingRatioOfGain
    rw [← mul_inv, ← mul_pow, Real.sqrt_inv, Real.sqrt_sq (mul_nonneg hL.le hNext.le), inv_inv]
  · rw [sq]
    exact mul_le_mul_of_nonneg_right hmono hNext.le

/-- The error in the accumulated logarithm of the first coupling is
bounded by four times the initial ratio. Index zero denotes wave one. -/
theorem firstCoupling_cumulative_log_bound
    (ν ε : ℕ → ℝ) (hν : ∀ i, 0 < ν i) (hε : ∀ i, 0 ≤ ε i)
    (hratio : ∀ i, ε (i + 1) ≤ ε i / 32)
    (hlocal : ∀ i, |Real.log (ν (i + 1) / ν i)| ≤ 2 * ε i) (n : ℕ) :
    |Real.log (ν n / ν 0)| ≤ 4 * ε 0 := by
  have hsum : ∑ i ∈ Finset.range n, Real.log (ν (i + 1) / ν i) =
      Real.log (ν n / ν 0) := by
    simp_rw [Real.log_div (hν _).ne' (hν _).ne']
    exact Finset.sum_range_sub (fun i => Real.log (ν i)) n
  calc
    |Real.log (ν n / ν 0)| = |∑ i ∈ Finset.range n, Real.log (ν (i + 1) / ν i)| := by rw [hsum]
    _ ≤ ∑ i ∈ Finset.range n, |Real.log (ν (i + 1) / ν i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, 4 * (ε i - ε (i + 1)) := by
      refine Finset.sum_le_sum fun i _ => (hlocal i).trans ?_
      linarith [hratio i, hε i]
    _ = 4 * ε 0 - 4 * ε n := by
      have htel := Finset.sum_range_sub (fun i => -(4 * ε i)) n
      simpa only [neg_sub_neg, ← mul_sub] using htel
    _ ≤ 4 * ε 0 := by linarith [hε n]

/-- The scalar part of the conversion of the normalized crossing bracket to
the first half of the endpoint interval in §7. -/
theorem crossingClock_le_endpointHalfLength
    {μ r c L LNext : ℝ} (hμ : 0 < μ) (hc : 0 < c) (hL : 0 < L)
    (hstep : 640 * L ≤ LNext) (hr : c * μ ^ (1 / 8 : ℝ) ≤ r)
    (hlarge : 2 / c ≤ LNext) :
    2 * (couplingRatioOfGain L * couplingRatioOfGain LNext) ^ (-1 / 2 : ℝ) / r ≤
      μ ^ (-1 / 8 : ℝ) * LNext ^ 3 := by
  have hNext : 0 < LNext := (show 0 < 640 * L by positivity).trans_le hstep
  have hrpos : 0 < r := (mul_pos hc (Real.rpow_pos_of_pos hμ _)).trans_le hr
  rw [(couplingRatioOfGain_step hL hstep).2.2.1, div_le_iff₀ hrpos]
  calc
    _ = 2 * (L * LNext) := rfl
    _ ≤ 2 * LNext ^ 2 := mul_le_mul_of_nonneg_left
      (couplingRatioOfGain_step hL hstep).2.2.2 (by norm_num)
    _ ≤ (c * LNext) * LNext ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [mul_comm]
      exact (div_le_iff₀ hc).1 hlarge
    _ = (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (c * μ ^ (1 / 8 : ℝ)) := by
      have hcancel : μ ^ (-1 / 8 : ℝ) * μ ^ (1 / 8 : ℝ) = 1 := by
        rw [← Real.rpow_add hμ]
        norm_num
      calc
        _ = (c * LNext ^ 3) * 1 := by ring
        _ = (c * LNext ^ 3) * (μ ^ (-1 / 8 : ℝ) * μ ^ (1 / 8 : ℝ)) := by rw [hcancel]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

/-- The cumulative log estimate keeps the first coupling in the interval
used at later activations. -/
theorem firstCoupling_pi_bounds
    (ν ε : ℕ → ℝ) (hν : ∀ i, 0 < ν i) (hε : ∀ i, 0 ≤ ε i)
    (hratio : ∀ i, ε (i + 1) ≤ ε i / 32)
    (hlocal : ∀ i, |Real.log (ν (i + 1) / ν i)| ≤ 2 * ε i)
    (hstart : ν 0 = 2 * Real.pi) (hsmall : 4 * ε 0 ≤ Real.log 2) (n : ℕ) :
    Real.pi ≤ ν n ∧ ν n ≤ 4 * Real.pi := by
  have hb := abs_le.mp ((firstCoupling_cumulative_log_bound ν ε hν hε hratio hlocal n).trans hsmall)
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hratio_pos : 0 < ν n / (2 * Real.pi) := div_pos (hν n) hp
  rw [hstart] at hb
  have hlog_half : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlow : 1 / 2 ≤ ν n / (2 * Real.pi) := by
    apply (Real.log_le_log_iff (by norm_num) hratio_pos).1
    rw [hlog_half]
    exact hb.1
  have hupp : ν n / (2 * Real.pi) ≤ 2 :=
    (Real.log_le_log_iff hratio_pos (by norm_num)).1 hb.2
  constructor
  · have h := (le_div_iff₀ hp).1 hlow
    linarith
  · have h := (div_le_iff₀ hp).1 hupp
    linarith

/-- The lower bound on the first coupling gives the reciprocal bound for
`η = νε` used in the comparison error. -/
theorem inverse_secondCoupling_le {ν L : ℝ} (hν : Real.pi ≤ ν) :
    (ν * couplingRatioOfGain L)⁻¹ ≤ L ^ 2 / Real.pi := by
  rw [couplingRatioOfGain, mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (sq_nonneg _) Real.pi_pos hν

/-- The gain prescribed in (1.14) gives the fourth inverse power used in the
cutoff residual during activation. -/
theorem frequencySchedule_switchGain {freq : ℝ} (hfreq : 0 < freq) :
    Real.exp (3 - 4 * Real.log freq) = Real.exp 3 * (freq ^ 4)⁻¹ := by
  rw [Real.exp_sub, show (4 : ℝ) * Real.log freq = Real.log (freq ^ (4 : ℕ)) by
    rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hfreq _), div_eq_mul_inv]

end TorusEuler
