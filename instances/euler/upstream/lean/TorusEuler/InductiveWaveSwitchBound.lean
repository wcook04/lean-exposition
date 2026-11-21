import TorusEuler.ActivationProfiles
import TorusEuler.InductionAmplificationSmallness
import TorusEuler.InductiveStageConstruction
import TorusEuler.PhysicalAmplificationCrossing

/-! The scheduled initial switching loss for the actual later wave. -/

open Set

namespace TorusEuler

/-- The scheduled gain converts the switch derivative into a fourth
inverse power of the next frequency. -/
theorem exists_waveSwitch_scheduled_weighted_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {t₀ r μ next : ℝ}, 0 < r → 0 < next → ∀ γ : ℝ → ℝ,
        (∀ t ∈ Icc t₀ (t₀ + 1 / r), |γ t| ≤ Real.exp (3 - 4 * Real.log next)) →
        C * r * Real.exp 3 ≤ μ →
        ∀ t, |deriv (waveSwitch t₀ r) t| * |γ t| ≤ μ * next ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hSwitch⟩ := waveSwitch_weighted_derivative_bound
  refine ⟨C, hC, ?_⟩
  intro t₀ r μ next hr hn γ hγ hRate t
  have h := hSwitch hr (Real.exp_pos (3 - 4 * Real.log next)).le γ hγ t
  rw [abs_mul, frequencySchedule_switchGain hn] at h
  have hInv : (next ^ (4 : ℕ))⁻¹ = next ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hn.le, Real.rpow_ofNat]
  rw [hInv, ← mul_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_right hRate (Real.rpow_nonneg hn.le _))

/-- A sufficiently large parent frequency absorbs the growth rate times
the fixed switch derivative constant. -/
theorem exists_switchRate_threshold (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N : ℝ, 1 < N ∧
      ∀ {μ r L : ℝ}, N ≤ μ → 0 ≤ L → L ≤ (Real.log μ) ^ 2 →
        r ≤ K * μ ^ (1 / 8 : ℝ) * L → C * r * Real.exp 3 ≤ μ := by
  obtain ⟨N, hN, hBudget⟩ := exists_uniform_log_gain_budget (ι := Unit)
    (fun _ => C * K * Real.exp 3) (fun _ => 1) (fun _ => 7 / 8)
    (fun _ => by positivity) (fun _ => by norm_num)
  refine ⟨N, hN, ?_⟩
  intro μ r L hμ hL hLog hRate
  have hp : 0 < μ := (zero_lt_one.trans hN).trans_le hμ
  have hGain : C * K * Real.exp 3 * L ≤ μ ^ (7 / 8 : ℝ) := by
    simpa only [pow_one] using hBudget μ hμ L hL hLog ()
  calc
    C * r * Real.exp 3 ≤ C * (K * μ ^ (1 / 8 : ℝ) * L) * Real.exp 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRate hC) (Real.exp_pos _).le
    _ = (C * K * Real.exp 3 * L) * μ ^ (1 / 8 : ℝ) := by ring
    _ ≤ μ ^ (7 / 8 : ℝ) * μ ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right hGain (Real.rpow_nonneg hp.le _)
    _ = μ := by rw [← Real.rpow_add hp]; norm_num

namespace MovingWaveVector.PhysicalAmplification

/-- The normalized central amplitude is small on the full physical
interval where the time switch can have a nonzero derivative. -/
theorem GrowingCrossing.normalizedAmplitude_early_log_bound
    {I : Set ℝ} {t₀ T scale next freq : ℝ}
    (w : PhysicalAmplification I t₀)
    (d : w.GrowingCrossing T scale (scale ^ (-3 / 4 : ℝ)) next)
    (hScale : 0 < scale) (hL : 0 < 4 * Real.log freq)
    (hRatio : w.ratio = couplingRatioOfGain (4 * Real.log freq)) :
    ∀ t ∈ Icc t₀ (t₀ + 1 / w.rate),
      |scale ^ (3 / 4 : ℝ) * ‖d.amplitude t‖| ≤ Real.exp (3 - 4 * Real.log freq) := by
  have hSq : (Real.sqrt w.ratio)⁻¹ = 4 * Real.log freq := by
    rw [hRatio, couplingRatioOfGain, Real.sqrt_inv, Real.sqrt_sq hL.le, inv_inv]
  intro t ht
  have hGain := d.early_gain t (by simpa only [PhysicalAmplification.clock] using ht)
  rw [hSq] at hGain
  have hCancel : scale ^ (3 / 4 : ℝ) * scale ^ (-3 / 4 : ℝ) = 1 := by
    rw [neg_div, ← Real.rpow_add hScale, add_neg_cancel, Real.rpow_zero]
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hScale.le _) (norm_nonneg _))]
  calc
    _ ≤ scale ^ (3 / 4 : ℝ) * (Real.exp (3 - 4 * Real.log freq) *
        scale ^ (-3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hGain (Real.rpow_nonneg hScale.le _)
    _ = _ := by rw [mul_left_comm, hCancel, mul_one]

end MovingWaveVector.PhysicalAmplification
open MovingWaveVector

/-- The actual physical rate and the early weight of the same selected
later wave have simultaneous scheduled bounds. -/
theorem exists_inductiveEulerTip_switch_time_data
    (Cstrength C : ℝ) (hCstrength : 2 ≤ Cstrength) (hC : 0 ≤ C) :
    ∃ N : ℝ, 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        N ≤ P.frequency 0 → P.strengthConstant = Cstrength →
        ∀ (w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
          p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation))
          (s : LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
            (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
            (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9)),
        0 < P.frequency (n + 3) ∧
          C * w.physical.rate * Real.exp 3 ≤ P.frequency (n + 1) ∧
          ∀ t ∈ Icc p.nextActivation (p.nextActivation + 1 / w.physical.rate),
            |P.frequency (n + 2) ^ (3 / 4 : ℝ) * ‖s.crossing.amplitude t‖| ≤
              Real.exp (3 - 4 * Real.log (P.frequency (n + 3))) := by
  obtain ⟨N, hN, hRate⟩ :=
    exists_switchRate_threshold C (Real.sqrt (8 * Cstrength * Real.pi)) hC (Real.sqrt_nonneg _)
  refine ⟨N, hN, ?_⟩
  intro P n p hBase hStrength w s
  let μ := P.frequency (n + 1)
  let current := P.frequency (n + 2)
  let next := P.frequency (n + 3)
  let L := 4 * Real.log next
  have hBaseOne := hN.trans_le hBase
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hBaseOne.le P.frequency_step
  obtain ⟨hμ, hLog, hStep, hUpper⟩ :=
    frequencySchedule_laterWindow_gains P.exponentParameter P.order P.threshold P.frequency
      P.exponentParameter_ge P.initial_order P.initial_threshold hBaseOne P.frequency_step
      P.order_maximum P.threshold_pos P.threshold_floor n
  have hL : 0 < L := (Real.log_pos hμ).trans_le hLog
  have hLUpper : L ≤ (Real.log μ) ^ 2 := by
    change 640 * L ≤ 4 * Real.log (P.frequency (n + 4)) at hStep
    linarith only [hL, hStep, hUpper]
  have hCurrent : 0 < current := (zero_lt_one.trans hBaseOne).trans_le (hMono (Nat.zero_le _))
  have hNext : 0 < next := (zero_lt_one.trans hBaseOne).trans_le (hMono (Nat.zero_le _))
  have hσ : w.physical.initialStrength =
      ‖p.wave.waveVector p.nextActivation‖ * ‖p.wave.amplitude p.nextActivation‖ := by
    unfold PhysicalAmplification.initialStrength
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq]
  have hν : w.physical.firstCoupling =
      entry (frame p.wave.waveVector p.wave.amplitude p.nextActivation)
        (fderiv ℝ (p.older.velocity p.nextActivation) 0) 0 1 := by
    unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
  have hr : w.physical.ratio = couplingRatioOfGain L := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.thirdCoupling
      PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  have hσLo : Cstrength⁻¹ * μ ^ (1 / 4 : ℝ) ≤ w.physical.initialStrength := by
    rw [hσ, ← hStrength]
    exact p.wave.strength_at_crossing.1
  have hσHi : w.physical.initialStrength ≤ Cstrength * μ ^ (1 / 4 : ℝ) * L ^ 2 := by
    rw [hσ, ← hStrength]
    exact p.wave.strength_at_crossing.2
  have hNu : Real.pi ≤ w.physical.firstCoupling ∧ w.physical.firstCoupling ≤ 4 * Real.pi := by
    rw [hν]
    exact p.wave.coupling_at_crossing
  have hCpos : 0 < Cstrength := zero_lt_two.trans_le hCstrength
  have hRateHi := (activationGrowthRate_bounds (zero_lt_one.trans hμ) hL.le
    (inv_pos.mpr hCpos) hCpos hσLo hσHi hNu.1 hNu.2).2
  have hRateBudget : C * w.physical.rate * Real.exp 3 ≤ μ :=
    hRate (hBase.trans (hMono (Nat.zero_le (n + 1)))) hL.le hLUpper hRateHi
  exact ⟨hNext, hRateBudget, s.crossing.normalizedAmplitude_early_log_bound w.physical hCurrent hL hr⟩

/-- The actual later wave at a certified prefix tip satisfies the
switch derivative bound with the two prescribed neighboring frequencies. -/
theorem exists_inductiveEulerTip_scheduled_switch_bound
    (Cstrength : ℝ) (hCstrength : 2 ≤ Cstrength) :
    ∃ N : ℝ, 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        N ≤ P.frequency 0 → P.strengthConstant = Cstrength →
        ∀ (w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
          p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation))
          (s : LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
            (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
            (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9)),
        ∀ t, |deriv (waveSwitch p.nextActivation w.physical.rate) t| *
          |P.frequency (n + 2) ^ (3 / 4 : ℝ) * ‖s.crossing.amplitude t‖| ≤
          P.frequency (n + 1) * P.frequency (n + 3) ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hSwitch⟩ := exists_waveSwitch_scheduled_weighted_derivative_bound
  obtain ⟨N, hN, hData⟩ := exists_inductiveEulerTip_switch_time_data Cstrength C hCstrength hC
  refine ⟨N, hN, ?_⟩
  intro P n p hBase hStrength w s
  obtain ⟨hNext, hRate, hEarly⟩ := hData p hBase hStrength w s
  exact hSwitch w.physical.rate_pos hNext _ hEarly hRate

end TorusEuler
