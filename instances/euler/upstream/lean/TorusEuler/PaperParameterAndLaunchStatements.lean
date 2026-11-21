import TorusEuler.ScheduleGrowth
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.WaveProfile

/-! Statement-level checks for the frozen schedule, phase profile, and initial wave. -/

open Filter Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- `cc:uf:tower:lem:slow-orders`, with `i = j - 1`. The gain `L_(j+1)` is
`4 * log (freq (i+3))` under the schedule in (1.14). -/
theorem paperLemma13_slowOrders (b : ℕ) (B freq : ℕ → ℝ) (q : ℕ → ℕ)
    (hb : 1 ≤ b) (hq : q 1 = 1) (hInitial : B 1 ≤ freq 0)
    (hFrequency : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMaximum : ∀ i,
      IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hPositive : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) :
    (∀ i, q (i + 1) ≤ q (i + 2) ∧ q (i + 2) ≤ q (i + 1) + 1) ∧
      Tendsto q atTop atTop ∧ ∀ i, 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2 := by
  have hbPos : 0 < b := hb
  have hLog : 0 < Real.log (B 1) :=
    (show 0 < 4 * (frequencyExponent b 2 : ℝ) ^ 3 by unfold frequencyExponent; positivity).trans_le
      (hFloor 1 le_rfl)
  have hFreq : 1 < freq 0 := ((Real.log_pos_iff (hPositive 1 le_rfl).le).1 hLog).trans_le hInitial
  have hMono := frequencySchedule_frequency_mono b q freq hb hFreq.le hFrequency
  have hGrowth := frequencySchedule_frequency_tendsto_atTop b q freq hb hFreq hFrequency
  refine ⟨frequencySchedule_order_steps B freq q hq hInitial hMono hMaximum,
    frequencySchedule_order_tendsto_atTop B freq q hq hInitial hMono hGrowth hMaximum, ?_⟩
  exact frequencySchedule_log_bound_of_maxima b q B freq (fun j => 4 * Real.log (freq (j + 1)))
    hb hq hInitial hFrequency (fun _ => rfl) hMaximum hPositive hFloor

/-- `cc:uf:exact:lem:profile`. Bounds are pointwise in phase, so each also
bounds the supremum over a period. Uniform constants are chosen after the
two profile families and before the scale and phase. -/
theorem paperLemma31_waveProfile :
    ∃ (F P : ℝ → ℝ → ℝ) (C : ℝ), 0 < C ∧
      (∀ h, 0 < h → h ≤ 1 →
        ContDiff ℝ ∞ (F h) ∧ Function.Odd (F h) ∧ Function.Periodic (F h) 1 ∧
        ContDiff ℝ ∞ (P h) ∧ Function.Periodic (P h) 1 ∧ phaseMean (P h) = 0 ∧
        (∀ s, HasDerivAt (P h) (F h s) s) ∧ deriv (F h) 0 = 1 ∧
        ∀ s, -C * h ≤ deriv (F h) s ∧ deriv (F h) s ≤ 1 ∧ ‖F h s‖ ≤ C * h) ∧
      ∀ j : ℕ, 2 ≤ j → ∃ Cj : ℝ, 0 < Cj ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
        ‖iteratedDeriv j (F h) s‖ ≤ Cj * h ^ (1 - (j : ℤ)) := by
  obtain ⟨C, hC, hProfile, hDerivatives⟩ := lemma31_waveProfile
  exact ⟨waveProfile, wavePressurePrimitive, C, hC, hProfile, hDerivatives⟩

open MovingWaveVector in
/-- The two conditions in `cc:uf:tower:eq:wave-origin` are
expressed using the actual normalized weight and moving frame. -/
structure PaperFirstWaveConclusion {s T freq : ℝ} (w : FirstWaveOrigin s T freq) : Prop where
  propagation : ∀ D : ℝ, 2 ≤ D → ∀ b : ℝ → Vec3,
    (∀ t ∈ Icc 0 T, HasDerivWithinAt b
      (affineWaveAmplitudeOperator (stationaryShearGradient s) (w.covector t) (b t)) (Icc 0 T) t) →
    (∀ t ∈ Icc 0 T, ⟪w.covector t, b t⟫_ℝ = 0) →
    ∀ {t' t : ℝ}, t' ∈ Icc 0 T → t ∈ Icc 0 T → t' ≤ t →
      let γ (u : ℝ) := freq ^ (3 / 4 : ℝ) * ‖w.amplitude u‖
      ‖b t‖ / γ t ≤ D * (‖b t'‖ / γ t')
  coupling : ∀ D : ℝ, 2 ≤ D → ∀ t ∈ Icc 0 T,
    D⁻¹ ≤ entry (frame w.covector w.amplitude t) (stationaryShearGradient s) 0 1
  initialStrength :
    freq ^ (1 / 4 : ℝ) / 2 ≤ ‖w.covector 0‖ * ‖w.amplitude 0‖ ∧
    ‖w.covector 0‖ * ‖w.amplitude 0‖ ≤ freq ^ (1 / 4 : ℝ)

/-- `cc:uf:base:lem:first` for the normalized first wave on the stationary shear. -/
theorem paperLemma61_firstWave {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hs : 0 < s) (hs₁ : s ≤ 1) (hf : 0 < freq)
    (hSmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) : PaperFirstWaveConclusion w := by
  have hTilt : |s| ≤ 1 := by simpa only [abs_of_pos hs] using hs₁
  refine ⟨?_, ?_, w.initial_strength hf hSmall⟩
  · intro D hD b hb _ t' t ht' ht hTime
    exact w.weighted_forward hf hSmall hD ht' ht hTime hb
  · intro D hD t ht
    have hInv : D⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_two.trans_le hD)).2 (one_le_two.trans hD)
    have hPi : (1 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
    exact hInv.trans (hPi.trans (w.first_coupling_lower hf hTilt hSmall ht))

/-- The peak-normalized stationary-shear launch exists and satisfies the
first-wave lemma at every real positive carrier frequency. -/
theorem paperLemma61_exists_firstWave {s T freq : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) (hT : 0 ≤ T) (hf : 0 < freq)
    (hSmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) :
    ∃ w : FirstWaveOrigin s T freq, PaperFirstWaveConclusion w := by
  obtain ⟨w⟩ := firstWaveOrigin_exists (s := s) hT hf
  exact ⟨w, paperLemma61_firstWave w hs hs₁ hf hSmall⟩

end TorusEuler
