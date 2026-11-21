import TorusEuler.Paper.Proofs.S678b.Library.Comparison
import TorusEuler.Paper.Proofs.S678a.Library.Common
import TorusEuler.LaterPhysicalAmplification

/-! # The scheduled comparison window of a later wave (package S678a)

Copies of `frequencySchedule_laterWindow_gains` and `exists_frequencySchedule_laterPhysicalWindow`
(LaterPhysicalAmplification.lean:728, :823) in which the logarithmic bound (1.15) is a hypothesis
`hLog` (it is supplied by `h1_3`, `Lib.S678a.lemma13_schedule`) in place of
`frequencySchedule_log_bound_of_maxima` (content of Lemma 1.3). Item 2 of the proof of Theorem 7.1
(sections/08b_induction.tex:39-50, (6.6), finite smallness (2.7)). -/

open Set

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler
open TorusEuler.MovingWaveVector (PhysicalAmplification)
open TorusEuler.AmplificationCrossing (crossingHorizon)

noncomputable section


/-- The two gains for wave (j+2) are three and four frequency indices
ahead of the older velocity (U_j). -/
theorem laterWindow_gains'
    (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ)
    (hb : 1 ≤ b)
    (hbase : 1 < freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hLog : ∀ i, 4 * Real.log (freq (i + 3)) ≤ Real.log (freq i) ^ 2)
    (j : ℕ) :
    let μ := freq (j + 1)
    let L := 4 * Real.log (freq (j + 3))
    let LNext := 4 * Real.log (freq (j + 4))
    1 < μ ∧ Real.log μ ≤ L ∧ 640 * L ≤ LNext ∧ LNext ≤ (Real.log μ) ^ 2 := by
  dsimp only
  let gains := fun i => 4 * Real.log (freq (i + 1))
  have hmono := frequencySchedule_frequency_mono b q freq hb hbase.le hFreq
  have hpositive (i : ℕ) : 1 < freq i := hbase.trans_le (hmono (Nat.zero_le i))
  have hgain := frequencySchedule_gain_ratio b q freq gains (j + 2) hb
    (by simpa [Nat.add_assoc] using (hMax (j + 2)).1.1)
    (by simpa [Nat.add_assoc] using hpositive (j + 3))
    (by simpa [Nat.add_assoc] using hFreq (j + 3)) (fun _ => rfl)
  have hlogs := hLog (j + 1)
  have hlogmono : Real.log (freq (j + 1)) ≤ Real.log (freq (j + 3)) :=
    Real.log_le_log (zero_lt_one.trans (hpositive (j + 1))) (hmono (by omega))
  have hlogpos : 0 ≤ Real.log (freq (j + 3)) := (Real.log_pos (hpositive _)).le
  exact ⟨hpositive _, by linarith only [hlogmono, hlogpos],
    by simpa [gains, Nat.add_assoc] using hgain.2,
    by simpa [gains, Nat.add_assoc] using hlogs⟩


/-- Clock identity of the later physical window: the clock at the window length is the end of the interval and maps `[0,window]` into the interval (primed glue copy). -/
theorem laterPhysicalWindow_clock' {start finish halfTime : ℝ}
    (w : PhysicalAmplification (Icc start finish) start)
    (hFinish : finish = start + 2 * halfTime) :
    let window := 2 * w.rate * halfTime
    w.clock window = finish ∧ MapsTo w.clock (Icc 0 window) (Icc start finish) := by
  intro window
  have hclock : w.clock window = finish := by
    change start + (2 * w.rate * halfTime) / w.rate = finish
    rw [show 2 * w.rate * halfTime = (2 * halfTime) * w.rate by ring,
      mul_div_cancel_right₀ _ w.rate_pos.ne']
    exact hFinish.symm
  refine ⟨hclock, ?_⟩
  intro t ht
  have hlow := w.strictMono_clock.monotone ht.1
  have hhigh := w.strictMono_clock.monotone ht.2
  rw [w.clock_zero] at hlow
  rw [hclock] at hhigh
  exact ⟨hlow, hhigh⟩


set_option maxHeartbeats 650000 in
/-- The physical derivative and residual estimate (6.6), with the scheduled
preceding-wave strengths, gives finite smallness (2.7) uniformly and puts the entire search for
the next crossing in the first half of the actual wave-(j+2) interval. -/
theorem exists_frequencySchedule_laterPhysicalWindow' (C₀ : ℕ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) :
    ∃ N₀ : ℝ, 1 < N₀ ∧
      ∀ (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ),
        1 ≤ b → q 1 = 1 → B 1 ≤ freq 0 → N₀ ≤ freq 0 →
        (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
        (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) →
        (∀ s, 1 ≤ s → 0 < B s) →
        (∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
        (∀ i, 4 * Real.log (freq (i + 3)) ≤ Real.log (freq i) ^ 2) →
        ∀ (j : ℕ) {start finish Bmax Btmax Emax : ℝ}
          (w : PhysicalAmplification (Icc start finish) start),
        let μ := freq (j + 1)
        let L := 4 * Real.log (freq (j + 3))
        let LNext := 4 * Real.log (freq (j + 4))
        let halfTime := inductionHalfLength freq (j + 1)
        let window := 2 * w.rate * halfTime
        let next := couplingRatioOfGain LNext
        finish = start + 2 * halfTime →
        w.ratio = couplingRatioOfGain L →
        c * μ ^ (1 / 4 : ℝ) ≤ w.initialStrength →
        w.initialStrength ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2 →
        Real.pi ≤ w.firstCoupling → w.firstCoupling ≤ 4 * Real.pi →
        0 ≤ Bmax → Bmax ≤ freq j ^ 9 → Btmax ≤ freq j ^ 18 → Emax ≤ μ ^ (-1 / 4 : ℝ) →
        w.errorSize ≤ 8 * (2 * halfTime * (Bmax ^ 2 + Btmax) /
          (w.firstCoupling * w.ratio) + Bmax / w.rate + Emax / w.firstCoupling) →
        ScheduledLaterPhysicalWindowBounds w window halfTime next C₀ := by
  let cRate := Real.sqrt (2 * c * Real.pi)
  let CRate := Real.sqrt (8 * C * Real.pi)
  have hcRate : 0 < cRate := by dsimp [cRate]; positivity [Real.pi_pos]
  have hCRate : 0 < CRate := by dsimp [CRate]; positivity [Real.pi_pos]
  obtain ⟨N, hN, hSmall⟩ :=
    exists_induction_amplification_step_comparison C₀ 8 cRate CRate (by norm_num) hcRate hCRate.le
  let top := max N (Real.exp (1 + 2 / cRate))
  refine ⟨top, hN.trans_le (le_max_left _ _), ?_⟩
  intro b q B freq hb hq hInit hbase hFreq hMax hBPos hFloor hLog j start finish Bmax Btmax Emax w
    μ L LNext halfTime window next hFinish hRatio hσLo hσHi hνLo hνHi hB₀ hB hBt hE hError
  have hbase' : 1 < freq 0 := hN.trans_le ((le_max_left _ _).trans hbase)
  have hmono := frequencySchedule_frequency_mono b q freq hb hbase'.le hFreq
  obtain ⟨hμ, hlogL, hstep, hUpper⟩ :=
    laterWindow_gains' b q B freq hb hbase' hFreq hMax hLog j
  have hμpos : 0 < μ := zero_lt_one.trans hμ
  have hL : 0 < L := (Real.log_pos hμ).trans_le hlogL
  have hLNext : 0 < LNext := (mul_pos (by norm_num : 0 < (640 : ℝ)) hL).trans_le hstep
  have hLmono : L ≤ LNext := by linarith only [hstep, hL]
  have hμlarge : top ≤ μ := hbase.trans (hmono (Nat.zero_le _))
  have hloglarge : 1 + 2 / cRate ≤ Real.log μ := by
    have hlog := Real.log_le_log (Real.exp_pos (1 + 2 / cRate))
      ((le_max_right N (Real.exp (1 + 2 / cRate))).trans hμlarge)
    rwa [Real.log_exp] at hlog
  have hLNextLarge : 2 / cRate ≤ LNext := by linarith only [hloglarge, hlogL, hLmono]
  have hδ₀ : 0 ≤ w.errorSize := Lib.S678b.errorSize_nonneg w
  have hν : 1 ≤ w.firstCoupling := (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi).trans hνLo
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμpos hL.le hc hC hσLo hσHi hνLo hνHi
  have hhalf : halfTime = μ ^ (-1 / 8 : ℝ) * LNext ^ 3 := rfl
  have hhalf₀ : 0 ≤ halfTime := by rw [hhalf]; positivity
  have hRec : μ = freq j ^ frequencyExponent b (q (j + 1)) := hFreq j
  have hold : 1 ≤ freq j := hbase'.le.trans (hmono (Nat.zero_le _))
  have hErrActual : w.errorSize ≤ 8 * (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (Bmax ^ 2 + Btmax) /
      (w.firstCoupling * couplingRatioOfGain L) + Bmax / w.rate + Emax / w.firstCoupling) := by
    rwa [← hhalf, ← hRatio]
  obtain ⟨hT, hsmallε, hsmallδ⟩ := hSmall (r := w.rate) (μ := μ) (L := L) (LNext := LNext)
    (b := b) (q := q (j + 1)) ((le_max_left _ _).trans hμlarge) hb hold hRec hν
    hrLo hrHi hlogL hLmono hUpper hB₀ hB hBt hE hδ₀ hErrActual
  rw [← hhalf, ← hRatio] at hsmallδ
  rw [← hRatio] at hsmallε
  obtain ⟨hclock, hmap⟩ := laterPhysicalWindow_clock' w hFinish
  have hNextPos : 0 < next := inv_pos.mpr (sq_pos_of_pos hLNext)
  have hNextSmall : next ≤ w.ratio / 32 := by
    rw [hRatio]
    exact (couplingRatioOfGain_step hL hstep).2.1
  have hHhalf : crossingHorizon w.ratio next ≤ w.rate * halfTime := by
    have hh := crossingClock_le_endpointHalfLength hμpos hcRate hL hstep hrLo hLNextLarge
    rw [(couplingRatioOfGain_step hL hstep).2.2.1] at hh
    change crossingHorizon w.ratio (couplingRatioOfGain LNext) ≤ w.rate * halfTime
    rw [hRatio, crossingHorizon_eq_of_gains hL hstep, mul_comm w.rate halfTime, hhalf]
    exact (div_le_iff₀ w.rate_pos).mp hh
  have hHalfWin : w.rate * halfTime ≤ window := by
    change w.rate * halfTime ≤ 2 * w.rate * halfTime
    nlinarith only [mul_nonneg w.rate_pos.le hhalf₀]
  have hT' : 2 ≤ window := by
    change 2 ≤ 2 * w.rate * halfTime
    rw [hhalf]
    exact hT
  exact ⟨hT', hclock, hmap, hsmallε, hsmallδ, hNextPos, hNextSmall, hHhalf, hHhalf.trans hHalfWin⟩


end

end TorusEuler.Paper.Lib.S678a
