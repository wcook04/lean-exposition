import TorusEuler.Paper.Proofs.S678a.Library.CenterWave
import TorusEuler.Paper.Proofs.S678a.Library.LaterWindow
import TorusEuler.LaterPhysicalAmplification

/-! # The later wave over the actual parent (package S678a)

Copy of `exists_frequencySchedule_selectLaterWave` (LaterPhysicalAmplification.lean:1001) with the crossing of Proposition 2.8 (`GrowingCrossing`,
content of 2.1, 2.2, 2.4, 2.6, 2.8) replaced by the crossing built from `h2_5`, `h2_7`, `h2_8`
(`exists_growingCrossingV`) and the center data by `centerWaveOn_of_growingCrossingV` from `h2_6`.
Item 2 of the proof of Theorem 7.1 (sections/08b_induction.tex:284-328). -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler TorusEuler.MovingWaveVector TorusEuler.MovingWaveVector.PhysicalAmplification
open TorusEuler.AmplificationCrossing (crossingHorizon)
open TorusEuler.LocalizedAmplitude (CenterWaveOn)

noncomputable section

set_option maxHeartbeats 600000 in
/-- **The later wave over the actual parent gradient** (copy of `exists_frequencySchedule_selectLaterWave`;
sections/08b_induction.tex:284-328). The scheduled comparison hypotheses construct the later wave:
the crossing comes from `h2_5` (the reference solution), `h2_7`, `h2_8` and the center data (5.5) from `h2_6`. -/
theorem exists_frequencySchedule_selectLaterWaveV (h2_2 : Statement.lemma_2_2) (h2_5 : Statement.lemma_2_5) (h2_6 : Statement.lemma_2_6)
    (h2_7 : Statement.lemma_2_7) (h2_8 : Statement.proposition_2_8) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ (C₀ : ℕ) (N₀ : ℝ), 240 ≤ C₀ ∧ 1 < N₀ ∧
      ∀ (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ),
        1 ≤ b → q 1 = 1 → B 1 ≤ freq 0 → N₀ ≤ freq 0 →
        (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
        (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) →
        (∀ s, 1 ≤ s → 0 < B s) →
        (∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
        (∀ i, 4 * Real.log (freq (i + 3)) ≤ Real.log (freq i) ^ 2) →
        ∀ (j : ℕ) {older parent : Velocity} {kp ap : ℝ → Space}
          {E : ℝ → Space →L[ℝ] Space} {start finish : ℝ}
          (p : LaterPhysicalWindow older parent kp ap E start finish)
          (Bt : ℝ → Space →L[ℝ] Space),
        let w := p.physical
        let μ := freq (j + 1)
        let L := 4 * Real.log (freq (j + 3))
        let LNext := 4 * Real.log (freq (j + 4))
        let half := inductionHalfLength freq (j + 1)
        finish = start + 2 * half →
        w.ratio = couplingRatioOfGain L →
        c * μ ^ (1 / 4 : ℝ) ≤ w.initialStrength →
        w.initialStrength ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2 →
        Real.pi ≤ w.firstCoupling → w.firstCoupling ≤ 4 * Real.pi →
        (∀ t ∈ Icc start finish,
          HasDerivWithinAt (fun u => fderiv ℝ (older u) 0) (Bt t) (Icc start finish) t) →
        (∀ t ∈ Icc start finish, ‖fderiv ℝ (older t) 0‖ ≤ freq j ^ 9) →
        (∀ t ∈ Icc start finish, ‖Bt t‖ ≤ freq j ^ 18) →
        (∀ t ∈ Icc start finish, ‖E t‖ ≤ μ ^ (-1 / 4 : ℝ)) →
        Nonempty (LaterWaveSelection parent w C₀ half (freq (j + 2)) LNext (μ ^ 9)) := by
  obtain ⟨Ncross, hNcross, hExists⟩ := exists_growingCrossingV h2_5 h2_7 h2_8
  obtain ⟨Ncenter, hCenter⟩ := centerWaveOn_of_growingCrossingV h2_6
  let C₀ := max Ncross Ncenter
  obtain ⟨Nsmall, hNsmall, hSchedule⟩ := exists_frequencySchedule_laterPhysicalWindow' C₀ c C hc hC
  obtain ⟨Nparams, hNparams, hParams⟩ := PhysicalAmplification.exists_later_center_bounds C hC
  let N := max (max Nsmall Nparams) (Real.exp 1)
  have hSmallN : Nsmall ≤ N := (le_max_left Nsmall Nparams).trans (le_max_left _ _)
  have hParamsN : Nparams ≤ N := (le_max_right Nsmall Nparams).trans (le_max_left _ _)
  refine ⟨C₀, N, hNcross.trans (le_max_left _ _), hNsmall.trans_le hSmallN, ?_⟩
  intro b q B freq hb hq hInit hbase hFreq hMax hBpos hFloor hLog j older parent kp ap E start finish p Bt
    w μ L LNext half hFinish hRatio hσlo hσhi hνlo hνhi hBd hB hBt hE
  have hbase₁ : 1 < freq 0 := hNsmall.trans_le (hSmallN.trans hbase)
  have hMono := frequencySchedule_frequency_mono b q freq hb hbase₁.le hFreq
  have hμlarge : N ≤ μ := hbase.trans (hMono (Nat.zero_le _))
  obtain ⟨hμ, hLogL, hStep, hUpper⟩ :=
    laterWindow_gains' b q B freq hb hbase₁ hFreq hMax hLog j
  have hL : 0 < L := (Real.log_pos hμ).trans_le hLogL
  have hLNext : L ≤ LNext := by linarith only [hStep, hL]
  have hLone : 1 ≤ L := by
    have hs := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right (max Nsmall Nparams) (Real.exp 1)).trans hμlarge)
    rw [Real.log_exp] at hs
    exact hs.trans hLogL
  have hEps : w.ratio ≤ 1 := by
    rw [hRatio, couplingRatioOfGain, ← one_div, div_le_iff₀ (sq_pos_of_pos hL)]
    simpa only [one_mul] using (one_le_pow₀ hLone : 1 ≤ L ^ (2 : ℕ))
  have hG : ∀ t ∈ Icc start finish, HasDerivWithinAt w.B (Bt t) (Icc start finish) t := by
    change ∀ t ∈ Icc start finish, HasDerivWithinAt p.physical.B (Bt t) (Icc start finish) t
    rwa [p.older_gradient_eq]
  have hGnorm : ∀ t ∈ Icc start finish, ‖w.B t‖ ≤ freq j ^ 9 := by
    change ∀ t ∈ Icc start finish, ‖p.physical.B t‖ ≤ freq j ^ 9
    rwa [p.older_gradient_eq]
  have hEnorm : ∀ t ∈ Icc start finish, ‖w.E t‖ ≤ μ ^ (-1 / 4 : ℝ) := by
    change ∀ t ∈ Icc start finish, ‖p.physical.E t‖ ≤ μ ^ (-1 / 4 : ℝ)
    rwa [p.error_eq]
  have hη : w.thirdCoupling = w.firstCoupling * w.ratio := by
    calc
      _ = (w.thirdCoupling / w.firstCoupling) * w.firstCoupling :=
        (div_mul_cancel₀ _ w.first_coupling_positive.ne').symm
      _ = _ := mul_comm _ _
  have hTime : finish - start = 2 * half := by linarith only [hFinish]
  have hError := Lib.S678b.errorSize_le h2_2 w hEps Bt hG hGnorm hBt hEnorm
  rw [hTime, hη] at hError
  have hB₀ : 0 ≤ freq j ^ 9 :=
    pow_nonneg (zero_le_one.trans (hbase₁.le.trans (hMono (Nat.zero_le _)))) _
  obtain ⟨hT, hClock, hMap, hSmallε, hSmallδ, hNext, hNextSmall, hHorizonHalf, hHorizon⟩ :=
    hSchedule b q B freq hb hq hInit (hSmallN.trans hbase) hFreq hMax hBpos hFloor hLog j w
      hFinish hRatio hσlo hσhi hνlo hνhi hB₀ le_rfl le_rfl le_rfl hError
  let T := 2 * w.rate * half
  let scale := freq (j + 2)
  let next := couplingRatioOfGain LNext
  have hscale : 0 < scale := zero_lt_one.trans_le (hbase₁.le.trans (hMono (Nat.zero_le _)))
  have hPeak : 0 < scale ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos hscale _
  obtain ⟨d⟩ := hExists (le_max_left Ncross Ncenter) w hClock hT hscale hPeak
    hSmallε hSmallδ hNext hNextSmall hHorizon
  have hRate := (activationGrowthRate_bounds (zero_lt_one.trans hμ) hL.le hc hC
    hσlo hσhi hνlo hνhi).2
  obtain ⟨hGrowth, hInvCoupling⟩ := hParams w (hParamsN.trans hμlarge) hL
    (hLNext.trans hUpper) hνlo hRatio hRate
  have hCenterOn : CenterWaveOn w.gradient d.waveVector d.amplitude start finish (μ ^ 9) :=
    hCenter (le_max_right Ncross Ncenter) w hClock hT hscale hSmallε hSmallδ d (μ ^ 9)
      hGrowth hInvCoupling
  have hFirstHalf : d.crossing - start ≤ half :=
    d.delay_bounds.2.trans ((div_le_iff₀ w.rate_pos).mpr (by
      simpa only [mul_comm half] using hHorizonHalf))
  have hStartCross : start < d.crossing := by
    have h := d.crossing_after_switch
    unfold PhysicalAmplification.clock at h
    linarith only [h, one_div_pos.mpr w.rate_pos]
  exact ⟨⟨T, rfl, hT, hClock, hSmallε, hSmallδ, d, hStartCross, hFirstHalf,
    hCenterOn.congr_gradient p.parent_gradient_eq⟩⟩


end

end TorusEuler.Paper.Lib.S678a
