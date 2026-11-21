import TorusEuler.Paper.Proofs.S678a.Library.WaveSelection
import TorusEuler.Paper.Proofs.S678a.Library.LocalStep
import TorusEuler.InductiveLaterWaveSelection
import TorusEuler.Paper.Proofs.S678a.Library.TipThresholds
import TorusEuler.Paper.Proofs.S678a.Library.Common

/-! # The later wave at a certified prefix (package S678a)

Copy of `exists_inductiveEulerTip_laterWave_threshold` (InductiveStageConstruction.lean:932) in
which the selection `exists_frequencySchedule_selectLaterWave` (content of 2.1, 2.2, 2.4, 2.6, 2.8)
is replaced by `Lib.S678a.exists_frequencySchedule_selectLaterWaveV` (from `h2_2`, `h2_5`, `h2_6`, `h2_7`,
`h2_8`): item 2 of the proof of Theorem 7.1 (sections/08b_induction.tex:284-328). -/

open Set

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler MovingWaveVector MovingWaveVector.PhysicalAmplification

noncomputable section

set_option maxHeartbeats 3200000 in
/-- Library-copy of `exists_inductiveEulerTip_laterWave_threshold`: the later-wave selection of Lemmas 2.2, 2.5 and 2.6-2.8 taken from the hypotheses, the schedule (1.15) from `h1_3` and the older-gradient bounds from `hB_1`. -/
theorem exists_inductiveEulerTip_laterWaveV_threshold (hB_1 : Statement.lemma_B_1)
    (h1_3 : Statement.lemma_1_3)
    (h2_2 : Statement.lemma_2_2)
    (h2_5 : Statement.lemma_2_5) (h2_6 : Statement.lemma_2_6) (h2_7 : Statement.lemma_2_7) (h2_8 : Statement.proposition_2_8)
    (C : ℝ) (hC : 2 ≤ C) :
    ∃ (C₀ : ℕ) (N : ℝ), 240 ≤ C₀ ∧ 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        P.LifetimeBounds → N ≤ P.frequency 0 →
        P.strengthConstant = C → P.comparisonConstant = C₀ →
        ∃ w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
          p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation),
          Nonempty (LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
            (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
            (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9)) := by
  have hCp : 0 < C := (by norm_num : (0 : ℝ) < 2).trans_le hC
  obtain ⟨C₀, Nsel, hC₀, hNsel, hSel⟩ :=
    exists_frequencySchedule_selectLaterWaveV h2_2 h2_5 h2_6 h2_7 h2_8 C⁻¹ C (inv_pos.mpr hCp) hCp
  obtain ⟨Nold, _, hOld⟩ := exists_inductiveEulerTip_olderGradient_threshold_of_hB1 hB_1
  refine ⟨C₀, max Nsel Nold, hC₀, hNsel.trans_le (le_max_left _ _), ?_⟩
  intro P n p h hBase hStrengthConstant hComparisonConstant
  have hBaseSel : Nsel ≤ P.frequency 0 := (le_max_left _ _).trans hBase
  have hBaseOld : Nold ≤ P.frequency 0 := (le_max_right _ _).trans hBase
  obtain ⟨w⟩ := p.exists_laterPhysicalWindow h (hNsel.trans_le hBaseSel)
  let Bt (t : ℝ) := derivWithin (fun u => fderiv ℝ (p.older.velocity u) (0 : Vec3))
    (Icc 0 (P.slab n p.olderActivation)) t
  have hBt := hOld p h hBaseOld
  have hB : w.physical.initialStrength =
      ‖p.wave.waveVector p.nextActivation‖ * ‖p.wave.amplitude p.nextActivation‖ := by
    unfold PhysicalAmplification.initialStrength
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq]
  have hν : w.physical.firstCoupling =
      entry (frame p.wave.waveVector p.wave.amplitude p.nextActivation)
        (fderiv ℝ (p.older.velocity p.nextActivation) 0) 0 1 := by
    unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
  have hRatio : w.physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.thirdCoupling
      PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  have hσlo : C⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤ w.physical.initialStrength := by
    rw [hB, ← hStrengthConstant]
    exact p.wave.strength_at_crossing.1
  have hσhi : w.physical.initialStrength ≤
      C * P.frequency (n + 1) ^ (1 / 4 : ℝ) * (4 * Real.log (P.frequency (n + 3))) ^ 2 := by
    rw [hB, ← hStrengthConstant]
    exact p.wave.strength_at_crossing.2
  obtain ⟨hνlo, hνhi⟩ : Real.pi ≤ w.physical.firstCoupling ∧ w.physical.firstCoupling ≤ 4 * Real.pi := by
    rw [hν]
    exact p.wave.coupling_at_crossing
  have hSlab := p.next_activeSlab_subset h
  have hSelect := hSel P.exponentParameter P.order P.threshold P.frequency
    P.exponentParameter_ge P.initial_order P.initial_threshold hBaseSel P.frequency_step
    P.order_maximum P.threshold_pos P.threshold_floor (Lib.S678a.lemma13_schedule h1_3 P).2 n w Bt rfl
    hRatio hσlo hσhi hνlo hνhi
    (fun t ht => (hBt t ht).1) (fun t ht => (hBt t ht).2.1) (fun t ht => (hBt t ht).2.2)
    (fun t ht => p.wave.error_bound t (hSlab ht))
  exact ⟨w, by simpa only [hComparisonConstant] using hSelect⟩

/-- The later steps of a construction from the local data: a base with its local data and a step
with its local data at every certified prefix give a construction with `Theorem71Steps` and the
cutoff equations of the later waves (Section 7, sections/08b_induction.tex:94-140). -/
theorem exists_construction_of_local {P : InductiveEulerParameters} (hLife : P.LifetimeBounds)
    (a : ℕ) (ψ : Vec3 → ℝ) (b : InductiveEulerBase P)
    (hb : LocalStep b.stationary b.first b.wave a ψ)
    (hStep : ∀ (n : ℕ) (tip : InductiveEulerTip P n), InductiveEulerPrefix P hLife n tip →
      ∃ step : InductiveEulerStep tip, LocalStep tip.parent step.child step.wave a ψ ∧
        step.wave.cutoff = waveSwitch tip.nextActivation step.physical.rate) :
    ∃ c : InductiveEulerConstruction P, c.base = b ∧ Theorem71Steps c a ψ ∧
      ∀ i : ℕ, c.centralWaves.cutoff (i + 2) =
        waveSwitch (c.stages.activation (i + 2)) (c.centralWaves.physical i).rate := by
  classical
  let c : InductiveEulerConstruction P :=
    ⟨hLife, b, fun n tip pre => Classical.choose (hStep n tip pre)⟩
  refine ⟨c, rfl, steps_of_local c a ψ hb (fun n =>
    (Classical.choose_spec (hStep n (c.trace n).1 (c.trace n).2)).1), fun i => ?_⟩
  exact (Classical.choose_spec (hStep i (c.trace i).1 (c.trace i).2)).2

end

end TorusEuler.Paper.Lib.S678a
