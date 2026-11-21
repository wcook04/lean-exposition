import TorusEuler.Paper.Proofs.S678a.Library.ParentBridge
import TorusEuler.Paper.Proofs.S678a.Library.LaterWindow
import TorusEuler.Paper.Proofs.S678a.Library.Lifetime
import TorusEuler.Paper.Proofs.S678a.Library.Common
import TorusEuler.InductiveWaveSwitchBound
import TorusEuler.InductiveLaterWaveSelection

/-! # Threshold lemmas at a certified prefix (package S678a)

Copies of `exists_inductiveEulerTip_olderGradient_threshold` (InductiveStageConstruction.lean:904,
via `exists_older_central_gradient_raw_bounds_of_projectedMomentum`) with the Bernstein step from
`hB_1` (`projectedMomentum_bounds_of_hB1`) and of `exists_inductiveEulerTip_scheduled_switch_bound`
(InductiveWaveSwitchBound.lean:150, via `exists_inductiveEulerTip_switch_time_data`) with (1.15)
from `h1_3` (`Lib.S678a.lemma13_schedule`, `laterWindow_gains'`) in place of the library
schedule lemmas that carry Lemma 1.3 and Lemma B.1. Items 2 and 4 of the proof of Theorem 7.1
(sections/08b_induction.tex:284-328, :368-374). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler MovingWaveVector MovingWaveVector.PhysicalAmplification

noncomputable section

/-- The older central gradient bounds from the closed-slab projected momentum identity (copy of
`exists_older_central_gradient_raw_bounds_of_projectedMomentum` with `hB_1`). -/
theorem older_central_gradient_raw_bounds_of_hB1 (hB_1 : Statement.lemma_B_1) :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T l r old μ : ℝ}, 0 < T → 0 ≤ l → r ≤ T →
        N ≤ old → 1 ≤ μ →
        ∀ (U : ℝ → C(UnitAddTorus (Fin 3), Vec3)) (R : Velocity),
          (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (R t)) →
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          let B := fun t => fderiv ℝ (u t) (0 : Vec3)
          let Bt := fun t => derivWithin B (Icc 0 T) t
          ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
            ‖B t‖ ≤ old ^ 9 ∧ ‖Bt t‖ ≤ old ^ 18 := by
  obtain ⟨N, K, hN, _, hBounds⟩ := projectedMomentum_bounds_of_hB1 hB_1
  refine ⟨N, hN, ?_⟩
  intro T l r old μ hT hl hr hOld hμ₁ U R hRs u hSmooth hU hDiv hMom hR
  obtain ⟨_, _, _, _, _, _, _, hSpatial⟩ := hBounds hT hOld hμ₁ U R hRs hSmooth hU hDiv hMom hR
  exact older_central_gradient_raw_bounds_of_derivedLowBounds hT hl hr (hSmooth.of_le (by simp))
    (fun t ht => ⟨(hSpatial t ht 0).1, (hSpatial t ht 0).2.1⟩)

set_option maxHeartbeats 800000 in
/-- The older truncated stage supplies its raw central gradient bounds on the actual later
comparison interval (copy of `exists_inductiveEulerTip_olderGradient_threshold` with `hB_1`). -/
theorem exists_inductiveEulerTip_olderGradient_threshold_of_hB1 (hB_1 : Statement.lemma_B_1) :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        P.LifetimeBounds → N ≤ P.frequency 0 →
        let B := fun t => fderiv ℝ (p.older.velocity t) (0 : Vec3)
        let Bt := fun t => derivWithin B (Icc 0 (P.slab n p.olderActivation)) t
        ∀ t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation),
          HasDerivWithinAt B (Bt t) (Icc p.nextActivation (P.slab (n + 2) p.nextActivation)) t ∧
            ‖B t‖ ≤ P.frequency n ^ 9 ∧ ‖Bt t‖ ≤ P.frequency n ^ 18 := by
  obtain ⟨N, hN, hOld⟩ := older_central_gradient_raw_bounds_of_hB1 hB_1
  refine ⟨N, hN, ?_⟩
  intro P n p h hBase
  have hmono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (hN.trans hBase) P.frequency_step
  have hParent := p.next_slab_lt h
  have hfit := hParent.le.trans p.slab_le_parent
  have hOlderPos := (p.next_slab_pos h).trans_le hfit
  have hold : 0 < P.slab n p.olderActivation := hOlderPos.trans_le le_rfl
  have hsRfull : ContDiffOn ℝ ∞ (Function.uncurry p.older.residual)
      (Icc 0 (P.slab n p.olderActivation) ×ˢ (univ : Set Vec3)) :=
    contDiffOn_closedSlab_momentumResidual hold p.older.smooth_velocity p.older.smooth_pressure
  have hRs (t : ℝ) (ht : t ∈ Icc 0 (P.slab n p.olderActivation)) : ContDiff ℝ ∞ (p.older.residual t) :=
    contDiffOn_univ.mp (hsRfull.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun a _ => ⟨ht, mem_univ a⟩))
  exact hOld hOlderPos p.next_activation_nonnegative hfit
    (hBase.trans (hmono (Nat.zero_le n))) (hN.trans (hBase.trans (hmono (Nat.zero_le (n + 1)))))
    p.older.torusVelocity p.older.residual hRs p.older.smooth_velocity
    (fun t ht => ⟨p.older.velocity_bound t ht, p.older.velocity_band t ht⟩)
    p.older.divergence_free (fun t ht => (p.older.projected_eq t ht).symm)
    p.older.residual_bound

set_option maxHeartbeats 1600000 in
/-- **The switch bound of the later wave** (sections/08b_induction.tex:368-374, (6.8) and the rate
`r_j ≲ λ_j^{1/8} L_{j+1}`): copy of `exists_inductiveEulerTip_scheduled_switch_bound` with (1.15)
from `h1_3`. -/
theorem exists_inductiveEulerTip_scheduled_switch_bound_of_lemma13 (h1_3 : Statement.lemma_1_3)
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
    laterWindow_gains' P.exponentParameter P.order P.threshold P.frequency
      P.exponentParameter_ge hBaseOne P.frequency_step P.order_maximum
      (Lib.S678a.lemma13_schedule h1_3 P).2 n
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
  exact hSwitch w.physical.rate_pos hNext _
    (s.crossing.normalizedAmplitude_early_log_bound w.physical hCurrent hL hr) hRateBudget

end

end TorusEuler.Paper.Lib.S678a
