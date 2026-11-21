import TorusEuler.AuxiliaryTerminalSmoothness
import TorusEuler.TerminalScheduledNormContinuity

/-! The two quantitative lemmas on the schedule of the frozen auxiliary theorem. -/

open Filter Set
open scoped Topology

namespace TorusEuler

/-- Pointwise stage time estimates are bounds in the actual spatial supremum norm. -/
theorem InductiveEulerStages.stageTimeBounds_supNorm (s : InductiveEulerStages) {q ψ n : ℕ}
    (hBound : s.StageTimeBounds q ψ n) (i : ℕ) (hi : i ≤ q) (t : ℝ) (ht : t ∈ Icc 0 (s.slab n)) :
    spatialSupNorm (slabTimeJet 0 (s.slab n) i (s.velocity n) t) ≤ s.frequency n ^ ψ ∧
      spatialSupNorm (slabTimeJet 0 (s.slab n) i (s.residual n) t) ≤ s.frequency (n + 1) ^ (-(5 / 2) : ℝ) :=
  ⟨ciSup_le fun x => (hBound i hi t ht x).1, ciSup_le fun x => (hBound i hi t ht x).2⟩

/-- Auxiliary Lemma 1.2, on the physical stages of the chosen schedule.
`HasTerminalMixedIncrementBounds` bounds the order-`m` spatial Hölder norm
of each order-`q` Eulerian time derivative by `(s.frequency (n + 1))⁻¹`. -/
theorem auxiliaryLemma12 :
    ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ),
      Monotone threshold ∧ ∀ N ≥ N₁,
      ∃ (P : InductiveEulerParameters) (c : ScheduledEulerConstruction P),
        P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧
        let s := c.construction.stages
        s.HasTerminalMixedIncrementBounds ∧ ∀ q m : ℕ, ∀ᶠ n in atTop,
          let T := s.slab (n + 1)
          ContinuousOnSlabInSpatialNorm T (spatialHolderHalfNorm m) (slabTimeJet 0 T q
            (fun r x => s.velocity (n + 1) r x - s.velocity n r x - s.oscillation (n + 1) r x)) := by
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ := auxiliaryTerminalSmoothness
  refine ⟨b, threshold, N₁, hMono, fun N hN => ?_⟩
  obtain ⟨P, c, hb, hThreshold, hFrequency, _, hMixed, _⟩ := hSchedule N hN
  refine ⟨P, c, hb, hThreshold, hFrequency, hMixed, fun q m => ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  cases n with
  | zero => omega
  | succ n => exact (c.selectedStep_slabTimeJet_normContinuity n q m).2.2

/-- Auxiliary Lemma 1.3, from the same scheduled construction as Lemma 1.2.
`StageTimeBounds` bounds the velocity by `s.frequency n ^ ψ` and the residual
by `s.frequency (n + 1) ^ (-(5 / 2) : ℝ)` through the given time order. -/
theorem auxiliaryLemma13 :
    ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ),
      Monotone threshold ∧ ∀ N ≥ N₁,
      ∃ (P : InductiveEulerParameters) (c : ScheduledEulerConstruction P),
        P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧
        let s := c.construction.stages
        ∀ q, ∃ ψ : ℕ, ∀ᶠ n in atTop,
          s.StageTimeBounds q ψ n ∧ ∀ i ≤ q,
            let T := s.slab n
            ContinuousOnSlabInSpatialNorm T spatialSupNorm (slabTimeJet 0 T i (s.velocity n)) ∧
              ContinuousOnSlabInSpatialNorm T spatialSupNorm (slabTimeJet 0 T i (s.residual n)) := by
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ := auxiliaryTerminalSmoothness
  refine ⟨b, threshold, N₁, hMono, fun N hN => ?_⟩
  obtain ⟨P, c, hb, hThreshold, hFrequency, hTime, _⟩ := hSchedule N hN
  refine ⟨P, c, hb, hThreshold, hFrequency, fun q => ?_⟩
  obtain ⟨ψ, hψ⟩ := hTime q
  refine ⟨ψ, ?_⟩
  filter_upwards [hψ, eventually_ge_atTop (2 : ℕ)] with n hn h₂
  refine ⟨hn, fun i _ => ?_⟩
  have heq : n - 2 + 2 = n := by omega
  obtain ⟨hV, hR, _⟩ := c.selectedStep_slabTimeJet_normContinuity (n - 2) i 0
  rw [heq] at hV hR
  exact ⟨hV, hR⟩

end TorusEuler
