import TorusEuler.TerminalScheduledStages
import TorusEuler.TerminalParentTime
import TorusEuler.TerminalCoefficientTimeBase

/-! The old parent's time and space jets on the actual selected child slab. -/

open Set

namespace TorusEuler.ScheduledEulerConstruction

/-- The exact selected parent gives the mixed-jet data for its child's coefficient
calculus. The velocity is needed through one more time order than the residual. -/
theorem exists_scheduledParentMixedJetBounds (q A : ℕ) :
    ∃ (B : ℕ) (K : ℕ → ℝ), A ≤ B ∧ (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (n : ℕ),
        2 ≤ P.frequency (n + 1) → c.construction.stages.StageTimeBounds q A (n + 1) →
        let T := c.construction.slab (n + 2)
        let μ := P.frequency (n + 1)
        let ν := P.frequency (n + 2)
        TerminalMixedJetBound 0 T (q + 1) 5 μ (μ ^ B) K (c.construction.tip n).parent.velocity ∧
          TerminalMixedJetBound 0 T q 5 μ (ν ^ (-(5 / 2) : ℝ)) K
            (c.construction.tip n).parent.residual := by
  obtain ⟨B, K, hB, hK, hBounds⟩ := InductiveEulerStage.exists_terminalParentTime_bounds q A
  refine ⟨B, K, hB, hK, ?_⟩
  intro P c n hμ hTime
  let parent := (c.construction.tip n).parent
  let S := c.construction.slab (n + 1)
  let T := c.construction.slab (n + 2)
  have hOld : S = P.slab (n + 1) (c.construction.tip n).activation := rfl
  have hLT : T < S := c.construction.slab_succ_lt (n + 1)
  have hT : 0 < T := (c.selectedStep n).selected.time_pos
  have hS : 0 < S := hT.trans hLT
  have hSub : Icc 0 T ⊆ Icc 0 S := Icc_subset_Icc_right hLT.le
  obtain ⟨_, hU, hR⟩ := hBounds parent hS hμ
    (fun i hi t ht x => (hTime i hi t ht x).1)
    (fun i hi t ht x => (hTime i hi t ht x).2)
  constructor
  · intro i hi m t ht x
    have hEq : slabTimeJet 0 T i parent.velocity t = slabTimeJet 0 S i parent.velocity t :=
      funext (slabTimeJet_eq_of_subset (f := parent.velocity) hT hSub hS parent.smooth_velocity i ht)
    rw [hEq, hOld]
    simpa only [pow_add, mul_assoc] using hU i hi m t (hSub ht) x
  · intro i hi m t ht x
    have hEq : slabTimeJet 0 T i parent.residual t = slabTimeJet 0 S i parent.residual t :=
      funext (slabTimeJet_eq_of_subset hT hSub hS (parent.smooth_stage_residual hS) i ht)
    rw [hEq, hOld]
    exact (hR i hi m t (hSub ht) x).trans_eq (mul_right_comm _ _ _)

end TorusEuler.ScheduledEulerConstruction
