import TorusEuler.ActivationPrimaryJetBounds
import TorusEuler.InductiveLaterWaveSelection
import TorusEuler.HierarchyInductiveTransverseBudget

/-! The weighted activation estimate for the selected later inductive input. -/

open Set

namespace TorusEuler.InductiveEulerTip.SelectedLaterInput

open LocalizedAmplitude HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 1100000 in
/-- The selected later wave supplies the scheduled residual's primary
two-jet bound with a uniform radius threshold and coefficient. -/
theorem exists_activationPrimary_phaseJetBound :
    ∃ (A : ℕ) (C : ℝ), 30 ≤ A ∧ 0 ≤ C ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {p : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : p.SelectedLaterInput Cenv a), A ≤ a →
      ∀ t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation),
        let D := P.frequency (n + 1) ^ 9
        let freq := P.frequency (n + 2)
        let γ := freq ^ (3 / 4 : ℝ) * ‖d.selection.crossing.amplitude t‖
        PhaseJetBound 2 (γ * (C * D ^ (a + 27) * freq ^ (-5 / 4 : ℝ)))
          (scaledPhaseProfile d.radius d.width
            (PhysicalApproximationData.activationPrimary (h := d.width) d.seed d.parent.geometry.inverse t)) := by
  obtain ⟨W, hW, hJet⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨A, C, hA, hC, hPrimary⟩ :=
    PhysicalApproximationData.exists_parent_activationPrimary_phaseJetBound W hW
  refine ⟨A, C, hA, hC, ?_⟩
  intro P n p Cenv a d ha t ht D freq γ
  let T := P.slab (n + 2) p.nextActivation
  have hParentTwo : 2 ≤ P.frequency (n + 1) :=
    (by norm_num : (2 : ℝ) ≤ 4).trans d.parent_frequency_ge_four
  have hParentOne : 1 ≤ P.frequency (n + 1) := one_le_two.trans hParentTwo
  have hFreq : 1 ≤ freq := by
    change 1 ≤ P.frequency (n + 1 + 1)
    rw [P.frequency_step (n + 1)]
    exact one_le_pow₀ hParentOne
  have hFreqPos : 0 < freq := zero_lt_one.trans_le hFreq
  have hD : 2 ≤ D := hParentTwo.trans (by
    dsimp only [D]
    simpa only [pow_one] using pow_le_pow_right₀ hParentOne (show 1 ≤ (9 : ℕ) by decide))
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hD₀ : 0 < D := zero_lt_one.trans_le hD₁
  have hRadius : d.radius ≤ (D ^ A)⁻¹ :=
    inv_anti₀ (pow_pos hD₀ _) (pow_le_pow_right₀ hD₁ ha)
  have hRadiusInv : d.radius⁻¹ ≤ D ^ a := by
    change ((D ^ a)⁻¹)⁻¹ ≤ D ^ a
    rw [inv_inv]
  have hStart : p.nextActivation ∈ Icc 0 T :=
    ⟨d.regularity.nonneg_start, d.regularity.start_lt_end.le⟩
  have hStart' : p.nextActivation ∈ Icc p.nextActivation T :=
    ⟨le_rfl, d.regularity.start_lt_end.le⟩
  have hLaunch : ‖labelWaveVector p.parent.flow 0 0 d.carrier p.nextActivation‖ = freq := by
    rw [d.carrier_transport hStart']
    exact (d.selection.crossing.launch_geometry hFreqPos).2.1
  have hc := d.parent.centerWaveOn_labelWaveVector hStart (show d.carrier = _ from rfl)
    d.selection.center
  exact hPrimary (g := d.parent.geometry) d.time_le_one hD hRadius hRadiusInv hFreq hLaunch
    d.parent.deformationOn.flow d.parent.smooth_velocity (fun u _ => p.parent.periodic_velocity u)
    (fun _ hu x => (d.parent.raw_coframe_norm_le_frequency_nine hParentTwo hu x).1)
    (fun _ hu x => (d.parent.raw_coframe_norm_le_frequency_nine hParentTwo hu x).2)
    (fun i j hj hji u hu x => hJet p.parent hParentOne i j hj hji u (d.parent.subset hu) x)
    hc d.seed d.regularity t ht

end
end TorusEuler.InductiveEulerTip.SelectedLaterInput
