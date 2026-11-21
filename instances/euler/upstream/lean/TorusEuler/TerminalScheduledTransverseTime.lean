import TorusEuler.TerminalScheduledParentCoefficients
import TorusEuler.TerminalTransverseCoefficientBounds
import TorusEuler.TerminalInductiveTransverseTime

/-! The transverse time-norm row on the exact scheduled later hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile InductiveEulerStage.OnSlab

noncomputable section

set_option maxHeartbeats 1500000 in
/-- The raw parent coefficient bounds of the selected stage supply the
exact projected and normalized pressure coefficients. -/
theorem exists_scheduledTransverseTimeCoefficientBounds (q E : ℕ) (C : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (j : ℕ),
        16 ≤ c.radiusExponent → c.ScheduledParentCoefficientTimeBounds j q E C →
        let d := (c.selectedStep j).selected
        let osc := d.parent.geometry.oscillation
        let D := P.frequency (j + 1) ^ (9 : ℕ)
        let freq := P.frequency (j + 2)
        let hfreq : 0 < freq := zero_lt_one.trans_le d.child_frequency_ge_one
        let coeff := osc.timeCoefficients freq hfreq.ne'
        TerminalMixedJetBound 0 (c.construction.slab (j + 2)) (q + 1) 16 D (D ^ (4 * E)) K
          (fun t x => affineWaveAmplitudeOperator (osc.strain t x) (osc.covector t x)) ∧
        TerminalMixedJetBound 0 (c.construction.slab (j + 2)) (q + 1) 16 D (D ^ (4 * E)) K
          (fun t x => hierarchyRelayPressureAmplitudeCoefficient (osc.strain t x)
            (freq⁻¹ • osc.covector t x)) ∧
        ∀ m : ℕ,
          let NM := unweightedSeminorm (k := d.carrier) (E := Vec3 →L[ℝ] Vec3)
            False d.radius d.width m d.time_pos
          let NP := unweightedSeminorm (k := d.carrier) (E := Vec3 →L[ℝ] ℝ)
            False d.radius d.width m d.time_pos
          let B := K m * D ^ (4 * E)
          timeJetSeminorm d.time_pos (q + 1) NM coeff.velocity ≤ B ∧
          timeJetSeminorm d.time_pos (q + 1) NM coeff.source ≤ B ∧
          timeJetSeminorm d.time_pos (q + 1) NP coeff.pressureVelocity ≤ B ∧
          timeJetSeminorm d.time_pos (q + 1) NP coeff.pressureSource ≤ B := by
  obtain ⟨K, hK, hDerive⟩ := exists_transverseTimeCoefficientBounds (q + 1) C C C hC hC hC
  refine ⟨K, hK, ?_⟩
  intro P c j hRadius hRaw d osc D freq hf coeff
  let T := c.construction.slab (j + 2)
  have hM := hRaw.gradient.congr
    (g := osc.strain) (fun _ ht x => (d.parent.geometry.transverse_values ht x).2.1.symm)
  have hKeq (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      c.scheduledParentCovector j t x = freq⁻¹ • osc.covector t x :=
    congrArg (fun y : Vec3 => freq⁻¹ • y) (d.parent.geometry.transverse_values ht x).2.2.symm
  have hKappa := hRaw.covector.congr hKeq
  have hQ := hRaw.reciprocal.congr (fun t ht x =>
    congrArg (fun y : Vec3 => (‖y‖ ^ 2)⁻¹) (hKeq t ht x))
  have hD : 1 ≤ D := one_le_two.trans d.parent_scale_ge_two
  have h := hDerive (h := d.width) osc d.time_pos d.time_le_one hf.ne' hD
    d.regularity.envelope_pos.le (d.radius_mul_parent_power hRadius) hM hKappa hQ
  simp only [show E + 2 * E + E = 4 * E by omega] at h
  exact h

set_option maxHeartbeats 1800000 in
/-- At the actual selected later step, the four coefficient caps and the
original normalized spatial inverse supply the mixed transverse row. -/
theorem exists_scheduledTransverseTimeBudget :
    ∃ (A : ℕ) (Krec : ℕ → ℝ), 30 ≤ A ∧ (∀ m, 0 ≤ Krec m) ∧
      ∀ (q E : ℕ) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) →
      ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (j : ℕ),
        A ≤ c.radiusExponent → c.ScheduledParentCoefficientTimeBounds j q E C →
        let d := (c.selectedStep j).selected
        let cfg := d.approximation
        let D := P.frequency (j + 1) ^ (9 : ℕ)
        let freq := P.frequency (j + 2)
        let hfreq : 0 < freq := zero_lt_one.trans_le d.child_frequency_ge_one
        let h₀ := (c.construction.tip j).next_activation_nonnegative
        let hT := d.regularity.start_lt_end.le
        let U n := timeJetSeminorm d.time_pos (q + 1)
          (unweightedSeminorm (k := d.carrier) (E := Vec3) False d.radius d.width n d.time_pos)
        let Uforce n := timeJetSeminorm d.time_pos q
          (unweightedSeminorm (k := d.carrier) (E := Vec3) False d.radius d.width n d.time_pos)
        let W n := timeJetSeminorm d.time_pos (q + 1)
          (amplitudeSeminorm (k := d.carrier) (E := Vec3) False d.radius d.width n d.time_pos
            h₀ hT d.centerWeight d.centerWeight_continuous d.centerWeight_pos)
        let Q n := timeJetSeminorm d.time_pos (q + 1)
          (amplitudeSeminorm (k := d.carrier) (E := ℝ) False d.radius d.width n d.time_pos
            h₀ hT d.centerWeight d.centerWeight_continuous d.centerWeight_pos)
        let levels := HierarchyMeasuredLevels.ofProfilesWithMeanForce cfg.operators cfg.profiles d.depth
          cfg.leading.completionSwitch cfg.parentResidual freq hfreq.le U Uforce W Q
        ∀ m i : ℕ, i ∈ Finset.Icc 2 d.depth →
          levels.osc m i ≤
            (transverseTimeCost 1 m (q + 1) (Krec m) (K m) * D ^ (20 + (4 * E) * (q + 2))) *
              levels.oscSource m i := by
  obtain ⟨A, Krec, hA, hKrec, hBudget⟩ := exists_normalizedPhysicalTransverseTimeBudget_of_stage
  refine ⟨A, Krec, hA, hKrec, ?_⟩
  intro q E C hC
  obtain ⟨K, hK, hCoeff⟩ := exists_scheduledTransverseTimeCoefficientBounds q E C hC
  refine ⟨K, hK, ?_⟩
  intro P c j hRad hRaw d cfg D freq hf h₀ hT U Uforce W Q levels
  have hRad₁ : 16 ≤ c.radiusExponent := ((by decide : 16 ≤ 30).trans hA).trans hRad
  have hCap := (hCoeff c j hRad₁ hRaw).2.2
  exact hBudget (h := d.width) d.parent d.parent_frequency_ge_two h₀ d.regularity.start_lt_end
    d.regularity.envelope_pos (d.radius_le_inverse_power hRad) hf
    d.launch_covector_norm d.carrier_eq_launch_pullback d.centerWaveOn cfg
    (by have hDepth := d.depth_ge_two; omega) d.leading_inactive
    d.centerWeight_continuous d.centerWeight_pos (q + 1) (4 * E) K hK hCap

end

end TorusEuler.ScheduledEulerConstruction
