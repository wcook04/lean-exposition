import TorusEuler.InductiveParentGeometry
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.HierarchyPhysicalMeanBounds

/-! The concrete unweighted mean solve bound on each endpoint slab of the
induction, uniform in the parent and in the correction level. -/

open Set

namespace TorusEuler.InductiveEulerStage

open HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 2400000 in
/-- The physical mean callback for the actual parent, at label radius
`(λ ^ (9 * s))⁻¹`. The exponent and the constants are selected before
the parent, endpoint, depth and source. -/
theorem exists_onSlab_meanSeminormBound :
    ∃ (p s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {P : InductiveEulerParameters} {j : ℕ} {activation T : ℝ}
        {parent : InductiveEulerStage P j activation} {k : Vec3}
        {hT : 0 < T} (data : parent.OnSlab hT k) (hT₁ : T ≤ 1),
      2 ≤ P.frequency j →
      ∀ s : ℕ, s₀ ≤ s → ∀ (h : ℝ) (n : ℕ)
        (force : HierarchyTwistedProfile T k Vec3)
        (hforce : (HierarchyTwistedProfile.twistedHierarchyOperators hT
          data.geometry.inverse data.geometry.strain data.geometry.covector).average force = force),
        let freq := P.frequency j
        let ℓ := (freq ^ (9 * s))⁻¹
        let solvers := HierarchyTwistedProfile.physicalSolvers hT hT₁
          data.geometry.inverse data.geometry.strain data.geometry.covector
          data.geometry.mean data.geometry.oscillation
        unweightedSeminorm False ℓ h n hT (solvers.solveMean force hforce).val.B ≤
          C n * freq ^ (9 * (p + 2 + 2 * s)) * unweightedSeminorm False ℓ h (n + 1) hT force := by
  obtain ⟨R, hR, hJets⟩ := exists_velocity_jet_bounds
  obtain ⟨p, s₀, C, hC, hMean⟩ := HierarchyTwistedProfile.exists_physicalSolvers_meanSeminormBound R hR
  refine ⟨p, s₀, C, hC, ?_⟩
  intro P j activation T parent k hT data hT₁ hFreq s hs h n force hforce
  let freq := P.frequency j
  let D := freq ^ 9
  let geom := data.geometry
  have hfreq : 1 ≤ freq := (by norm_num : (1 : ℝ) ≤ 2).trans hFreq
  have hfreqD : freq ≤ D := by
    simpa only [pow_one] using (pow_le_pow_right₀ hfreq (by decide : 1 ≤ 9))
  have hD : 2 ≤ D := hFreq.trans hfreqD
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      ‖fderiv ℝ (parent.flow 0 t) a‖ ≤ D :=
    (((data.deformationOn.bounds t ht).2.1 a).2).trans hfreqD
  have hG (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      ‖fderiv ℝ (parent.flow t 0) (parent.flow 0 t a)‖ ≤ D :=
    (((data.deformationOn.bounds t ht).2.2 (parent.flow 0 t a)).2).trans hfreqD
  have hUjets (m r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖iteratedFDeriv ℝ r (parent.velocity t) x‖ ≤ R m * D ^ r :=
    hJets parent hfreq m r hr hrm t (data.subset ht) x
  have hGin : geom.mean.inverse_bound ≤ D := data.inverse_bound.le.trans hfreqD
  have hMin : geom.mean.strain_bound ≤ D := data.strain_bound.le
  have hM (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      geom.mean.strain (t, toUnitTorus a) = fderiv ℝ (parent.velocity t) (parent.flow 0 t a) :=
    (geom.mean.strain_value (t, a, 0) ⟨ht, mem_univ _⟩).symm.trans
      (geom.strain_value (t, a, 0) ⟨ht, mem_univ _⟩)
  have hBound := hMean hT hT₁ hD data.deformationOn.flow data.smooth_velocity
    (fun t _ => parent.periodic_velocity t) hF hG hUjets
    geom.inverse geom.strain geom.covector geom.mean hGin hMin geom.deformation_value hM
    geom.oscillation s hs h n force hforce
  simpa only [D, freq, ← pow_mul] using hBound

end

end TorusEuler.InductiveEulerStage
