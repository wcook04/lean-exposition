import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.HierarchyPhysicalApproximation

/-! The initial stationary-shear wave in the actual physical hierarchy. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T s freq : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity}
variable (d : ParentGeometry hT U X (firstWaveLaunchCovector freq))

/-- The general flow operators of the stationary shear are exactly the
explicit operators used to prove the first-wave equation. -/
theorem ParentGeometry.firstWave_operators_eq
    (hU : U = fun _ => stationaryShear s) (hX : X = fun r t => stationaryShearFlow s (t - r)) :
    twistedHierarchyOperators hT d.inverse d.strain d.covector = firstWaveHierarchyOperators hT s freq := by
  have hG : d.inverse = firstWaveHierarchyInverseDeformation s := by
    apply HierarchyTwistedProfile.ext
    rintro ⟨t, a, z⟩ hz
    rw [d.inverse_value _ hz, firstWaveHierarchyInverseDeformation_eval s hz,
      firstWaveInverseDeformation_eq, hX]
    simp only [zero_sub, sub_zero]
  have hM : d.strain = firstWaveHierarchyMaterialGradient s := by
    apply HierarchyTwistedProfile.ext
    rintro ⟨t, a, z⟩ hz
    rw [d.strain_value _ hz, firstWaveHierarchyMaterialGradient_eval s hz,
      firstWaveMaterialGradient_eq s t a, hU, hX]
    simp only [sub_zero]
  have hκ : d.covector = firstWaveHierarchyCovector s freq := by
    apply HierarchyTwistedProfile.ext
    rintro ⟨t, a, z⟩ hz
    rw [d.covector_value _ hz, firstWaveHierarchyCovector_eval s freq hz, labelWaveVector,
      firstWaveTransportedCovector_eq_inverseDeformation, firstWaveInverseDeformation_eq, hX]
    simp only [zero_sub, sub_zero, firstWaveLaunchCovector]
  simp only [hG, hM, hκ, firstWaveHierarchyOperators]

variable (hU : U = fun _ => stationaryShear s)
variable (hX : X = fun r t => stationaryShearFlow s (t - r))
variable {r h : ℝ} (c : ℝ) (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2)
variable (hh : 0 < h) (hh₁ : h ≤ 1)

/-- The first wave is present at the initial time, so both switch sources vanish. -/
def ParentGeometry.firstPhysicalLeadingInput : PhysicalLeadingInput d where
  output := {
    V := firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁
    p := firstWaveHierarchyLeadingPressure s c hf hr hcell hh hh₁
    average_V := by
      rw [d.firstWave_operators_eq hU hX]
      exact firstWaveHierarchyLeading_average hT hr hcell hh hh₁
    phaseAdv_V := by
      rw [d.firstWave_operators_eq hU hX]
      exact (firstWaveHierarchyLeadingOutput (s := s) (c := c) hT hf hr hcell hh hh₁).phaseAdv_V }
  leadingSwitch := 0
  completionSwitch := 0
  momentum := by
    dsimp only
    rw [d.firstWave_operators_eq hU hX]
    exact firstWaveHierarchyLeading_momentum hT hf hr hcell hh hh₁
  velocity_odd := firstWaveHierarchyLeadingVelocity_reflection hr hcell hh hh₁
  pressure_even := firstWaveHierarchyLeadingPressure_reflection hf hr hcell hh hh₁
  completionSwitch_odd := fun _ => (smul_zero _).symm

/-- Outside the wrapped radial envelope, the first velocity and phase
pressure are zero at every time and phase of the slab. -/
theorem ParentGeometry.firstPhysicalLeadingInput_inactive {S : Set Vec3}
    (hS : Function.support (periodizeCentered (radialEnvelope r)) ⊆ S) :
    (d.firstPhysicalLeadingInput hU hX c hf hr hcell hh hh₁).Inactive 0 S := by
  have hEnvelope (x : HierarchyProfilePoint) (hx : x ∈ hierarchyInactiveRegion T 0 S) :
      radialEnvelope r (centeredLabel x.2.1) = 0 := by
    apply Function.notMem_support.mp
    intro hm
    exact hx.2.elim (not_lt_of_ge hx.1.1.1) (fun ha => ha (hS hm))
  refine ⟨?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x hx
    change (firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁).val.val.val x = 0
    rw [firstWaveHierarchyLeadingVelocity_eval s c freq hr hcell hh hh₁ hx.1]
    simp only [phaseTwistedPeriodizeCentered, firstWaveLeadingProfile,
      hEnvelope x hx, zero_mul, zero_smul]
  · intro x hx
    change (firstWaveHierarchyLeadingPressure s c hf hr hcell hh hh₁).val.val.val x = 0
    rw [firstWaveHierarchyLeadingPressure_eval s c hf hr hcell hh hh₁ hx.1]
    simp only [phaseTwistedPeriodizeCentered, firstWaveLeadingPressureProfile,
      hEnvelope x hx, zero_mul]

/-- Evaluating the first typed leading profile on its actual physical graph
recovers the explicit first wave used at the central crossing. -/
theorem PhysicalApproximationData.leadingVelocity_eq_first {p : Pressure} {P : ℕ}
    (b : PhysicalApproximationData d p P)
    (hL : b.leading = d.firstPhysicalLeadingInput hU hX c hf hr hcell hh hh₁)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    b.leadingVelocity t x = localizedTransportedProfile (fun u => stationaryShearFlow s (-u))
      (firstWaveLaunchCovector freq) (firstWaveLeadingProfile s c r h) t x := by
  change graphRead (fun u => X u 0) b.leading.output.V t x = _
  rw [hL]
  change (firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁).val.val.val
    (t, X t 0 x, ⟪firstWaveLaunchCovector freq, X t 0 x⟫_ℝ) = _
  rw [show X t 0 = stationaryShearFlow s (-t) by simp only [hX, zero_sub]]
  exact firstWaveHierarchyLeadingVelocity_graph hr hcell hh hh₁ ht x

/-- The constructed first-wave velocity splits into the stationary shear,
the explicit leading wave, and the actual higher oscillatory and mean terms. -/
theorem PhysicalApproximationData.velocity_eq_first_leading {p : Pressure} {P : ℕ}
    (b : PhysicalApproximationData d p P) (hP : 1 ≤ P)
    (hL : b.leading = d.firstPhysicalLeadingInput hU hX c hf hr hcell hh hh₁)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    b.velocity t = stationaryShear s + localizedTransportedProfile (fun u => stationaryShearFlow s (-u))
      (firstWaveLaunchCovector freq) (firstWaveLeadingProfile s c r h) t +
        b.oscillationRemainder t + b.meanCorrection t := by
  funext x
  have hv := congrFun (congrFun (b.velocity_eq_parent_add_leading_add_remainder_add_mean hP) t) x
  change b.velocity t x = U t x + b.leadingVelocity t x + b.oscillationRemainder t x + b.meanCorrection t x at hv
  rw [show U t x = stationaryShear s x from congrArg (fun f : Velocity => f t x) hU,
    PhysicalApproximationData.leadingVelocity_eq_first d hU hX c hf hr hcell hh hh₁ b hL ht x] at hv
  exact hv

end

end TorusEuler.HierarchyTwistedProfile
