import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.LaterWaveHierarchyInput

/-! The switched later wave as input to the canonical physical hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalLeadingInput

noncomputable section

open LocalizedAmplitude

variable {T t₀ ell D C r h : ℝ} {hT : 0 < T}
  {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {center : ℝ → Vec3}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

private theorem label_even_of_profile_even
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : HierarchyTwistedProfile T k E} {f : ℝ → Vec3 → E}
    (hval : ∀ z ∈ hierarchyProfileSlab T, F.val.val.val z = f z.1 z.2.1)
    (hF : HierarchyProfileReflectionParity 1 F.val.val.val)
    {t : ℝ} (ht : t ∈ I) : Function.Even (f t) := by
  intro a
  have he := hF (t, a, 0)
  simp only [hierarchyProfileReflection_apply, neg_zero, one_smul] at he
  rw [hval _ ⟨ht, mem_univ _⟩, hval _ ⟨ht, mem_univ _⟩] at he
  exact he

/-- The actual selected seed produces the two leading profiles and both
activation sources using the same parent coframe as the hierarchy. -/
def ofLaterWave (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) : PhysicalLeadingInput g :=
  have hpar := g.reflection hX hU hper hodd
  have hsub : Icc t₀ T ⊆ I := Icc_subset_Icc_left reg.nonneg_start
  { output := w.twistedLeadingOutput reg g.inverse g.strain g.covector g.covector_value
    leadingSwitch := w.twistedLeadingSwitch reg k
    completionSwitch := w.twistedCompletionSwitch reg g.inverse g.covector
      g.oscillation.covector_independent g.oscillation.covector_ne_zero
    momentum := w.twistedLeadingOutput_momentum reg g.inverse g.strain g.covector
      g.strain_value g.covector_value
    velocity_odd := w.twistedLeading_reflectionOdd reg k hAmp
    pressure_even := w.twistedPressure_reflectionEven reg k hAmp
      (fun _ ht => label_even_of_profile_even (f := M) g.strain_value hpar.2.1 (hsub ht))
      (fun _ ht => label_even_of_profile_even (f := K) g.covector_value hpar.2.2.1 (hsub ht))
    completionSwitch_odd := w.twistedCompletionSwitch_reflectionOdd reg g.inverse g.covector
      g.oscillation.covector_independent g.oscillation.covector_ne_zero hpar.1 hpar.2.2.1 hAmp }

/-- The physical leading input inherits the inactive region of the
periodized radial envelope, including the completed switch. -/
theorem ofLaterWave_inactive (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    {S : Set Vec3} (hS : IsClosed S) (henv : Function.support (periodizeCentered (radialEnvelope ell)) ⊆ S) :
    (ofLaterWave g w reg hX hU hper hodd hAmp).Inactive t₀ S := by
  obtain ⟨hV, hp, hF, hCF⟩ := w.twistedLeading_inactive reg g.inverse g.covector
    g.oscillation.covector_independent g.oscillation.covector_ne_zero hS henv
  exact ⟨hV, hp, hF, hCF⟩

end
end TorusEuler.HierarchyTwistedProfile.PhysicalLeadingInput
