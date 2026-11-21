import TorusEuler.HierarchyPhysicalApproximation

/-! Initial-slice vanishing of the selected physical hierarchy. -/

open ContinuousLinearMap Set
open scoped InnerProductSpace

namespace TorusEuler

namespace HierarchySmoothProfile

/-- Completion uses only the label and phase variables, so it preserves an
identically zero time slice, including at a slab endpoint. -/
theorem profileCompletion_eq_zero_on_time_slice {T t : ℝ} (hT : 0 < T)
    (G : HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)) (κ V : HierarchySmoothProfile T Vec3)
    (hκ : ∀ r ∈ Icc 0 T, ∀ a, κ.val (r, a, 0) ≠ 0) (ht : t ∈ Icc 0 T)
    (hV : ∀ a s, V.val (t, a, s) = 0) (a : Vec3) (s : ℝ) :
    (profileCompletion hT G κ hκ V).val (t, a, s) = 0 := by
  let Q := profileWavePotential hT κ hκ V
  have hQ : (fun b : Vec3 => Q.val (t, b, s)) = fun _ => 0 := by
    funext b
    change (profileWavePotential hT κ hκ V).val (t, b, s) = 0
    rw [profileWavePotential_apply hT κ hκ V ht]
    exact wavePotential_zero_of_profile_zero (hV b) s
  change (profileSlowCurl hT G Q).val (t, a, s) = 0
  rw [profileSlowCurl_apply hT G Q ht, hQ]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_comp]
  exact curlOfDerivativeCLM.map_zero

end HierarchySmoothProfile

namespace HierarchyTwistedProfile.PhysicalApproximationData

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

private theorem velocity_profile_initial
    (b : PhysicalApproximationData d p P)
    (hLead : ∀ a s, b.leading.output.V.val.val.val (0, a, s) = 0)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P) :
    profilePhaseAverage hT (b.profiles.V i) = 0 ∧
    ∀ a s, (b.profiles.V i).val.val.val (0, a, s) = 0 := by
  by_cases hOne : i = 1
  · subst i
    have hEq : b.profiles.V 1 = b.leading.output.V :=
      (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
        b.parentResidual_average b.leading.output).1
    rw [hEq]
    exact ⟨b.leading.output.average_V, hLead⟩
  · obtain ⟨hi₁, hiP⟩ := Finset.mem_Icc.mp hi
    have hi' : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, hiP⟩
    let f := -(b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch i -
      b.operators.average (b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch i)) -
      hierarchyAdvectionAtLevel P 1 i (b.operators.meanPhaseProduct b.profiles)
    obtain ⟨hf, hEq, _⟩ := b.solvers.construct_transverse_selected hi' b.leading.completionSwitch
      b.parentResidual b.parentResidual_average b.leading.output
    change b.operators.average f = 0 at hf
    let o := solveTransverse hT d.inverse d.strain d.covector d.oscillation f hf
    change b.profiles.V i = o.output.V at hEq
    rw [hEq]
    exact ⟨o.output.average_V, o.velocity_initial⟩

/-- If the leading wave vanishes on the initial slice, then the actual
Eulerian oscillation does too. Every higher transverse solve starts at zero. -/
theorem oscillation_eq_zero_at_zero (b : PhysicalApproximationData d p P)
    (hLead : ∀ a s, b.leading.output.V.val.val.val (0, a, s) = 0) : b.oscillation 0 = 0 := by
  funext x
  let z := hierarchyGraphPoint (fun r => X r 0) k 0 x
  let E : VP →ₗ[ℝ] Vec3 := (LinearMap.proj z).comp (((hierarchySmoothProfileSubmodule T Vec3).subtype.comp
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype).comp (hierarchyTwistedProfileSubmodule T k Vec3).subtype)
  rw [b.oscillation_eq_graph_sum]
  change E (∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hMean, hV⟩ := velocity_profile_initial b hLead hi
  have hCompletion : b.profiles.C i = b.solvers.complete (b.profiles.V i) :=
    b.solvers.construct_completion hi b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  have hC (a : Vec3) (s : ℝ) : (b.profiles.C i).val.val.val (0, a, s) = 0 := by
    rw [hCompletion]
    change (complete hT d.inverse d.covector d.oscillation.covector_independent
      d.oscillation.covector_ne_zero (b.profiles.V i)).val.val.val (0, a, s) = 0
    rw [complete_val_val_of_phaseMean_zero hT d.inverse d.covector d.oscillation.covector_independent
      d.oscillation.covector_ne_zero (b.profiles.V i) hMean]
    exact HierarchySmoothProfile.profileCompletion_eq_zero_on_time_slice hT d.inverse.val.val
      d.covector.val.val (b.profiles.V i).val.val d.oscillation.covector_ne_zero
      (left_mem_Icc.mpr hT.le) hV a s
  change (b.profiles.V i).val.val.val (0, z.2.1, z.2.2) +
    (b.profiles.C i).val.val.val (0, z.2.1, z.2.2) = 0
  rw [hV, hC, add_zero]

/-- The oscillation vanishes through activation on the closed time slab,
including when activation is exactly at the initial endpoint. -/
theorem oscillation_eq_zero_through_nonnegative_activation (b : PhysicalApproximationData d p P)
    {τ : ℝ} {S : Set Vec3} (hP : 1 ≤ P) (hS : IsClosed S) (hτ : 0 ≤ τ)
    (hL : b.leading.Inactive τ S)
    (hLead : τ = 0 → ∀ a s, b.leading.output.V.val.val.val (0, a, s) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (hx : t ≤ τ ∨ X t 0 x ∉ S) : b.oscillation t x = 0 := by
  obtain hτ | rfl := hτ.lt_or_eq
  · exact b.oscillation_eq_zero_through_activation hP hS hτ hL ht x hx
  · obtain ht₀ | hOutside := hx
    · have he := le_antisymm ht₀ ht.1
      subst t
      exact congrFun (b.oscillation_eq_zero_at_zero (hLead rfl)) x
    · exact (b.inactive hP hS hL ht x (Or.inr hOutside)).1

end HierarchyTwistedProfile.PhysicalApproximationData

end TorusEuler
