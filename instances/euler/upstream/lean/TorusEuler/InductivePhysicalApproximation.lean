import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.InductiveParentGeometry
import TorusEuler.PhysicalWaveEnvelopeSupport

/-! The physical hierarchy over the actual inductive parent on the next slab. -/

open Set
open scoped ContDiff

namespace TorusEuler.InductiveEulerStage.OnSlab

open HierarchyTwistedProfile

noncomputable section

variable {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
  {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}

/-- Use the same pulled-back residual furnished with the parent geometry,
so its quantitative estimates apply to the selected hierarchy. -/
def physicalApproximationData (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) (depth : ℕ) : PhysicalApproximationData d.geometry s.pressure depth where
  time_le_one := hT₁
  leading := L
  parentResidual := d.residualProfile
  parentResidual_average := d.residualProfile_mean
  parentResidual_value z hz := (d.residualProfile_value z hz).trans
    (congrFun (d.momentum_same z.1 hz.1) _).symm
  parentResidual_odd := d.residualProfile_odd

@[simp] theorem physicalApproximationData_leading (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) (depth : ℕ) : (d.physicalApproximationData hT₁ L depth).leading = L :=
  rfl

@[simp] theorem physicalApproximationData_parentResidual (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) (depth : ℕ) :
    (d.physicalApproximationData hT₁ L depth).parentResidual = d.residualProfile :=
  rfl

/-- The physical approximation over the restricted parent has all the
qualitative properties required as input to the actual periodic cutoff. -/
theorem physicalApproximationProperties (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) {depth : ℕ} (hDepth : 2 ≤ depth) :
    PhysicalApproximationProperties (d.physicalApproximationData hT₁ L depth) :=
  (d.physicalApproximationData hT₁ L depth).assemble_of_parent hDepth d.deformationOn.flow
    d.smooth_velocity d.smooth_pressure (fun t _ => s.periodic_velocity t)
    (fun t ht => s.periodic_pressure t (d.subset ht)) (fun t ht => s.odd_velocity t (d.subset ht))
    (fun t ht => s.divergence_free t (d.subset ht))

/-- The actual oscillatory correction vanishes through positive activation. -/
theorem physicalApproximation_oscillation_vanishes (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) {depth : ℕ} (hDepth : 1 ≤ depth)
    {τ ℓ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    (hL : L.Inactive τ (tsupport (periodizeCentered (radialEnvelope ℓ)))) :
    ∀ t ∈ Icc 0 τ, (d.physicalApproximationData hT₁ L depth).oscillation t = 0 := by
  intro t ht
  funext x
  exact (d.physicalApproximationData hT₁ L depth).oscillation_eq_zero_through_activation
    hDepth (isClosed_tsupport (periodizeCentered (radialEnvelope ℓ))) hτ hL ⟨ht.1, ht.2.trans hτT⟩ x (Or.inl ht.2)

/-- Nonzero oscillation lies within inverse parent-frequency distance of
some lattice point in the actual Eulerian coordinates. -/
theorem physicalApproximation_oscillation_support (d : s.OnSlab hT k) (hT₁ : T ≤ 1)
    (L : PhysicalLeadingInput d.geometry) {depth : ℕ} (hDepth : 1 ≤ depth)
    {τ ℓ D : ℝ} (hℓ : 0 < ℓ) (hμ : 2 ≤ P.frequency n) (hD : P.frequency n ≤ D)
    (hRadius : ℓ ≤ (D ^ (3 : ℕ))⁻¹)
    (hL : L.Inactive τ (tsupport (periodizeCentered (radialEnvelope ℓ)))) :
    ∀ t ∈ Icc 0 T, ∀ x, (d.physicalApproximationData hT₁ L depth).oscillation t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency n)⁻¹ := by
  let b := d.physicalApproximationData hT₁ L depth
  intro t ht x hV
  have hLabel : s.flow t 0 x ∈ tsupport (periodizeCentered (radialEnvelope ℓ)) := by
    by_contra h
    exact hV (b.inactive hDepth (isClosed_tsupport (periodizeCentered (radialEnvelope ℓ))) hL ht x (Or.inr h)).1
  exact d.deformationOn.flow.exists_lattice_dist_le_inv_of_inverse_mem_periodicEnvelope_tsupport
    hT hℓ (d.smooth_velocity.of_le (by simp)) (fun t _ => s.periodic_velocity t)
    (fun t ht => s.odd_velocity t (d.subset ht)) ht hμ hD hRadius
    (fun a => ((d.deformationOn.bounds t ht).2.1 a).2.trans hD) hLabel

end

end TorusEuler.InductiveEulerStage.OnSlab
