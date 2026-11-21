import TorusEuler.PhysicalWaveStageClosure
import TorusEuler.InductiveStepNumericalBudgets

/-! Estimates and cutoff for one actual approximation on the common schedule. -/

open Set
open TorusEuler.HierarchyTwistedProfile

namespace TorusEuler

noncomputable section

variable {P : InductiveEulerParameters} {i : ℕ} {activationOld activation : ℝ}
  {k : Vec3} {hT : 0 < P.slab (i + 1) activation}

local notation "D" => P.frequency i ^ (9 : ℕ)
local notation "childFrequency" => P.frequency (i + 1)
local notation "r" a => ((D ^ a)⁻¹)
local notation "width" => childFrequency ^ (-1 / 2 : ℝ)

/-- The graph, pressure, and deformation estimates refer to the same
finite expansion and the same Fourier cutoff. -/
structure ScheduledPhysicalStage (parent : InductiveEulerStage P i activationOld)
    {geom : ParentGeometry hT parent.velocity parent.flow k}
    (b : PhysicalApproximationData geom parent.pressure (P.stepDepth i))
    (properties : PhysicalApproximationProperties b) (a : ℕ) where
  symbol : Vec3 → ℝ
  cutoff : TruncatedChildStage (P.slab (i + 1) activation)
    ((P.frequency i ^ frequencyExponent P.exponentParameter (P.order (i + 1))) ^ 5)
    symbol b.velocity b.residual
  C : ℝ
  K : ℝ
  Cmean : ℝ
  B : ℝ
  Γ : ℝ
  jetPower : ℕ
  cutoffBounds : cutoff.CutoffBounds (b.potential properties) (P.stepDepth i) C K
  bounds : PhysicalWaveApproximationBounds parent activation b.velocity b.residual
    b.oscillation b.meanCorrection (b.potential properties) (Γ * D ^ P.exponentParameter) Cmean
  cutoff_nonneg : 0 ≤ C
  tail_nonneg : 0 ≤ K
  tail_le_parent : K ≤ P.frequency i
  mean_le_parent : Cmean ≤ P.frequency i
  step_le_child : Γ * D ^ P.exponentParameter ≤ childFrequency ^ (1 / 32 : ℝ)
  cutoff_le_next : max 2 ((2 * C) ^ (2 : ℕ)) ≤ P.frequency (i + 2)
  parent_le_scale : P.frequency i ≤ D
  radius_pos : 0 < r a
  jet_nonneg : 0 ≤ B
  radius_inv : (r a)⁻¹ ≤ D ^ a
  carrier_le : ‖k‖ ≤ D * childFrequency
  flow_exponent : max a 1 + (max a 1 + jetPower) + 1 ≤ P.exponentParameter
  flow_constant : 1 + 40 * B ≤ Γ
  jets : cutoff.PulledBackProfileJetBounds parent.flow b.profileVelocity childFrequency (r a) width B D jetPower
  center : ∀ t ∈ Icc activation (P.slab (i + 1) activation),
    ‖fderiv ℝ (b.oscillationRemainder t) 0‖ + ‖fderiv ℝ (b.meanCorrection t) 0‖ ≤
      (Γ * D ^ P.exponentParameter) * childFrequency ^ (-5 / 12 : ℝ)

end

end TorusEuler
