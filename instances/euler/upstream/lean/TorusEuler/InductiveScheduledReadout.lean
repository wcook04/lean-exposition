import TorusEuler.ScheduledPhysicalStage
import TorusEuler.HierarchyPhysicalVelocityBounds

/-! Assembly of the numerical schedule and the Eulerian estimates of the
same finite approximation and cutoff. -/

open Set
open TorusEuler.HierarchyTwistedProfile
open scoped InnerProductSpace

namespace TorusEuler.ScheduledPhysicalStage

noncomputable section

variable {P : InductiveEulerParameters} {i : ℕ} {activationOld activation : ℝ}
  {k : Vec3} {hT : 0 < P.slab (i + 1) activation}

local notation "Tchild" => P.slab (i + 1) activation
local notation "D" => P.frequency i ^ (9 : ℕ)
local notation "freq" => P.frequency (i + 1)
local notation "nextFreq" => P.frequency (i + 2)
local notation "depth" => P.stepDepth i
local notation "q" => P.order (i + 1)

/-- The scheduled stage keeps the supplied cutoff on the actual approximation.
The cutoff tail and the mean and deformation prefactors are the entries
certified by the numerical budget at this order and depth. -/
def of_actual_readout {ι : Type*} {cost : InductiveEulerParameters.StepCosts ι}
    {a jetPower lossPower absolutePower : ℕ} {C B : ℝ} {ψ : Vec3 → ℝ}
    (parent : InductiveEulerStage P i activationOld)
    {geom : ParentGeometry hT parent.velocity parent.flow k}
    (b : PhysicalApproximationData geom parent.pressure depth)
    (properties : PhysicalApproximationProperties b)
    (numerical : P.StepNumericalBudget i a jetPower lossPower absolutePower C cost)
    (s : TruncatedChildStage Tchild
      ((P.frequency i ^ frequencyExponent P.exponentParameter q) ^ 5) ψ b.velocity b.residual)
    (hCutoff : s.CutoffBounds (b.potential properties) depth C (cost.cutoffTail depth))
    (hC : 0 ≤ C) (hK : 0 ≤ cost.cutoffTail depth)
    (hVelocity : ∀ t ∈ Icc 0 Tchild,
      1 + spatialHolderHalfNorm depth (b.velocity t) ≤ 3 * freq ^ (2 * (depth + 1)))
    (hResidual : ∀ t ∈ Icc 0 Tchild, spatialHolderHalfNorm 1 (b.residual t) ≤ nextFreq ^ (-7 / 2 : ℝ))
    (hOscillation : ∀ t ∈ Icc 0 Tchild, ∀ x,
      ‖b.oscillation t x‖ ≤ (cost.step depth * D ^ P.exponentParameter) * freq ^ (-5 / 4 : ℝ))
    (hMean : ∀ m ≤ q, ∀ t ∈ Icc 0 Tchild,
      SpatialHolderHalf m (b.meanCorrection t) ∧
        spatialHolderHalfNorm m (b.meanCorrection t) ≤
          cost.mean q depth * D ^ (P.exponentParameter * (m + 2)) * freq ^ (-5 / 2 : ℝ))
    (hPressure : ∀ t ∈ Icc 0 Tchild, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (b.pressure t)) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (parent.pressure t)) x v⟫_ℝ +
          ((cost.step depth * D ^ P.exponentParameter) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hk : ‖k‖ ≤ D * freq) (hB : 0 ≤ B) (hGamma : 1 + 40 * B ≤ cost.step depth)
    (hJets : s.PulledBackProfileJetBounds parent.flow b.profileVelocity freq
      ((D ^ a)⁻¹) (freq ^ (-1 / 2 : ℝ)) B D jetPower)
    (hCenter : ∀ t ∈ Icc activation Tchild,
      ‖fderiv ℝ (b.oscillationRemainder t) 0‖ + ‖fderiv ℝ (b.meanCorrection t) 0‖ ≤
        (cost.step depth * D ^ P.exponentParameter) * freq ^ (-5 / 12 : ℝ)) :
    ScheduledPhysicalStage parent b properties a := by
  have hNext : nextFreq = (P.frequency i ^ frequencyExponent P.exponentParameter q) ^
      frequencyExponent P.exponentParameter (P.order (i + 2)) := by
    rw [P.frequency_step (i + 1), P.frequency_step i]
  have hOrderDepth : q ≤ depth + 1 :=
    (le_max_right 2 q).trans (numerical.order_le_depth.trans (Nat.le_succ depth))
  refine
    { symbol := ψ
      cutoff := s
      C := C
      K := cost.cutoffTail depth
      Cmean := cost.mean q depth
      B := B
      Γ := cost.step depth
      jetPower := jetPower
      cutoffBounds := hCutoff
      bounds := ?_
      cutoff_nonneg := hC
      tail_nonneg := hK
      tail_le_parent := numerical.cutoff_tail_le
      mean_le_parent := numerical.mean_le q hOrderDepth
      step_le_child := numerical.step_rate
      cutoff_le_next := numerical.cutoff_large
      parent_le_scale := numerical.coframe_dominates
      radius_pos := numerical.radius_pos
      jet_nonneg := hB
      radius_inv := by rw [inv_inv]
      carrier_le := hk
      flow_exponent := numerical.profile_exponent
      flow_constant := hGamma
      jets := hJets
      center := hCenter }
  refine PhysicalWaveApproximationBounds.of_actual_readout (P := P) (n := i)
    (activationOld := activationOld) (activation := activation) (k := k) (hT := hT) (g := geom)
    parent b properties ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simpa only [P.frequency_step i, InductiveEulerParameters.stepDepth] using hVelocity t ht
  · intro t ht
    rw [← hNext]
    exact hResidual t ht
  · intro t ht x
    rw [← P.frequency_step i]
    exact hOscillation t ht x
  · intro m hm t ht
    rw [← P.frequency_step i]
    exact hMean m hm t ht
  · intro t ht x v
    rw [← P.frequency_step i]
    exact hPressure t ht x v

end

end TorusEuler.ScheduledPhysicalStage
