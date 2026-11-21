import TorusEuler.HierarchySelectedLinearEstimates
import TorusEuler.InductiveStepNumericalBudgets
import TorusEuler.HierarchyCenterWeight
import TorusEuler.HierarchyInductiveTransverseBudget

/-! Common inputs to the exact hierarchy for the first and later waves. -/

open Set
open TorusEuler.HierarchyTwistedProfile
open TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

namespace TorusEuler

noncomputable section

variable {P : InductiveEulerParameters} {i : ℕ} {oldActivation activation : ℝ}
  {parent : InductiveEulerStage P i oldActivation} {k : Vec3} {hT : 0 < P.slab (i + 1) activation}

local notation "slabEnd" => P.slab (i + 1) activation
local notation "freq" => P.frequency (i + 1)
local notation "parentScale" => P.frequency i ^ (9 : ℕ)
local notation "activeSlab" => Icc activation slabEnd
local notation "radius" a => (parentScale ^ a)⁻¹
local notation "width" => freq ^ (-1 / 2 : ℝ)
local notation "weight" center => (fun t : ℝ => freq ^ (3 / 4 : ℝ) * ‖center t‖)

/-- The normalized leading term, its exact activation relay, and its
measured seminorms on the active part of the physical parent slab. -/
structure SelectedPhysicalStageSeed (d : parent.OnSlab hT k)
    (b : PhysicalApproximationData d.geometry parent.pressure (P.stepDepth i))
    (a : ℕ) (seedCost : ℕ → ℝ) where
  center : ℝ → Vec3
  covector : ℝ → Vec3
  activation_nonneg : 0 ≤ activation
  activation_lt : activation < slabEnd
  covector_norm : ‖covector activation‖ = freq
  carrier_eq : k = (fderiv ℝ (parent.flow 0 activation) (0 : Vec3)).adjoint (covector activation)
  carrier_le : ‖k‖ ≤ parentScale * freq
  center_wave : LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (parent.velocity t) 0)
    covector center activation slabEnd parentScale
  weight_continuous : ContinuousOn (weight center) activeSlab
  weight_pos : ∀ t ∈ activeSlab, 0 < (weight center) t
  weight_le_one : ∀ t ∈ activeSlab, (weight center) t ≤ 1
  leading_inactive : b.leading.Inactive activation (tsupport (periodizeCentered (radialEnvelope (radius a))))
  relay : LeadingRelayData b
  seed_le : ∀ n,
    amplitudeSeminorm False (radius a) width n hT activation_nonneg activation_lt.le
      (weight center) weight_continuous weight_pos b.leading.output.V +
      freq * amplitudeSeminorm False (radius a) width n hT activation_nonneg activation_lt.le
        (weight center) weight_continuous weight_pos b.leading.output.p ≤
    seedCost n * parentScale ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1

namespace SelectedPhysicalStageSeed

variable {d : parent.OnSlab hT k}
  {b : PhysicalApproximationData d.geometry parent.pressure (P.stepDepth i)}
  {a : ℕ} {seedCost : ℕ → ℝ}

abbrev gamma (s : SelectedPhysicalStageSeed d b a seedCost) : ℝ → ℝ := weight s.center

/-- The recurrence and every physical readout use the same measured
profiles and their same positive time weight. -/
abbrev measured (s : SelectedPhysicalStageSeed d b a seedCost) (hf : 0 ≤ freq) :=
  actualMeasuredLevels b.operators b.profiles (P.stepDepth i) b.leading.completionSwitch
    b.parentResidual freq hf (radius a) width hT s.activation_nonneg s.activation_lt.le
    s.gamma s.weight_continuous s.weight_pos

theorem label_covector_norm (s : SelectedPhysicalStageSeed d b a seedCost) :
    ‖labelWaveVector parent.flow 0 0 k activation‖ = freq := by
  have ht : activation ∈ Icc 0 slabEnd := ⟨s.activation_nonneg, s.activation_lt.le⟩
  have eq := d.centerCovector_eq_labelWaveVector ht s.carrier_eq s.center_wave.covector
    ⟨le_rfl, ht.2⟩
  rw [← eq, s.covector_norm]

end SelectedPhysicalStageSeed

end

end TorusEuler
