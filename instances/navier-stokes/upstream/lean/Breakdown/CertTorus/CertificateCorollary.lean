import Breakdown.CellReduction.CellLayerBreakdownClosed
import Breakdown.CertTorus.Main

open Breakdown.CertCell

namespace Breakdown

namespace CellLayerSystem

theorem torusBreakdown_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : BreakdownOnTorus := by
  obtain ⟨b, hb⟩ := isExtendedCertificate_of_parts
      (CellReduction.Instantiation.instantiation_holds_of_open CellReduction.Instantiation.stepPhase_holds CellReduction.Instantiation.movedFieldJointSmooth_holds CellReduction.Instantiation.movedFieldUniformDecay_holds CellReduction.Instantiation.pinValueContinuous_holds CellReduction.Instantiation.pressureFieldRegular_holds)
      (CellReduction.Instantiation.offsetClause_holds_of CellReduction.Instantiation.stepPhase_holds CellReduction.Instantiation.pressureFieldRegular_holds CellReduction.Instantiation.offsetBallIdentity_holds)
      CertReduction.gapTransferBridgeHolds_proof
      CertReduction.formShiftBridgeHolds_proof
      (CertReduction.frozenFormBridgeHolds_of_convection Breakdown.CertReduction.convectionIdentity_holds)
      (CertReduction.adjointQuadraticBridge_of (CertReduction.adjointQuadTerm_of CertReduction.matrixFacts CertReduction.perturbationSliceHolds CertReduction.energyBoundsHolds_proof CertReduction.cubicWeightProductHolds CertReduction.periodGlue) CertReduction.periodGlue)
      (AdjointDefect.adjointDefectBridge_of_pieces (AdjointDefect.representationHolds_of_density AdjointDefect.testFieldDensityHolds_proof) AdjointDefect.potentialBoundHolds_proof (AdjointDefect.dualBoundedBound_of_parts AdjointDefect.remainderPlainHolds_proof AdjointDefect.remainderAzimuthalHolds_proof) AdjointDefect.pinChargeHolds_proof AdjointDefect.freeShiftBoundHolds_proof)
      (CellReduction.Instantiation.adjointStructure_holds_of (CellReduction.Instantiation.adjointField_holds_of CellReduction.Instantiation.fieldDecayOrder_holds CellReduction.Instantiation.fieldPotential_holds CellReduction.Instantiation.classicalDivergenceWeak_holds) (CellReduction.Instantiation.profilePiecesFlow_of CellReduction.Instantiation.stepPhase_holds CellReduction.Instantiation.movedFieldUniformDecay_holds))
      CertReduction.smoothShiftPiecesHolds
      PotentialShape.potentialParts_holds
      h
  exact FarField.breakdownOnTorus_of_weak (extended_certificate_orbit_proved ⟨k, _, hb⟩)

theorem spaceAndTorusBreakdown_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) :
    BreakdownOnSpace ∧ BreakdownOnTorus := by
  exact ⟨spaceBreakdown_of_cell_system_condition D X R T Y N B h, torusBreakdown_of_cell_system_condition D X R T Y N B h⟩

end CellLayerSystem

end Breakdown
