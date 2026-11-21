import Breakdown.CellReduction.AdjointAssembly
import Breakdown.CellReduction.AdjointDualBounded
import Breakdown.CellReduction.AdjointFreeShift
import Breakdown.CellReduction.AdjointPinCharge
import Breakdown.CellReduction.AdjointPotentialBound
import Breakdown.CellReduction.AdjointQuadTerm
import Breakdown.CellReduction.AdjointQuadraticBridge
import Breakdown.CellReduction.AdjointRemainderAzimuthal
import Breakdown.CellReduction.AdjointRemainderPlain
import Breakdown.CellReduction.AdjointRepresentation
import Breakdown.CellReduction.AdjointTestDensity
import Breakdown.CellReduction.ConvectionIdentityClosed
import Breakdown.CellReduction.CubicWeightProduct
import Breakdown.CellReduction.CellLayerBreakdownCompose
import Breakdown.CellReduction.InstAdjointField
import Breakdown.CellReduction.InstAdjointStructure
import Breakdown.CellReduction.InstAssembly
import Breakdown.CellReduction.InstFieldDecayOrder
import Breakdown.CellReduction.InstFieldPotential
import Breakdown.CellReduction.InstMovedDecay
import Breakdown.CellReduction.InstMovedSmooth
import Breakdown.CellReduction.InstOffsetClause
import Breakdown.CellReduction.InstOffsetIdentity
import Breakdown.CellReduction.InstPinContinuous
import Breakdown.CellReduction.InstPressureRegular
import Breakdown.CellReduction.InstProfilePieces
import Breakdown.CellReduction.InstStepPhase
import Breakdown.CellReduction.InstWeakDivergence
import Breakdown.CellReduction.MatrixFacts
import Breakdown.CellReduction.PeriodGlue
import Breakdown.CellReduction.PerturbationSlice
import Breakdown.CellReduction.PotentialPartsClosed
import Breakdown.CellReduction.ReductionClosed
import Breakdown.CellReduction.SmoothShiftPieces

open Breakdown.CertCell

namespace Breakdown

namespace CellLayerSystem

theorem spaceBreakdown_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : BreakdownOnSpace :=
  breakdownOnSpace_of_cell_system_condition_of_parts
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
    D X R T Y N B h

end CellLayerSystem

end Breakdown
