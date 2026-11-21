import Breakdown.CellReduction.MatrixFacts
import Breakdown.CellReduction.SliceSupNorm
import Breakdown.CellReduction.SliceSupNormSmooth
import Breakdown.CellReduction.SliceSupNormMollify
import Breakdown.CellReduction.PerturbationSlice
import Breakdown.CellReduction.EnergyBounds
import Breakdown.CellReduction.CubicWeightProduct
import Breakdown.CellReduction.PeriodGlue
import Breakdown.CellReduction.FrozenIntegrand
import Breakdown.CellReduction.GapSupTerm
import Breakdown.CellReduction.GapGradTerm
import Breakdown.CellReduction.ShiftSupTerm
import Breakdown.CellReduction.ShiftGradTerm
import Breakdown.CellReduction.StrainTerm
import Breakdown.CellReduction.GapTransferBridge
import Breakdown.CellReduction.FormShiftBridge
import Breakdown.CellReduction.FrozenFormBridge

noncomputable section

namespace Breakdown

namespace CertReduction

theorem matrixFactsHolds_proof : MatrixFactsHolds := matrixFacts

theorem sliceSupNormHolds_proof : SliceSupNormHolds :=
  sliceSupNorm_of smoothSupNormBound weakFieldMollify

theorem perturbationSliceHolds_proof : PerturbationSliceHolds := perturbationSliceHolds

theorem energyBoundsHolds_proof : EnergyBoundsHolds :=
  energyBounds_of sliceSupNormHolds_proof perturbationSliceHolds_proof

theorem cubicWeightProductHolds_proof : CubicWeightProductHolds := cubicWeightProductHolds

theorem periodGlueHolds_proof : PeriodGlueHolds := periodGlue

theorem frozenIntegrandHolds_proof : FrozenIntegrandHolds := frozenIntegrand

theorem gapSupTermHolds_proof : GapSupTermHolds :=
  gapSupTerm_of matrixFactsHolds_proof energyBoundsHolds_proof

theorem gapGradTermHolds_proof : GapGradTermHolds :=
  gapGradTerm_of perturbationSliceHolds_proof energyBoundsHolds_proof cubicWeightProductHolds_proof
    periodGlueHolds_proof

theorem shiftSupTermHolds_proof : ShiftSupTermHolds := shiftSupTerm_of matrixFactsHolds_proof

theorem shiftGradTermHolds_proof : ShiftGradTermHolds :=
  shiftGradTerm_of energyBoundsHolds_proof cubicWeightProductHolds_proof

theorem gapTransferBridgeHolds_proof : GapTransferBridgeHolds :=
  gapTransferBridge_of gapSupTermHolds_proof gapGradTermHolds_proof periodGlueHolds_proof

theorem formShiftBridgeHolds_proof : FormShiftBridgeHolds :=
  formShiftBridge_of frozenIntegrandHolds_proof shiftSupTermHolds_proof shiftGradTermHolds_proof
    periodGlueHolds_proof

theorem strainTermHolds_of_convection (hconv : ConvectionIdentityHolds) : StrainTermHolds :=
  strainTerm_of hconv

theorem frozenFormBridgeHolds_of_convection (hconv : ConvectionIdentityHolds) :
    FrozenFormBridgeHolds :=
  frozenFormBridge_of frozenIntegrandHolds_proof (strainTermHolds_of_convection hconv)
    shiftGradTermHolds_proof periodGlueHolds_proof

theorem reductionStatements_of (hconv : ConvectionIdentityHolds)
    (hsmooth : SmoothShiftPiecesHolds) (hquad : AdjointQuadTermHolds)
    (hbridge : AdjointQuadraticBridgeHolds) :
    MatrixFactsHolds ∧ SliceSupNormHolds ∧ PerturbationSliceHolds ∧ EnergyBoundsHolds ∧
      CubicWeightProductHolds ∧ PeriodGlueHolds ∧ ConvectionIdentityHolds ∧ FrozenIntegrandHolds ∧
      SmoothShiftPiecesHolds ∧ GapSupTermHolds ∧ GapGradTermHolds ∧ ShiftSupTermHolds ∧
      ShiftGradTermHolds ∧ StrainTermHolds ∧ AdjointQuadTermHolds ∧ GapTransferBridgeHolds ∧
      FormShiftBridgeHolds ∧ FrozenFormBridgeHolds ∧ AdjointQuadraticBridgeHolds :=
  ⟨matrixFactsHolds_proof, sliceSupNormHolds_proof, perturbationSliceHolds_proof,
    energyBoundsHolds_proof, cubicWeightProductHolds_proof, periodGlueHolds_proof, hconv,
    frozenIntegrandHolds_proof, hsmooth, gapSupTermHolds_proof, gapGradTermHolds_proof,
    shiftSupTermHolds_proof, shiftGradTermHolds_proof, strainTermHolds_of_convection hconv, hquad,
    gapTransferBridgeHolds_proof, formShiftBridgeHolds_proof,
    frozenFormBridgeHolds_of_convection hconv, hbridge⟩

end CertReduction

end Breakdown
