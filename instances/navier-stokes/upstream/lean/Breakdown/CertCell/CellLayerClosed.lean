import Breakdown.CertCell.CellLayerResidualClosed
import Breakdown.CertCell.RowsMatchBridge
import Breakdown.CertCell.RowsMatchTrace
import Breakdown.CertCell.PressureStripFlipLinks
import Breakdown.CertCell.AssemblyPairingStage
import Breakdown.CertCell.AssemblyEliminationStage
import Breakdown.CertCell.AssemblyBandTurned
import Breakdown.CertCell.AssemblyTreeState
import Breakdown.CertCell.AssemblyCellRange
import Breakdown.CertCell.RowsMatchAssemble
import Breakdown.CertCell.GaugeKeyConj
import Breakdown.CertCell.GaugeKeyRealLabel
import Breakdown.CertCell.GaugePlanePair
import Breakdown.CertCell.GaugePlaneOdd
import Breakdown.CertCell.AssemblyRowExpansionLink
import Breakdown.CertCell.CreditLeavesBound
import Breakdown.CertCell.InstancePairSurrogateClosed
import Breakdown.CertCell.AssemblyRowExpansionLow
import Breakdown.CertCell.AssemblyRowExpansionDeactSplit
import Breakdown.CertCell.AssemblyRowExpansionRestDeact
import Breakdown.CertCell.AssemblyRowExpansionActuator
import Breakdown.CertCell.AssemblyRowExpansionAllowance
import Breakdown.CertCell.AssemblyRowExpansion
import Breakdown.CertCell.AssemblyRowExpansionRest
import Breakdown.CertCell.AssemblyRowExpansionRestError
import Breakdown.CertCell.AssemblyRowExpansionLongPiece
import Breakdown.CertCell.AssemblyPotentialLink
import Breakdown.CertCell.AssemblyPotentialEps
import Breakdown.CertCell.SideTraceMatch
import Breakdown.CertCell.AxisSideTrace
import Breakdown.CertCell.RadialStripTrace
import Breakdown.CertCell.HeightStripTrace
import Breakdown.CertCell.ModeRadialDerivative
import Breakdown.CertCell.CornerPointTrace
import Breakdown.CertCell.CornerAxisTrace
import Breakdown.CertCell.ModePlaneDerivatives
import Breakdown.CertCell.PressureModeDerivative
import Breakdown.CertCell.PressureModeIntegrable
import Breakdown.CertCell.PressurePlaneFlip
import Breakdown.CertCell.PotentialConstant
import Breakdown.CertCell.PotentialNegation
import Breakdown.CertCell.PotentialShift
import Breakdown.CertCell.PotentialOfGradient
import Breakdown.CertCell.HarmonicPressureSquare
import Breakdown.CertCell.HarmonicPressureFlip
import Breakdown.CertCell.StripDataFlipAxis
import Breakdown.CertCell.CornerDataFlipAxis
import Breakdown.CertCell.ModeAxisIntegrable
import Breakdown.CertCell.ModeAxisPlainIntegrable
import Breakdown.CertCell.AssemblyOddStream
import Breakdown.CertCell.AssemblyPressureFlip
import Breakdown.CertCell.HarmonicCornerData

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

theorem creditLeavesBound_closed : CreditEval.CreditLeavesBoundHolds :=
  creditLeavesBound creditPatchBound_closed creditEvalMatches_closed

theorem rowMomentExpansion_closed : Assembly.RowMomentExpansionHolds :=
  Assembly.rowMomentExpansion_of_parts Assembly.rowIdentity_holds Assembly.freqPieceBound_holds
    Assembly.errorPieceBound_holds Assembly.longPieceBound_holds Assembly.deactSplit_holds
    Assembly.deactPieceBound_holds Assembly.actuatorPieceBound_holds Assembly.allowanceSplit_holds
    Assembly.rowCombine

theorem potentialStage_closed : Assembly.PotentialStageHolds :=
  Assembly.potentialStageHolds_of_epsResolved Assembly.epsResolvedStage_holds

theorem planeFlipStrip_closed : PlaneFlipFacts.StripDataFlipAxisHolds :=
  SideTrace.stripDataFlipAxis planeDataFlip_closed SideTrace.heightStripTrace SideTrace.sideTraceMatch
    modeHeightDeriv_closed (SideTrace.modeAxisIntegrable Bridge.secondDerivEnergyIdentity)
    (SideTrace.modeAxisPlainIntegrable Bridge.secondDerivEnergyIdentity)
    (SideTrace.modePlaneDerivs Bridge.secondDerivEnergyIdentity)

theorem planeFlipCorner_closed : PlaneFlipFacts.CornerDataFlipAxisHolds :=
  SideTrace.cornerDataFlipAxis Bridge.modeFlip Bridge.cornerFlip Bridge.cornerTrace SideTrace.sideTraceMatch
    modeHeightDeriv_closed (SideTrace.modeAxisIntegrable Bridge.secondDerivEnergyIdentity)
    (SideTrace.modeAxisPlainIntegrable Bridge.secondDerivEnergyIdentity)
    (SideTrace.modePlaneDerivs Bridge.secondDerivEnergyIdentity)

theorem planeTraceFacts_closed : PlanePairInternal.PlaneTraceFacts :=
  ⟨CellCalculus.harmonicLift_holds, periodicSecondOrder_closed, planeFlipStrip_closed, planeFlipCorner_closed,
    SideTrace.pressureStripFlip SideTrace.pressureModeDeriv SideTrace.pressureModeIntegrable
      (SideTrace.pressurePlaneFlip SideTrace.potentialConstant) SideTrace.heightStripTrace SideTrace.sideTraceMatch,
    SideTrace.potentialShift,
    SideTrace.harmonicPressureSquare, SideTrace.harmonicPressureFlip⟩

theorem fieldGauge_closed : FieldGaugeParts := fun _ _ T hG =>
  T.fieldGaugeHolds_of hG T.fieldKeyConj_holds (TreeEntry.fieldRealLabelZero_holds T)
    (TreeEntry.fieldPlanePairZero_of planeTraceFacts_closed T)
    (TreeEntry.fieldPlaneOddZero_of planeFlipStrip_closed planeFlipCorner_closed CellCalculus.harmonicLift_holds
      periodicSecondOrder_closed T)

theorem pairingStage_closed : Assembly.PairingStageHolds :=
  Assembly.pairingStageHolds_of_lowTailSplit Assembly.lowTailSplit_holds
    (fun Kb hK B hB Q F hFm hFi => Assembly.Internal.PotentialTails.proj_orth_of_sq Kb hK B hB Q F hFm hFi)

theorem bandProfileTurned_closed : Assembly.BandProfileTurnedHolds :=
  Assembly.bandProfileTurned_holds periodicSecondOrder_closed CellCalculus.harmonicLift_holds

theorem cellLayerParts_closed : CellLayerParts :=
  cellLayerParts_of_stages InstancePair.pairSharesFromSurrogateProfiles_holds creditLeavesBound_closed
    (cellResidualFromConditions_of potentialStage_closed rowMomentExpansion_closed pairingStage_closed
      Assembly.eliminationStage_holds bandProfileTurned_closed)
    Assembly.treeState_holds
    (Assembly.rowsMatchFieldsHolds_of_lift planeTraceFacts_closed periodicSecondOrder_closed CellCalculus.harmonicLift_holds
      (fun D => Assembly.harmonicTraceIndependence_of_lift periodicSecondOrder_closed CellCalculus.harmonicLift_holds D))
    Assembly.rowsMatchStateOfFields_holds Assembly.cellStateInRowRange_holds
    fieldGauge_closed

section Closure

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem cellJunctions_closed (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e)
    (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T) (hY : CellLayerEntryConditions D R T e Y) :
    CellJunctions D R e T :=
  cellJunctions_of_parts cellLayerParts_closed D X R T e h hT Y hY

theorem rowRestClause_closed (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e)
    (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T) (hY : CellLayerEntryConditions D R T e Y) :
    CoerciveWeak.RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight :=
  rowRestClause_of_parts cellLayerParts_closed D X R T e h hT Y hY

theorem extendedCoerciveClause_closed (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e)
    (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T) (hY : CellLayerEntryConditions D R T e Y)
    (hrad : ∀ j ∈ D.cert.adjointSet, 0 ≤ D.cert.radius j)
    (hwup : ∀ y, D.cert.weightFn y ≤ D.cert.weightMax)
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖D.cert.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (D.cert.actuatorBound ^ 2))
    {epsSup epsGradSup ratio : ℝ}
    (hm : ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn (D.cert.model q) (D.modelHess q) D.cert.weight epsSup epsGradSup ratio)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt D.cert.weight) ^ 2 / D.coercivity
      + ratio / (D.pieces 0).cμ) / Real.sqrt D.coercivity ≤ D.cert.coerciveL2)
    (hPin : Real.sqrt (D.pinWeight / D.coercivity) ≤ D.cert.coercivePin) :
    CoerciveWeak.ExtendedCoerciveClause D.cert :=
  extendedCoerciveClause_of_parts cellLayerParts_closed D X R T e h hT Y hY hrad hwup hnorm hm hL2 hPin

end Closure

end CertCell

end Breakdown
