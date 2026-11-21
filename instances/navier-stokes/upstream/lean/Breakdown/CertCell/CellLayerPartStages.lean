import Breakdown.CertCell.CellLayerPartProofs
import Breakdown.CertCell.AssemblyLinkInitial
import Breakdown.CertCell.AssemblyOffModes
import Breakdown.CertCell.AssemblyFormSplit
import Breakdown.CertCell.CouplingGlobalLeaf

noncomputable section

namespace Breakdown

namespace CertCell

theorem initialState_closed : InitialStateHolds :=
  Assembly.initialStateHolds_of_split Assembly.formSplit_holds Coupling.globalLeaf

theorem cellLayerParts_of_stages (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hCredit : CreditEval.CreditLeavesBoundHolds) (hRes : CellResidualFromConditions) (hTree : Assembly.TreeStateHolds)
    (hRF : Assembly.RowsMatchFieldsHolds) (hRS : Assembly.RowsMatchStateOfFieldsHolds)
    (hSI : Assembly.CellStateInRowRangeHolds) (hFG : FieldGaugeParts) : CellLayerParts :=
  cellLayerParts_of_cell initialState_closed hPair hCredit Assembly.offModeConditionSound_holds
    Assembly.offModesVanishHolds hRes hTree hRF hRS hSI hFG

end CertCell

end Breakdown
