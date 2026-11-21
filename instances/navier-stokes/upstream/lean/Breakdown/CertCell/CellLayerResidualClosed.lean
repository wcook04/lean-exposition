import Breakdown.CertCell.CellLayerPartStages
import Breakdown.CertCell.AssemblyResidual
import Breakdown.CertCell.AssemblyPiecesFinite
import Breakdown.CertCell.AssemblyAllocationSplit
import Breakdown.CertCell.AssemblyBandIntegrable
import Breakdown.CertCell.AssemblyPotentialLeaf
import Breakdown.CertCell.AssemblyRowShareStacked
import Breakdown.CertCell.AssemblyRowRemoval
import Breakdown.CertCell.AssemblyTailGain
import Breakdown.CertCell.AssemblyTopBound
import Breakdown.CertCell.TailPointwise

noncomputable section

namespace Breakdown

namespace CertCell

theorem cellResidualFromConditions_of (hP : Assembly.PotentialStageHolds) (hM : Assembly.RowMomentExpansionHolds)
    (hQ : Assembly.PairingStageHolds) (hE : Assembly.EliminationStageHolds) (hBT : Assembly.BandProfileTurnedHolds) :
    CellResidualFromConditions :=
  fun D R A P T W hN hc hs h hS => Assembly.cellResidual_of_conditions Assembly.cellPiecesFiniteHolds
    Assembly.allocationSplitHolds Assembly.trueFieldRegularHolds Assembly.bandProfileIntegrable_holds hP hQ
    (Assembly.rowStage_of_parts Assembly.rowShareStacked_holds Assembly.rowRemoval) hM
    (Assembly.tailStage_of_parts TailBand.tailAbsorption Assembly.tailGainHolds)
    (Assembly.topBound_of velocitySixthIntegral_closed) hE hBT D R A P T W hN hc hs h hS

end CertCell

end Breakdown
