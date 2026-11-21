import Breakdown.Frac.ScaledScale
import Breakdown.Frac.ScaledOrbitPhysical
import Breakdown.Frac.ScaledOrbitNorm
import Breakdown.Frac.ScaledProfilePiece
import Breakdown.Frac.ScaledGlue
import Breakdown.Frac.ScaledMonodromy
import Breakdown.Frac.ScaledStepData
import Breakdown.Frac.ScaledMain
import Breakdown.Transfer.Exports
import Breakdown.Spectral.RealDichotomy

namespace Breakdown

theorem scaledScale : ScaledScaleStatement := scaledScale_of varConstIntegral

theorem scaledOrbitPhysical : ScaledOrbitPhysicalStatement := scaledOrbitPhysical_of varConstIntegral

theorem scaledOrbitNorm : ScaledOrbitNormStatement :=
  scaledOrbitNorm_of scaledOrbitPhysical mildUnique mildSmallData

theorem scaledProfilePiece : ScaledProfilePieceStatement := scaledProfilePiece_of scaledOrbitPhysical

theorem scaledGlue : ScaledGlueStatement := scaledGlue_of scaledScale concat shift

theorem scaledMonodromy : ScaledMonodromyStatement :=
  scaledMonodromy_of pieceOperator compactPiece scaledProfilePiece

theorem scaledStepData : ScaledStepDataStatement :=
  scaledStepData_of scaledMonodromy scaledProfilePiece scaledOrbitBound pieceOperator periodicInverse
    exists_section dichotomyHolds

theorem scaledTransferHolds : ScaledTransferHolds :=
  scaledTransferHolds_of scaledStepData contraction piecePerturbation scaledProfilePiece scaledGlue

end Breakdown
