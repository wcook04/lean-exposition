import Breakdown.Transfer.VarConstIntegral
import Breakdown.Transfer.PieceOperator
import Breakdown.Transfer.Restrict
import Breakdown.Transfer.Unique
import Breakdown.Transfer.SmallData
import Breakdown.Transfer.CompactSimple
import Breakdown.Transfer.CompactPiece
import Breakdown.Transfer.PiecePerturbation
import Breakdown.Transfer.Scale
import Breakdown.Transfer.OrbitPhysical
import Breakdown.Transfer.OrbitNorm
import Breakdown.Transfer.ProfilePiece
import Breakdown.Transfer.Glue
import Breakdown.Transfer.Monodromy
import Breakdown.Transfer.DiscreteDichotomy
import Breakdown.Transfer.PeriodicInverse
import Breakdown.Transfer.Contraction
import Breakdown.Transfer.Section
import Breakdown.Transfer.StepData
import Breakdown.Transfer.Main

namespace Breakdown

theorem pieceOperator : PieceOperatorStatement := pieceOperator_of varConstIntegral

theorem mildUnique : UniqueStatement := unique_of varConstIntegral restrict

theorem mildSmallData : SmallDataStatement := smallData_of varConstIntegral pieceOperator

theorem compactSimple : CompactSimpleStatement := compactSimple_of varConstIntegral pieceOperator

theorem compactPiece : CompactPieceStatement := compactPiece_of compactSimple

theorem piecePerturbation : PiecePerturbationStatement :=
  piecePerturbation_of varConstIntegral pieceOperator

theorem scale : ScaleStatement := scale_of varConstIntegral

theorem orbitPhysical : OrbitPhysicalStatement := orbitPhysical_of varConstIntegral

theorem orbitNorm : OrbitNormStatement := orbitNorm_of orbitPhysical mildUnique mildSmallData

theorem profilePiece : ProfilePieceStatement := profilePiece_of orbitPhysical

theorem glue : GlueStatement := glue_of scale concat shift

theorem monodromy : MonodromyStatement := monodromy_of pieceOperator compactPiece profilePiece

theorem periodicInverse : PeriodicInverseStatement := periodicInverse_of discreteDichotomy

theorem stepData (hD : DichotomyHolds) : StepDataStatement :=
  stepData_of monodromy profilePiece orbitBound pieceOperator periodicInverse exists_section hD

theorem transferHolds_of_dichotomy (hD : DichotomyHolds) : TransferHolds :=
  transferHolds_of (stepData hD) contraction piecePerturbation profilePiece glue

end Breakdown
