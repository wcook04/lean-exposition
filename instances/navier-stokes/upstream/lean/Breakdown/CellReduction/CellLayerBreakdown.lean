import Breakdown.CertCell.CellLayerStatements
import Breakdown.Cert.ExtendedMain
import Breakdown.Weak.Main
import Breakdown.CellReduction.ReductionStatements
import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.InstanceStatements
import Breakdown.CellReduction.PotentialShape
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory Breakdown.CertCell Breakdown.CertCell.GivenShape

noncomputable section

namespace Breakdown

namespace CellLayerSystem

def shiftPieceFields {k : ℕ} (P : CellReduction.Instantiation.ProfileShapeEntry k) (W : ℝ → Space → Space) :
    Fin 2 → (Fin k → ℝ) → ℝ → Space → Space :=
  ![fun _ σ y => P.field 0 σ y - W σ y, fun q σ y => P.field q σ y - P.field 0 σ y]

def shiftPiecesOfSystem {k : ℕ} (P : CellReduction.Instantiation.ProfileShapeEntry k) (W : ℝ → Space → Space)
    (N : ShiftNumbers) : CertReduction.ShiftPieces k where
  count := 2
  piece := shiftPieceFields P W
  pieceGrad := fun a q σ y => fderiv ℝ (shiftPieceFields P W a q σ) y
  cubicForm := ![false, true]
  supNum := ![N.centreSup, N.boxSup]
  gradNum := ![N.centreGrad, N.boxGrad]

end CellLayerSystem

end Breakdown
