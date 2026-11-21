import Breakdown.FracCell.StFormulaProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem exactFormula_symm {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (R : CellRows N slots k) (F : CellFormulaInputs k N S) : (F.exactFormula c K B R).IsSymm := by
  ext e e'
  simp only [Matrix.transpose_apply, CellFormulaInputs.exactFormula]
  have key : ∀ a b : F.Coord → ℝ,
      F.formulaValue c K B R (a + b) - F.formulaValue c K B R a - F.formulaValue c K B R b =
        F.formulaValue c K B R (b + a) - F.formulaValue c K B R b - F.formulaValue c K B R a := by
    intro a b
    rw [add_comm a b]
    ring
  rw [key]

end CellFormula

end CellCert

end Breakdown
