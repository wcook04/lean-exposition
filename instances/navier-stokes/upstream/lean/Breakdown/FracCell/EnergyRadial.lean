import Breakdown.FracCell.EnergyRadialParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

theorem componentRadial (hT : RadialTraceStatement) : ComponentRadialStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hE n C
  rw [RadialForm.value_add, RadialForm.value_add,
    RadialPieces.proj_piece hT α c K B S I v G H u hE n C,
    RadialPieces.outer_piece hT α c K B S I v G H u hE n C]
  unfold CellBox.radialEnergy
  by_cases h : K.r₁ = 0
  · simp only [h, if_true, RadialForm.value_zero]
  · simp only [h, if_false, RadialPieces.inner_piece hT α c K B S I v G H u hE n C h]

end Breakdown.CellCert.CellEnergy
