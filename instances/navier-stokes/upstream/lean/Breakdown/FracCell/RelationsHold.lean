import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem relationsHold_of (h1 : RelRadialCoefStatement) (h2 : RelHeightCoefStatement) (h3 : RelTurnStatement)
    (h4 : RelTraceStatement) (h5 : RelZeroModeStatement) (h6 : RelRadialSideStatement)
    (h7 : RelHeightSideStatement) (h8 : RelAxisStatement) (h9 : RelStreamStatement)
    (h10 : RelSideSplitStatement) : RelationsHoldStatement := by
  intro k N c K S B L hL x hx ρ
  rcases ρ with ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ
  · exact h1 c K S B L hL x hx ρ
  · exact h2 c K S B L hL x hx ρ
  · exact h3 c K S B L hL x hx ρ
  · exact h4 c K S B L hL x hx ρ
  · exact h5 c K S B L hL x hx ρ
  · exact h6 c K S B L hL x hx ρ
  · exact h7 c K S B L hL x hx ρ
  · exact h8 c K S B L hL x hx ρ
  · exact h9 c K S B L hL x hx ρ
  · exact h10 c K S B L hL x hx ρ

end Breakdown.CellCert.CellFormula
