import Breakdown.FracCell.SharpYSharpCross
import Breakdown.FracCell.SharpTargetSquare

namespace Breakdown

namespace CellCert

namespace CellAnalysis

theorem yTargetSquare_holds : YTargetSquareStatement := by
  intro α h1 h2 k N c hform K S B Cl slots R hcell hax x hx ζ
  obtain ⟨hF, hV, -, -⟩ := sharpTargetSquare α h1 h2 c hform K S B Cl R hcell hax x hx ζ
  exact ⟨fun n hn i q => hF n hn i q, fun n hn i => hV n hn i⟩

end CellAnalysis

end CellCert

end Breakdown
