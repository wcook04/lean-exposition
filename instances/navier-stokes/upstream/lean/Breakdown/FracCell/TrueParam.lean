import Breakdown.FracCell.StCoordsProof

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

theorem trueParam_of (h1 : RelationsHoldStatement) (h2 : ParamRecoverStatement) : TrueParamStatement := by
  intro k N c K S B L hL P sel hP x hx
  refine h2 P hP.param (L.trueData x) ?_
  funext i
  rw [Pi.zero_apply, Matrix.mulVec, dotProduct, hP.rows i]
  exact h1 c K S B L hL x hx (sel i)

end Breakdown.CellCert.CellFormula
