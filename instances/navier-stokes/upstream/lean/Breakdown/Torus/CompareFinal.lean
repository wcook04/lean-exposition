import Breakdown.Torus.CompareStatements
import Breakdown.Torus.CompareHeatDivFree
import Breakdown.Torus.CompareChain
import Breakdown.Torus.CompareLambda
import Breakdown.Torus.CompareEntryR3
import Breakdown.Torus.CompareEntryTorus
import Breakdown.Torus.CompareFrame
import Breakdown.Torus.CompareWindow
import Breakdown.Torus.CompareTail
import Breakdown.Torus.CompareInvSeries
import Breakdown.Torus.CompareSplit
import Breakdown.Torus.CompareDilate
import Breakdown.Torus.CompareSeedEntry
import Breakdown.Torus.CompareLambdaAssembly
import Breakdown.Torus.CompareSeedAssembly

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

theorem comparisonSmall_of_parts (hL : LambdaComparison) (hS : SeedComparison) : ComparisonSmall := by
  intro hK F hK' hG hD P k θ b E _ _ _ J ψ A hl hl1 hP hk hL2 hθ hθ1 hb δ hδ
  exact (hL hK F hK' hG hD P k θ b A hl hl1 hP hk hL2 hθ hθ1 hb δ hδ).elim fun T₁ h₁ =>
    (hS hK F hK' hG hD P k θ b E J ψ hl hl1 hP hk hL2 hθ hθ1 hb δ hδ).elim fun T₂ h₂ =>
      ⟨min T₁ T₂, lt_min h₁.1 h₂.1, fun T hT hT1 hTT Jt hJt =>
        ⟨h₁.2 T hT hT1 (lt_of_lt_of_le hTT (min_le_left _ _)),
          h₂.2 T hT hT1 (lt_of_lt_of_le hTT (min_le_right _ _)) Jt hJt⟩⟩

theorem comparisonSmall (hHLC : HeatDivFreeComparison) (hFHC : FreeHeatComparison)
    (hRB : R3LambdaBound) (hTB : TorusLambdaBound) (hRR : RestrictR3Bound) (hTN : TransplantNorm)
    (hS : SeqOpSpec) (hV : PieceConvSpec) (hC : PieceCompSpec) (hO : OperatorNormBounds)
    (hP : PieceOperatorStatement) (hFR : Freq.FieldOpRealized) (hH : Freq.HeatSemigroup)
    (hD : Freq.DilationAlgebra) (hVD : Freq.VelocityDilate) (hG : Freq.GradSixDecay) (hE : Freq.EmbedNorm)
    (hED : Freq.EmbedDilate) : ComparisonSmall :=
  have hSh : HeatDivFreeShift := heatDivFreeShift hFR hH
  have hCo : HeatDivFreeContinuous := heatDivFreeContinuous hSh hH
  comparisonSmall_of_parts
    (lambdaComparison invSeriesEntry hS hC hO
      (windowBound
        (r3EntryFormula (r3ChainFormula hP) (r3LambdaFormula hS hV hRB hCo) hSh hCo hRB)
        (torusEntryFormula (torusChainFormula hP) (torusLambdaFormula hS hV hTB) hTB)
        (frameChange hVD hD hFR) splitIntegralBound hHLC hRB hTB hRR (advectShellBounds hG hE) hD hCo)
      (tailBound shiftChainNorm hO hRR))
    (seedComparison
      (r3SeedEntry invSeriesEntry hS (r3ChainFormula hP) hO hP)
      (torusSeedEntry invSeriesEntry hS (torusChainFormula hP) hO hP)
      transplantDilate dilateTest hFHC hED hTN hRR hS hC hH hD)

end Breakdown.Periodic
