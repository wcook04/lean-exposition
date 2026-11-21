import Breakdown.Frac.StTorusStepCompare

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

theorem fracComparisonSmall_of_parts (α : ℝ) (hα : 1 < α) (hL : FracLambdaComparison α hα)
    (hS : FracSeedComparison α hα) : FracComparisonSmall α hα := by
  intro F hK hG hD P k θ b E _ _ _ J ψ A hl hl1 hP hk hL2 hθ hθ1 hb δ hδ
  exact (hL F hK hG hD P k θ b A hl hl1 hP hk hL2 hθ hθ1 hb δ hδ).elim fun T₁ h₁ =>
    (hS F hK hG hD P k θ b E J ψ hl hl1 hP hk hL2 hθ hθ1 hb δ hδ).elim fun T₂ h₂ =>
      ⟨min T₁ T₂, lt_min h₁.1 h₂.1, fun T hT hT1 hTT Jt hJt =>
        ⟨h₁.2 T hT hT1 (lt_of_lt_of_le hTT (min_le_left _ _)),
          h₂.2 T hT hT1 (lt_of_lt_of_le hTT (min_le_right _ _)) Jt hJt⟩⟩

end Breakdown.Periodic
