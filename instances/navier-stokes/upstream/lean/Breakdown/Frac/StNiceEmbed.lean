import Breakdown.Frac.StRealize

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Freq

def FracNiceEmbedPower (α : ℝ) : Prop :=
  ∀ φ, IsNiceField φ → IsSspOf (embedX φ) (embedX (negSsp φ)) ∧
    IsFracOf α (embedX φ) (embedX (fractionalPowerAt α φ))

end Breakdown.Freq
