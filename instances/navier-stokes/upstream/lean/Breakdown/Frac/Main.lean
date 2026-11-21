import Breakdown.Frac.SpaceExports
import Breakdown.Frac.TorusBlowupExports

namespace Breakdown

theorem fractional_breakdown_on_space_proved (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnSpace α :=
  fracBreakdownOnSpace α hα₁ hα₂ h

theorem fractional_breakdown_on_torus_proved (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnTorus α :=
  fracBreakdownOnTorus α hα₁ hα₂ h

end Breakdown
