import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def fracNormSq (r : ℝ) (f : Space → CSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖f ξ‖ₑ ^ 2

def heatPart (a : ℝ) (f : Space → CSpace) (t : ℝ) (ξ : Space) : CSpace :=
  ((heatSymbol (t - a) ξ : ℝ) : ℂ) • f ξ

end Breakdown.SmoothFlow
