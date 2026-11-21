import Breakdown.Frac.StSpace
import Breakdown.Frac.StProfile

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def FracMildRegularStatement (α : ℝ) : Prop :=
  ∀ F : ScaledMildFramework Freq.X (dilExponent α), F.G = Freq.fracHeatX α → F.K = Freq.fracBilinX α →
    ∀ φ, IsTestField φ → ∀ (u : ℝ → Freq.X) (T : ℝ), 0 < T → F.IsMildOnIcc u 0 T →
    u 0 = Freq.embedX φ →
    ∃ (U : ℝ → Space → Space) (P : ℝ → Space → ℝ), FracSolutionOn α T U P ∧ U 0 = φ ∧
      EnergyBoundedOn T U ∧ GradientBoundedOn T U ∧
      ∀ t ∈ Icc 0 T, (Freq.velocity (u t) : Space → Space) =ᵐ[volume] U t

def FracOrbitRateFalseStatement (α : ℝ) : Prop :=
  ∀ F : ScaledMildFramework Freq.X (dilExponent α), F.D = Freq.fracDilX α →
    ∀ (R : Space ≃ₗᵢ[ℝ] Space) (w : ℝ → Freq.X) (P : ℝ), F.IsOrbit (Freq.rotX R) w P →
    ∀ (u : ℝ → Freq.X) (C κ : ℝ), 0 < κ →
    (∀ t ∈ Ico (0 : ℝ) 1, ‖F.D (1 - t) (u t) - w (-Real.log (1 - t))‖ ≤ C * (1 - t) ^ κ) →
    ∀ v : ℝ → Space → Space, ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 1 ×ˢ univ) →
    (∀ t ∈ Ico (0 : ℝ) 1, (Freq.velocity (u t) : Space → Space) =ᵐ[volume] v t) → False

def FracSpaceUnitBreakdownStatement (α : ℝ) : Prop :=
  RotatingFractionalProfileExists α → ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧ FracNoBoundedSolution α u₀

end Breakdown
