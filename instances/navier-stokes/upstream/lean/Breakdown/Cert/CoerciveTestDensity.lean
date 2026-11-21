import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

def GradSolenoidalDensityHolds : Prop :=
  ∀ X : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume →
    IsTimePeriodic X → periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ →
    (∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (gradientAt (q σ) y) = 0) →
    (∀ ψ, IsPeriodicTestField ψ → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (ψ σ y) = 0) →
    ∀ᵐ z : ℝ × Space, X z.1 z.2 = 0

def CurlGraphDensityHolds : Prop :=
  ∀ F Q : ℝ → Space → Space, ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2) → IsTimePeriodic F →
    (∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) → IsSolenoidalPartOf F Q →
    ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
          ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2))
        Filter.atTop (nhds 0)

end Coercive

end Breakdown
