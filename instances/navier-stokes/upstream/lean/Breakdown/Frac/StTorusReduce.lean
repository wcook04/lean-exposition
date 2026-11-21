import Breakdown.Frac.StTorusBasic
import Breakdown.Frac.StTorusCoef
import Breakdown.Torus.StatementsSmooth

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def FracTorusSmoothIsMild (α : ℝ) : Prop :=
  ∀ (u₀ : Space → Space) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsFractionalSolution α 1 u₀ u p → (∀ t ≥ 0, IsPeriodic (u t)) → (∀ t ≥ 0, IsPeriodic (p t)) →
      ∀ T : ℝ, 0 < T → IsFracTorusMildOnIcc α (fun t => toV (u t)) 0 T

def FracTorusDrift (α : ℝ) : Prop :=
  ∀ (u₀ : Space → Space) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsFractionalSolution α 1 u₀ u p → (∀ t ≥ 0, IsPeriodic (u t)) →
      ∃ (u' : ℝ → Space → Space) (p' : ℝ → Space → ℝ), IsFractionalSolution α 1 u₀ u' p' ∧
        (∀ t ≥ 0, IsPeriodic (u' t)) ∧ ∀ t ≥ 0, IsPeriodic (p' t)

def FracTorusBlowup (α : ℝ) : Prop :=
  ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergenceAt u₀ x = 0) ∧
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → V, u 0 = toV u₀ ∧ IsFracTorusMildOn α u 0 T ∧
      ¬ BddAbove ((fun t => ‖u t‖) '' Ico 0 T)

end Breakdown.Periodic
