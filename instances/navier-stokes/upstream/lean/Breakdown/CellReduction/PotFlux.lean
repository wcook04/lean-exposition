import Breakdown.CellReduction.PotentialShape

open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

theorem fluxPotentialRegular_of
    (hdiv : ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F →
      ∀ σ, IsWeakMatrixDivergence (fluxMap P F σ) (matrixDivergence (fluxMap P F σ)))
    (hdec : ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
      AEStronglyMeasurable (fun z : ℝ × Space => fluxMap P F z.1 z.2) volume ∧
      (∀ σ y, ‖fluxMap P F σ y‖ ≤ C / (1 + ‖y‖) ^ 2) ∧
      ∀ σ, ∀ᵐ y, ‖y‖ * ‖matrixDivergence (fluxMap P F σ) y‖ ≤ C / (1 + ‖y‖) ^ 2) :
    FluxPotentialRegular := by
  intro P F hP hF
  obtain ⟨C, hmeas, hbound, hdivbound⟩ := hdec P F hP hF
  exact ⟨C, hmeas, hdiv P F hP hF, hbound, hdivbound⟩

end PotentialShape

end Breakdown
