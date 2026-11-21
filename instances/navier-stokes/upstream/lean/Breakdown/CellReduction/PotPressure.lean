import Breakdown.CellReduction.PotentialShape

open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

def PressureWeakGradientRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F →
    AEStronglyMeasurable (fun z : ℝ × Space => pressureValue P F z.1 z.2) volume ∧
    ∀ σ, IsWeakScalarGradient (pressureValue P F σ) (gradientAt (pressureValue P F σ))

def PressureDecayRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
    (∀ σ y, |pressureValue P F σ y| ≤ C / (1 + ‖y‖) ^ 2) ∧
    ∀ σ, ∀ᵐ y, ‖y‖ * ‖gradientAt (pressureValue P F σ) y‖ ≤ C ∧
      ‖y‖ ^ 3 * ‖gradientAt (pressureValue P F σ) y‖ ≤ C

theorem pressurePotentialRegular_of (hw : PressureWeakGradientRegular) (hd : PressureDecayRegular) :
    PressurePotentialRegular := by
  intro P F hP hF
  obtain ⟨hm, hg⟩ := hw P F hP hF
  obtain ⟨C, hv, ha⟩ := hd P F hP hF
  exact ⟨C, hm, hg, hv, ha⟩

end PotentialShape

end Breakdown
