import Breakdown.FracCell.StEnergyProof

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis SteadyCert

def CircleWeakStatement : Prop :=
  ∀ (f : Space → ℝ) (g : Space → Space), LocallyIntegrable f volume → LocallyIntegrable g volume →
    (∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = -∫ y, φ y * inner ℝ (g y) (unitVector j)) →
    (∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      IntervalIntegrable (fun θ => f (cylPoint p.1 θ p.2)) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun θ => inner ℝ (g (cylPoint p.1 θ p.2)) (angularUnit θ)) volume 0
        (2 * Real.pi)) ∧
    ∀ w : ℝ → ℂ, ContDiff ℝ ∞ w → Function.Periodic w (2 * Real.pi) →
      ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
            w θ * ((p.1 * inner ℝ (g (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) =
          -∫ θ in (0 : ℝ)..(2 * Real.pi), deriv w θ * (f (cylPoint p.1 θ p.2) : ℂ)

end Breakdown.CellCert.CellEnergy
