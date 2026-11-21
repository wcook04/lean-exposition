import Breakdown.FracCell.CellDataDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert CellAnalysis

def CylModeWeakStatement : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (f : Space → F) (g : Space → (Space →L[ℝ] F)), LocallyIntegrable f volume →
    (∀ j : Fin 3, LocallyIntegrable (fun y => g y (unitVector j)) volume) →
    (∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g y (unitVector j)) →
    ∀ (L : ℝ × ℝ → (F →L[ℝ] ℝ)), ContDiff ℝ ∞ L →
    ∀ (m : ℕ) (n : ℤ) (ψ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (L (Real.cos θ, Real.sin θ) (f (cylPoint p.1 θ p.2)) : ℂ) =
        -∫ p, (ψ p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
            (L (Real.cos θ, Real.sin θ) (g (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (L (Real.cos θ, Real.sin θ) (f (cylPoint p.1 θ p.2)) : ℂ) =
        -∫ p, (ψ p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
            (L (Real.cos θ, Real.sin θ) (g (cylPoint p.1 θ p.2) axialUnit) : ℂ))

def CylChangeStatement : Prop :=
  ∀ h : Space → ℂ, Integrable h →
    ∫ y, h y = ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
      (q.1 : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), h (cylPoint q.1 θ q.2)

def AxisWeakStatement : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (f : Space → F) (g : Space → (Space →L[ℝ] F)), LocallyIntegrable f volume →
    (∀ j : Fin 3, LocallyIntegrable (fun y => g y (unitVector j)) volume) →
    (∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g y (unitVector j)) →
    ∀ (W : ℝ × ℝ → (F →L[ℝ] ℂ)), ContDiff ℝ ∞ W →
    ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (Integrable (fun y => ((fderiv ℝ ψ (cylRadius y, y 2) (1, 0) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y)) ∧
        Integrable (fun y => ((fderiv ℝ ψ (cylRadius y, y 2) (0, 1) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y)) ∧
        Integrable (fun y => ((ψ (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y)
            (g y (EuclideanSpace.single 0 (y 0 / cylRadius y) + EuclideanSpace.single 1 (y 1 / cylRadius y)))) ∧
        Integrable (fun y => ((ψ (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (g y axialUnit))) ∧
      (∫ y, ((fderiv ℝ ψ (cylRadius y, y 2) (1, 0) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y) =
        -∫ y, ((ψ (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y)
            (g y (EuclideanSpace.single 0 (y 0 / cylRadius y) + EuclideanSpace.single 1 (y 1 / cylRadius y)))) ∧
      (∫ y, ((fderiv ℝ ψ (cylRadius y, y 2) (0, 1) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y) =
        -∫ y, ((ψ (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (g y axialUnit))

end Breakdown.CellCert.CellFormula
