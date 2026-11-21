import Breakdown.FracCell.FormulaDataDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def ModeHeightAxisStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (n : ℤ) (a : Fin 3) (R Z : ℝ), IntegrableOn (gradMode m n G a 2) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z)

def ModeWeakIdentityStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (n : ℤ) (a : Fin 3) (ψ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a = -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a = -∫ p, (ψ p : ℂ) * gradMode m n G a 2 p) ∧
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * gradMode m n G a 2 p =
        -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a 0 p =
        -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p)

end Breakdown.CellCert.CellFormula
