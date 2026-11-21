import Breakdown.FracCell.StAngularMode

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def AngularHeightModeStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * modeThird m n H 0 1 2 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 0 2 p - gradMode m n G 1 2 p ∧
      (p.1 : ℂ) * modeThird m n H 1 1 2 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 1 2 p + gradMode m n G 0 2 p ∧
      (p.1 : ℂ) * modeThird m n H 2 1 2 p = ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 2 2 p

end CellFormula

end CellCert

end Breakdown
