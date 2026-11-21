import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def ModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect ∧
      ∀ b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect

def AngularModeStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * gradMode m n G 0 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 0 - modeVec m n v p.1 p.2 1 ∧
      (p.1 : ℂ) * gradMode m n G 1 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 1 + modeVec m n v p.1 p.2 0 ∧
      (p.1 : ℂ) * gradMode m n G 2 1 p = ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 2

end CellFormula

end CellCert

end Breakdown
