import Breakdown.FracCell.CellDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert

def ModeRadialWeakStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p) K.rect ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
        ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a + ((ψ p.1 : ℝ) : ℂ) * gradMode m n G a 0 p)
          * ((t p.2 : ℝ) : ℂ) = 0

end CellAnalysis

end CellCert

end Breakdown
