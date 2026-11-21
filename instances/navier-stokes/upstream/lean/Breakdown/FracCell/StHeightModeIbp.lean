import Breakdown.FracCell.CellDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def HeightModeIbpStatement : Prop :=
  ∀ (m : ℕ) (n : ℤ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ K : CellBox, IsCellBox K → ∀ a : Fin 3,
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p) K.rect ∧
      ∀ f h : ℝ → ℝ, Continuous f → ContDiff ℝ 1 h → h K.z₁ = 0 → h K.z₂ = 0 →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a * ((f p.1 * deriv h p.2 : ℝ) : ℂ) =
          -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((f p.1 * h p.2 : ℝ) : ℂ)

end Breakdown.CellCert.CellFormula
