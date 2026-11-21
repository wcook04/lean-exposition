import Breakdown.CertCell.RowsMatchKeyRows

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def KeyPlaneFlip (D : CellLayerData k C nE nM) (L : CellLayout) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ι : ℤ × ℤ) (key : SkeletonKey),
      key ≠ SkeletonKey.private_ → (GaugeKey.keyMode key = some ι.1 ∨ ∃ p, key = SkeletonKey.stream p) →
      GaugeKey.KeyInHalfPlane key → keyOnPlane key →
      keyHarmonic L (labelTime ι) v G H Pg key
        = (keyFlipSign key : ℂ) * keyHarmonic L (labelTime ι) v G H Pg (keyWithMode (-ι.1) key)

end Assembly

end CertCell

end Breakdown
