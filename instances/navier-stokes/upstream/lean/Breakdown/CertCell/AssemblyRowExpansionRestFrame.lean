import Breakdown.CertCell.AssemblyPotentialModelFrame

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

def VecFieldFrameStatement : Prop :=
  ∀ (M : CellMesh) (F : CellVecField M.count) (m : ℕ) (K : Fin M.count), IsCellMesh M →
    F.IsConjugateClosed M.box →
    ∀ᵐ p ∂(volume.restrict (M.box K).rect), ∀ τ φ : ℝ, ∀ a : Fin 3,
      ((fibVel (F.field M.box m) (planePoint p) τ φ a : ℝ) : ℂ)
        = ∑ α ∈ F.labels K, labelPhase m α τ φ * F.planeValue M.box K α a p

end Internal

end Assembly

end CertCell

end Breakdown
