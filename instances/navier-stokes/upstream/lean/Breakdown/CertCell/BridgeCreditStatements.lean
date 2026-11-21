import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal ComplexOrder
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace CreditPatch

variable (R : CreditPatch)

def data (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin R.dataCount → ℂ :=
  fun d => (R.segment (R.dataOf d).1).velocityData R.label v G 2 (R.dataOf d).2

end CreditPatch

def CreditPatchBoundHolds : Prop :=
  ∀ (R : CreditPatch), IsCreditPatch R →
    ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
      Coupling.quadForm R.credit (R.data v G)
        ≤ ∫ p in R.region, R.charge p * cnormSq (modeVel (flipLabel R.label) v 0 (planePoint p)) * p.1

end Bridge

end CertCell

end Breakdown
