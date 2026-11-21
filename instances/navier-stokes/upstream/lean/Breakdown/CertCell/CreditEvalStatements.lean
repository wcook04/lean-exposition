import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.BridgeCreditStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace CreditEval

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def creditData (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (j : Fin R.creditCount)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : ℕ → ℂ) : Fin (R.creditPatch j).dataCount → ℂ :=
  fun d => cellState D.mesh (R.creditOwner j d) (R.layouts (R.creditOwner j d)) v G H Pg κ ζ
    (fun i => η (R.portKey (R.creditOwner j d) i)) (Sum.inl (Sum.inl (R.creditCoord j d)))

def CreditEvalMatchesHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D), CreditEvalConditions D R →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      ∀ (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : ℕ → ℂ) (j : Fin R.creditCount),
        creditData D R j v G H Pg κ ζ η = (R.creditPatch j).data v G

def CreditLeavesBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D), IsCellMesh D.mesh →
    Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → CreditEvalConditions D R →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      ∀ (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : ℕ → ℂ),
        2 * ∑ j, Coupling.quadForm (R.creditPatch j).credit (creditData D R j v G H Pg κ ζ η)
          ≤ ∑ K, creditShare D R K v

end CreditEval

end CertCell

end Breakdown
