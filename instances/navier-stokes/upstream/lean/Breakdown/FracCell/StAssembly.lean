import Breakdown.FracCell.AssemblyDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

def QuadFormSplitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ S : CellSplit k N, S.IsCellSplit c α →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∑ K, S.cellPart c α K x ζ) + S.exteriorPart c α x + quadValue (S.globalMatrix c) (S.stateOf x ζ)
        ≤ c.quadForm α x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

def AdmissibleLinearStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N),
    IsAdmissible c 0 ∧ (∀ x x', IsAdmissible c x → IsAdmissible c x' → IsAdmissible c (x + x')) ∧
      ∀ (r : ℝ) x, IsAdmissible c x → IsAdmissible c (r • x)

end Assembly

end CellCert

end Breakdown
