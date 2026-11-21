import Breakdown.FracCell.StCellBound

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def CellModeBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      CellScalars.localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
          - CellScalars.nearWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R
          - CellScalars.farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R / R.farShare
          - 2 * ∑ a ∈ R.rowSet, μ a * CellScalars.rowYPair c K S R B x.2.2.2.1 ζ x.1 x.2.1 a
          - ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2
          - CellScalars.rowSquare c K S R B μ (fun _ _ => True)
          - CellScalars.rowSquareFar c K S R B μ / (1 - R.farShare)
        ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
              + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
          + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p)
          + 2 / (4 * Real.pi) *
              ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)

end CellAnalysis

end CellCert

end Breakdown
