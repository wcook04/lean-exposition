import Breakdown.FracCell.StateBound
import Breakdown.FracCell.FormNonneg
import Breakdown.FracCell.QuadFormSplit
import Breakdown.FracCell.AdmissibleLinear
import Breakdown.FracCell.IntervalIdentity
import Breakdown.FracCell.IntervalMinimal
import Breakdown.FracCell.IntervalMonotone
import Breakdown.FracCell.SpectralTail
import Breakdown.FracCell.AxisClosed
import Breakdown.FracCell.IntervalClosed
import Breakdown.FracCell.SpectralBlocksMode
import Breakdown.FracCell.BlockLocal
import Breakdown.FracCell.CylIntegral
import Breakdown.FracCell.FieldWitness
import Breakdown.FracCell.OffAxisCore
import Breakdown.FracCell.OnAxisCore
import Breakdown.FracCell.RectOff
import Breakdown.FracCell.RectAxis
import Breakdown.FracCell.OffAxisCoreSlope
import Breakdown.FracCell.AxisLift
import Breakdown.FracCell.AxisLiftSlope
import Breakdown.FracCell.AxisLiftDeriv
import Breakdown.FracCell.ShapeGrad

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

theorem stateBound_of_cells (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (S : CellSplit k N) (hS : S.IsCellSplit c α) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue ((∑ K, S.cellMatrix K) + S.globalMatrix c) (S.stateOf x ζ)
        ≤ c.quadForm α x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
  stateBound_of_cells_of quadFormSplit α hα₁ hα₂ c hc S hS

theorem formNonneg_of_tree (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (S : CellSplit k N) (hS : S.IsCellSplit c α) (T : TreeCertificate S.slots k)
    (hT : IsTreeCertificate T)
    (hcells : ∃ e : T.Cell ≃ Fin S.cellCount ⊕ Fin S.delayCount,
      ∀ K, T.cellForm K = Sum.elim S.cellMatrix S.delayForm (e K))
    (hglobal : T.globalForm = S.globalMatrix c) :
    ∀ v G H, IsSecondOrderField c.order v G H → ∀ κ : Fin k → ℝ, ∀ Q, IsGradientField Q →
      IsClassField c.order Q → 0 ≤ c.quadForm α v G H κ Q :=
  formNonneg_of_tree_of quadFormSplit admissibleLinear α hα₁ hα₂ c hc S hS T hT hcells hglobal

end Assembly

namespace Spectral

open SteadyCert

theorem intervalMinimal_holds : IntervalMinimalStatement := intervalMinimal_of intervalIdentity

theorem intervalMonotone_holds : IntervalMonotoneStatement := intervalMonotone_of intervalIdentity intervalMinimal_holds

theorem intervalClosed_holds : IntervalClosedStatement := intervalClosed_of intervalIdentity intervalMinimal_holds

theorem blockBound_of_parts (hL : BlockLocalStatement) (hC : CylStatement) : BlockBoundStatement :=
  blockBound_of_cyl intervalIdentity intervalMinimal_holds intervalMonotone_holds intervalClosed_holds axisClosed_holds hL hC

theorem blockBound_of_cores (hOff : OffAxisCoreStatement) (hOn : OnAxisCoreStatement) : BlockBoundStatement :=
  blockBound_of_field_cyl intervalIdentity intervalMinimal_holds intervalMonotone_holds intervalClosed_holds
    axisClosed_holds (fieldWitness_of_cores intervalClosed_holds hOff hOn) cylIntegral

theorem spectral_of_blocks_of_bound (hb : BlockBoundStatement) {k N : ℕ} (c : FracCellData k N) (sd : SpectralData)
    (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  ⟨hb c sd h, tail_holds c sd h⟩

theorem spectral_of_blocks_of_parts (hL : BlockLocalStatement) (hC : CylStatement) {k N : ℕ} (c : FracCellData k N)
    (sd : SpectralData) (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  spectral_of_blocks_of_bound (blockBound_of_parts hL hC) c sd h

theorem spectral_of_blocks_of_cores (hOff : OffAxisCoreStatement) (hOn : OnAxisCoreStatement) {k N : ℕ}
    (c : FracCellData k N) (sd : SpectralData) (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  spectral_of_blocks_of_bound (blockBound_of_cores hOff hOn) c sd h

theorem spectral_of_blocks_of_leaves (hG : ShapeGradStatement) (hL : AxisLiftStatement) {k N : ℕ}
    (c : FracCellData k N) (sd : SpectralData) (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  spectral_of_blocks_of_cores (offAxisCore_of_rect rectOff_holds shapeNorm_holds hG) (onAxisCore_of_rect rectAxis_holds hL) c sd h

theorem spectral_of_blocks_of_derivs (hL : ShapeSlopeStatement) (hD : ShapeDerivStatement) (hA : LiftDerivStatement)
    {k N : ℕ} (c : FracCellData k N) (sd : SpectralData) (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  spectral_of_blocks_of_cores (offAxisCore_of_parts rectOff_holds hL hD)
    (onAxisCore_of_rect rectAxis_holds (axisLift_of_parts liftSlope_holds hA)) c sd h

theorem spectral_of_blocks {k N : ℕ} (c : FracCellData k N) (sd : SpectralData) (h : IsSpectralData c sd) :
    (∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2) ∧
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ)) :=
  spectral_of_blocks_of_derivs shapeSlope_holds shapeDeriv_holds liftDeriv_holds c sd h

end Spectral

end CellCert

end Breakdown
