import Breakdown.FracCell.FormulaDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

namespace CellCoords

variable {k slots : ℕ} (C : CellCoords k slots)

end CellCoords

structure IsCellCoords (α : ℝ) {k N : ℕ} (c : FracCellData k N) (Sp : CellSplit k N) (K₂ : Fin Sp.cellCount)
    (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N Sp.slots k)
    (C : CellCoords k Sp.slots) : Prop where
  visc_pos : 0 < c.splitVisc
  given_symm : C.given.IsSymm
  layout_valid : IsPressureLayout c K S B C.layout
  param_valid : IsCellParam C.layout C.param C.selection
  param_conj_closed : ∀ d, (d ∈ C.param.skeleton ↔ C.layout.conjDatum d ∈ C.param.skeleton) ∧
    (d ∈ C.param.solvedSet ↔ C.layout.conjDatum d ∈ C.param.solvedSet)
  rows_shape : IsRowShape c K S R
  row_traces : ∀ a ∈ R.rowSet, ∀ s n i, ∃ Pl : ℝ → ℂ,
    (∃ cf : Fin (C.layout.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * ((C.layout.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((C.layout.segment s).radial → p.1 = (C.layout.segment s).level → rowModeVec c a n p i = Pl p.2) ∧
        (¬ (C.layout.segment s).radial → p.2 = (C.layout.segment s).level → rowModeVec c a n p i = Pl p.1)
  row_normal_traces : ∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ,
    (∃ cf : Fin C.layout.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((C.layout.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((C.layout.presSegment s).radial → p.1 = (C.layout.presSegment s).level →
          rowModeVec c a n p 0 = Pl p.2) ∧
        (¬ (C.layout.presSegment s).radial → p.2 = (C.layout.presSegment s).level → rowModeVec c a n p 2 = Pl p.1)
  gauge_spec : IsGaugeSpec C.layout C.gaugeSpec
  gauge_linear : ∀ (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
    C.gaugeLeft (a • x + b • y) = a * C.gaugeLeft x + b * C.gaugeLeft y ∧
      C.gaugeRight (a • x + b • y) = a * C.gaugeRight x + b * C.gaugeRight y
  edge_jump : ∀ e, C.gaugeSpec.edge = some e → ∀ x, IsAdmissible c x →
    C.gaugeRight x = C.gaugeLeft x + C.layout.gaugeJump C.gaugeSpec x
  root_zero : ∀ r ∈ C.gaugeSpec.roots, ∀ x, IsAdmissible c x → C.layout.rootShifted C.gaugeLeft C.gaugeRight x r = 0
  skeleton_slot : ∀ x, IsAdmissible c x → ∀ j, ∑ i, C.Tmap j i * Sp.moment x i =
    C.layout.realPart (C.layout.shiftedData (C.layout.gaugeShiftOf C.gaugeLeft C.gaugeRight) x) ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1 /
      presetScale C.layout c.splitVisc ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1.1
  skeleton_free : ∀ j i, ∑ l, C.Tmap j l * Sp.freeMap l i = 0
  matrix_embedding : ∀ w : Fin Sp.slots ⊕ Fin k → ℝ,
    quadValue (Sp.cellMatrix K₂) w ≤
      4 * Real.pi * c.splitVisc * quadValue C.given (C.restrictState c.splitVisc Sp.kappaSlot w)
  far_low : R.farSupport ⊆ lowSupport S
  given_le_exact : ∀ (s : Fin (systemSkeletonCoords C.layout C.param).card → ℝ)
    (ξ : Fin (systemInteriorCoords C.layout C.param).card → ℝ) (κ' ζ' : Fin k → ℝ),
    quadValue C.given (Sum.elim s (Sum.elim κ' ζ')) ≤
      quadValue ((C.formula c K S B Cl R α).exactFormula c K B R)
        (Sum.elim (fun i => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i))
          (Sum.elim (fun j => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j)) (Sum.elim κ' ζ')))

end CellCoordinates

end CellCert

end Breakdown
