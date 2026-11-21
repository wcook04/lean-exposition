import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.ParamDefs
import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.EnergyDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

section Synthesis

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)

end Synthesis

section Pieces

variable {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
  (R : CellRows N slots k)

def augVector (x : FieldTuple k) (ζ : Fin k → ℝ) : Aug S k → ℂ :=
  Sum.elim (fun i => lowCoef c K S B x i.1)
    (Sum.elim (fun i => ((x.2.2.2.1 i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

end Pieces

def NearIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      nearWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R =
        quadFormValue (nearMatrix c K S B R) (augVector c K S B x ζ)

def RowYIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ a ∈ R.rowSet,
      rowYPair c K S R B x.2.2.2.1 ζ x.1 x.2.1 a = (linForm (rowYVec c K S B R a) (augVector c K S B x ζ)).re

def FarIdentityStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (R : CellRows N slots k), R.farSupport ⊆ lowSupport S →
    ∀ (x : FieldTuple k) (ζ : Fin k → ℝ),
      farFormValue c K S R B x ζ = quadFormValue (farMatrix S R) (augVector c K S B x ζ)

section RowFunctional

variable {k N slots : ℕ} (c : FracCellData k N) (α : ℝ)

def layoutRowValue (L : CellLayout) (R : CellRows N slots k) (a : Fin N) (u : L.Datum → ℂ) (κ : Fin k → ℝ) : ℝ :=
  (∑ d : L.Datum, layoutRowData c α L R a d * u d).re + ∑ i : Fin k, κ i * layoutRowKappa c a i

end RowFunctional

structure IsRowShape {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (R : CellRows N slots k) : Prop where
  row_slope : ∀ a ∈ R.rowSet, ∃ L : NNReal,
    LipschitzOnWith L (c.row a) (K.solid ∩ {y | 0 ≤ cylHeight y})
  row_smooth : ∀ a ∈ R.rowSet, ∀ δ : ℝ, 0 < δ → ∃ f : Space → Space, ContDiff ℝ 2 f ∧
    ∀ y ∈ K.solid, 0 ≤ cylHeight y → δ ≤ cylRadius y → c.row a y = f y
  row_mirror : ∀ a ∈ R.rowSet, ∀ y ∈ K.solid, cylHeight y < 0 → c.row a y = mirror (c.row a (mirror y))
  row_solenoidal : ∀ a ∈ R.rowSet, ∀ y ∈ K.solid,
    ∑ i : Fin 3, inner ℝ (fderiv ℝ (c.row a) y (unitVector i)) (unitVector i) = 0
  row_class : ∀ a ∈ R.rowSet, IsClassField c.order (c.row a)
  row_low_velocity : ∀ a ∈ R.rowSet, ∀ n i, ∃ P ∈ polyFn (S.degHigh - 1) (S.degHigh - 1),
    ∀ p ∈ K.rect, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * rowModeVec c a n p i = P p
  row_low_position : ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
    ∀ p ∈ K.rect, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * (frameY p b * rowModeVec c a n p i) = P p
  row_low_turn : ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
    ∀ p ∈ K.rect, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * (frameTurnY p b * rowModeVec c a n p i) = P p
  row_low_gradient : ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
    ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p

def LayoutRowValueStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R → IsRowShape c K S R → ∀ L : CellLayout, IsPressureLayout c K S B L →
    (∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1)) →
    (∀ a ∈ R.rowSet, ∀ s n, ∃ P : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, P t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = P p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = P p.1)) →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      lowRowValue c K S α x a = layoutRowValue c α L R a (L.trueData x) x.2.2.2.1

def GaugeInvarianceStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R → IsRowShape c K S R → ∀ (L : CellLayout), IsPressureLayout c K S B L →
    (∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = Pl p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = Pl p.1)) →
    ∀ g : GaugeShift k, IsGaugeShift c L g → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ a ∈ R.rowSet, ∀ (u : L.Datum → ℂ) (κ : Fin k → ℝ),
        layoutRowValue c α L R a (fun d => u d + L.pressureShift g x d) κ = layoutRowValue c α L R a u κ

namespace CellFormulaInputs

variable {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N) (K : CellBox)
  (B : CellBases) (R : CellRows N slots k)

def coordsOf (x : FieldTuple k) (ζ : Fin k → ℝ) (visc : ℝ) : F.Coord → ℝ :=
  Sum.elim (F.skeleton x) (Sum.elim (F.interior x) (Sum.elim (fun i => x.2.2.2.1 i / visc) (fun i => ζ i / visc)))

end CellFormulaInputs

structure IsFormulaInputs (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (Cl : CellClasses) (rowSet : Finset (Fin N)) (F : CellFormulaInputs k N S) : Prop where
  coord_linear : IsLinearMap ℝ F.coordToData
  data_represents : ∀ x : FieldTuple k, IsAdmissible c x →
    F.coordToData (Sum.elim (F.skeleton x) (F.interior x)) = F.trueData x
  lowEntry_agree : ∀ x : FieldTuple k, IsAdmissible c x → ∀ i : LowSupp S,
    (F.lowEntry i).elim 0 (F.trueData x) = lowCoef c K S B x i.1
  row_value : ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ rowSet,
    lowRowValue c K S α x a = F.rowValue a (F.trueData x) x.2.2.2.1
  local_form : ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
    letI := F.dataFintype; letI := F.dataDecEq;
    quadFormValue F.localForm (F.dataVec (F.trueData x) x.2.2.2.1 ζ) ≤
      localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1

section Canonical

variable {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
  (R : CellRows N slots k) (L : CellLayout) (P : ParamData L.Datum) (α : ℝ) (g : GaugeShift k)

end Canonical

def CanonicalInputsValidStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R → IsRowShape c K S R → ∀ (L : CellLayout) (P : ParamData L.Datum)
    (sel : Fin P.relCount → L.RelIndex), IsPressureLayout c K S B L → IsCellParam L P sel →
    ∀ g : GaugeShift k, IsGaugeShift c L g →
    (∀ a ∈ R.rowSet, ∀ s n i, ∃ Pl : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = Pl p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = Pl p.1)) →
    (∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = Pl p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = Pl p.1)) →
    IsFormulaInputs α c K S B Cl R.rowSet (canonicalInputs c K S B Cl R L P α g)

end CellFormula

end CellCert

end Breakdown
