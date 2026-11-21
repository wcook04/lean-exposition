import Breakdown.FracCell.ParamDefs
import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def radialFaceMoment (K : CellBox) (F dF : ℝ × ℝ → ℂ) (e : Fin 2) (t : ℝ → ℝ) : ℂ :=
  if e = 1 then radialStripMoment K.r₂ K.r₁ K.z₁ K.z₂ F dF t
  else radialStripMoment K.r₁ K.r₂ K.z₁ K.z₂ F dF t

def heightFaceMoment (K : CellBox) (F dF : ℝ × ℝ → ℂ) (e : Fin 2) (t : ℝ → ℝ) : ℂ :=
  if e = 1 then heightStripMoment K.z₂ K.z₁ K.r₁ K.r₂ (fun r => r) F dF t
  else heightStripMoment K.z₁ K.z₂ K.r₁ K.r₂ (fun r => r) F dF t

namespace FaceSegment

variable (S : FaceSegment)

end FaceSegment

namespace CellDatum

variable {modes : Finset ℤ} {Q q segs psegs corners : ℕ}

end CellDatum

namespace CellLayout

variable (L : CellLayout)

end CellLayout


namespace CellLayout

variable (L : CellLayout)

end CellLayout

namespace CellLayout

variable (L : CellLayout)

end CellLayout

def LowEntryStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ i d, L.lowEntry i = some d → L.trueData x d = CellScalars.lowCoef c K S B x i

def AdmissiblePotentialStatement : Prop :=
  ∀ Q : Space → Space, IsGradientField Q → ∃ q, IsPotentialOf Q q

def SegmentIndependenceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (n : ℤ) (S S' : FaceSegment),
      IsFaceSegment S → IsFaceSegment S' → S.radial = S'.radial → S.level = S'.level → S.lo = S'.lo →
        S.hi = S'.hi → S.testCoef = S'.testCoef → (S.radial → S.level ≠ 0) →
        (S.radial → 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other) → ∀ (a : Fin 3) (d : ℕ),
          S.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d =
            S'.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d ∧
          (if S.radial then S.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (L.secondModeOf n x a 0 2) d
            else S.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) =
          (if S'.radial then S'.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (L.secondModeOf n x a 0 2) d
            else S'.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) ∧
          S.moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d =
            S'.moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d

def CornerIndependenceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (n : ℤ) (cr cz orr oz orr' oz' : ℝ), cr ≠ 0 → orr ≠ cr → oz ≠ cz →
      orr' ≠ cr → oz' ≠ cz → 0 ≤ min cr orr → 0 ≤ min cr orr' → ∀ a : Fin 3,
        cornerMoment cr orr cz oz (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
            (L.secondModeOf n x a 0 2) =
          cornerMoment cr orr' cz oz' (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
            (L.secondModeOf n x a 0 2)

def RelationsHoldStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ : L.RelIndex, ∑ d, L.relationRow ρ d * L.trueData x d = 0

def TrueParamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ (P : ParamData L.Datum) (sel : Fin P.relCount → L.RelIndex), IsCellParam L P sel →
      ∀ x : FieldTuple k, IsAdmissible c x → P.param (L.trueData x) = L.trueData x

namespace CellLayout

variable (L : CellLayout)

def strainFaceValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (e : Fin 4) (a b : Fin 3) (l : ℕ) : ℂ :=
  if e.val < 2 then radialFaceMoment L.box (L.gradModeOf n x a b) (L.secondModeOf n x a b 0)
      (sideRadialIndex e) (L.bases.heightPoly l)
  else heightFaceMoment L.box (L.gradModeOf n x a b) (L.secondModeOf n x a b 2)
      (sideHeightIndex e) (L.bases.radialPoly l)

end CellLayout

def StrainFaceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ), l ≤ L.degSide → (e.val = 0 → K.r₁ ≠ 0) →
        L.strainFaceValue n x e a b l = ∑ d, L.strainFaceRow n e a b l d * L.trueData x d


namespace CellLayout

variable (L : CellLayout)

end CellLayout

def ConjugateDataStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsPressureLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ d, L.trueData x (L.conjDatum d) = (starRingEnd ℂ) (L.trueData x d)

def PlaneDeletedStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsPressureLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ d, L.IsPlaneDeleted d → L.trueData x d = 0

namespace CellLayout

variable (L : CellLayout)

end CellLayout

structure IsGaugeShift {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (g : GaugeShift k) : Prop where
  linear : ∀ (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
    g.left (a • x + b • y) = a * g.left x + b * g.left y ∧
      g.right (a • x + b • y) = a * g.right x + b * g.right y ∧
      ∀ r, g.point (a • x + b • y) r = a * g.point x r + b * g.point y r
  point_left : L.box.r₁ ≠ 0 → ∀ x, g.point x L.box.r₁ = g.left x
  point_right : ∀ x, g.point x L.box.r₂ = g.right x

namespace CellLayout

variable (L : CellLayout)

def rootShifted {k : ℕ} (left right : FieldTuple k → ℝ) (x : FieldTuple k)
    (i : Fin L.presCount × Fin L.degSide) : ℝ :=
  L.pressureDatumValue x i + L.shiftCoefLeft i * left x + L.shiftCoefRight i * right x

end CellLayout

def GaugeShiftOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (sp : GaugeSpec L), IsPressureLayout c K S B L → IsGaugeSpec L sp →
    ∀ left right : FieldTuple k → ℝ,
      (∀ (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
        left (a • x + b • y) = a * left x + b * left y ∧ right (a • x + b • y) = a * right x + b * right y) →
      (∀ e, sp.edge = some e → ∀ x, IsAdmissible c x → right x = left x + L.gaugeJump sp x) →
      (∀ r ∈ sp.roots, ∀ x, IsAdmissible c x → L.rootShifted left right x r = 0) →
      IsGaugeShift c L (L.gaugeShiftOf left right) ∧
        ∀ x : FieldTuple k, IsAdmissible c x → ∀ d, L.IsGaugeDeleted d →
          L.shiftedData (L.gaugeShiftOf left right) x d = 0

def ShiftedRealReductionStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (g : GaugeShift k), IsPressureLayout c K S B L → IsGaugeShift c L g → ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ d, L.IsGaugeDeleted d → L.shiftedData g x d = 0) →
      L.expandSystem (L.realPart (L.shiftedData g x)) = L.realPart (L.shiftedData g x)

def ShiftedParamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ (P : ParamData L.Datum) (sel : Fin P.relCount → L.RelIndex), IsCellParam L P sel →
      ∀ (g : GaugeShift k) (x : FieldTuple k), IsAdmissible c x →
        P.param (L.shiftedData g x) = L.shiftedData g x

end CellFormula

end CellCert

end Breakdown
