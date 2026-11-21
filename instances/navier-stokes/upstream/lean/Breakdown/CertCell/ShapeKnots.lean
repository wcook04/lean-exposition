import Breakdown.CertCell.ShapeDefs
import Breakdown.CertCell.ShapeKnotHessian
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline)

def ShapeKnotsNull : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → volume (shapeKnots P D) = 0

theorem mirrorKnots_closed (P : ShapeParams) (D : TimeFieldData) : KnotZero.IsMirrorClosed (mirrorKnots P D) := by
  intro p
  constructor
  · rintro (h | h)
    · exact Or.inr (by simpa using h)
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by simpa using h)

def ShapeKnotsNullSpace : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P →
    volume {y : Space | KnotZero.planeOf y ∈ mirrorKnots P D} = 0

end GivenShape

end CertCell

end Breakdown
