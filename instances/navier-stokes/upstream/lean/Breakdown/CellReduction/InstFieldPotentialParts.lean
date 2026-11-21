import Breakdown.CertCell.ShapeDefs

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

def radialAmpField (P : ShapeParams) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ) (V : Space →L[ℝ] Space) (y : Space) :
    Fin 3 → ℂ :=
  (Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      CellCert.GivenFields.weightPoly 1 e (chartCoord P y) *
      f (chartCoord P y, CellCert.GivenFields.heightRatio y)) • fun i => ((V y i : ℝ) : ℂ)

def RadialAmpFieldRegular : Prop :=
  ∀ (P : ShapeParams) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ) (V : Space →L[ℝ] Space), IsShapeParams P → 3 ≤ e →
    ContDiff ℝ 1 f → ‖V‖ ≤ 1 →
    ContDiff ℝ 1 (radialAmpField P j e f V) ∧ ∃ C : ℝ, ∀ y, ‖radialAmpField P j e f V y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
      ‖fderiv ℝ (radialAmpField P j e f V) y‖ ≤ C / (1 + ‖y‖) ^ 3

def PrimitiveSmoothHolds : Prop :=
  ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ 1 g → ContDiff ℝ 1 (fun z : ℝ × ℝ => ∫ u in (-1 : ℝ)..z.2, g (z.1, u))

end Instantiation

end CellReduction

end Breakdown
