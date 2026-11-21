import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellEnergy

open CellAnalysis CellFormula

section Rows

variable {D : Type} [Fintype D] [DecidableEq D]

def rowApply (row : D → ℂ) (u : D → ℂ) : ℂ := ∑ d, row d * u d

end Rows

section Cell

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
  (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q)

end Cell

section Low

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)

end Low

section Forms

open SteadyCert Assembly

variable {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
  (S : CellScalars) (Cl : CellClasses) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)

def dataVector (u : D → ℂ) (κ ζ : Fin k → ℝ) : D ⊕ (Fin k ⊕ Fin k) → ℂ :=
  Sum.elim u (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

end Forms

structure Represents {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (m : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ) : Prop where
  strain : ∀ n a b j l, u (I.strainSlot n a b j l) = B.coef K (gradMode m n G a b) j l
  velocity : ∀ n a j l, u (I.velocitySlot n a j l) = B.coef K (fun p => modeVec m n v p.1 p.2 a) j l
  radial_face : ∀ n e a b l, (e = 0 → K.r₁ ≠ 0) → rowApply (I.radialFaceRow n e a b l) u =
    radialFaceMoment K (gradMode m n G a b) (radialGradMode m n H a b) e (B.heightPoly l)
  height_face : ∀ n e a b j, rowApply (I.heightFaceRow n e a b j) u =
    heightFaceMoment K (gradMode m n G a b) (heightGradMode m n H a b) e (B.radialPoly j)

end CellEnergy

end CellCert

end Breakdown
