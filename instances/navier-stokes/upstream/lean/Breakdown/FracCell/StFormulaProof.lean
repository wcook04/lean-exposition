import Breakdown.FracCell.FormulaDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

def SynthesisStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases), IsCellBox K → IsCellBases K B →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ n ∈ S.resolved, ∀ p ∈ K.rect,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p

def YCoefLinearStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R →
    ∀ (U : Aug S k → ℂ) (n : ℤ) (j l : ℕ),
      (∀ a b : Fin 3, yCoef c K S B U n j l a b = ∑ e, U e * yVec c K S B n j l a b e) ∧
        ∀ a : Fin 3, yVelCoef c K S B U n j l a = ∑ e, U e * velVec c K S B n j l a e

def IsRealQuadratic {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ M : Matrix ι ι ℝ, ∀ w, f w = w ⬝ᵥ (M *ᵥ w)

def polarized {ι : Type} [DecidableEq ι] (f : (ι → ℝ) → ℝ) : Matrix ι ι ℝ := fun e e' =>
  (f (Pi.single e 1 + Pi.single e' 1) - f (Pi.single e 1) - f (Pi.single e' 1)) / 2

def PolarizationStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ), IsRealQuadratic f →
    ∀ w, Finite.quadValue (polarized f) w = f w

def FormulaQuadraticStatement : Prop :=
  ∀ {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N) (K : CellBox)
    (B : CellBases) (R : CellRows N slots k), IsLinearMap ℝ F.coordToData →
    letI := F.dataFintype; IsRealQuadratic (F.formulaValue c K B R)

end CellFormula

end CellCert

end Breakdown
