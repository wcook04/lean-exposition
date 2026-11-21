import Breakdown.FracCell.CellCoordsDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def RelRadialCoefStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inl ρ) d * L.trueData x d) = 0

def RelHeightCoefStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inl ρ)) d * L.trueData x d) = 0

def RelTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inl ρ))) d * L.trueData x d) = 0

def RelTraceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ)))) d * L.trueData x d) = 0

def RelZeroModeStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ))))) d * L.trueData x d) = 0

def RelRadialSideStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ)))))) d
        * L.trueData x d) = 0

def RelHeightSideStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ))))))) d
        * L.trueData x d) = 0

def RelAxisStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl ρ)))))))) d * L.trueData x d) = 0

def RelStreamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl ρ))))))))) d * L.trueData x d) = 0

def RelSideSplitStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr ρ))))))))) d * L.trueData x d) = 0

def IsConjClosedParam (L : CellLayout) (P : ParamData L.Datum) : Prop :=
  ∀ d, (d ∈ P.skeleton ↔ L.conjDatum d ∈ P.skeleton) ∧ (d ∈ P.solvedSet ↔ L.conjDatum d ∈ P.solvedSet)

def ExactFormulaBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R → R.farSupport ⊆ lowSupport S → 0 < c.splitVisc →
    ∀ F : CellFormulaInputs k N S, IsFormulaInputs α c K S B Cl R.rowSet F →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (F.exactFormula c K B R) (F.coordsOf x ζ c.splitVisc) ≤
        CellScalars.cellForm c K S R α B Cl x ζ / c.splitVisc

end CellFormula

end CellCert

end Breakdown
