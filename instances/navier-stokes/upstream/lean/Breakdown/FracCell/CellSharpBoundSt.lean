import Breakdown.FracCell.CellFormBoundSharpSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def IsWeightedSquareOn (K : CellBox) (F : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable F (volume.restrict K.rect) ∧ IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect

def SharpTargetSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∀ n ∈ R.yModes, ∀ a b : Fin 3,
          IsWeightedSquareOn K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b)) ∧
      (∀ n ∈ S.resolved, ∀ a : Fin 3,
          IsWeightedSquareOn K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a)) ∧
      (∀ r ∈ R.rowSet, ∀ n ∈ S.resolved ∪ S.band, ∀ a b : Fin 3,
          IsWeightedSquareOn K (fun p => CellScalars.rowCouplingFolded c K S R r n p a b)) ∧
      (∀ r ∈ R.rowSet, ∀ n ∈ S.resolved, ∀ a : Fin 3,
          IsWeightedSquareOn K (fun p => CellScalars.rowCouplingVelocity c K R r n p a))

def SharpCoreStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      ∃ (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ),
        Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, (S.symWeight n jl.1 jl.2 * symSq (σ n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (σ n jl.1 jl.2)))
            + ∑ n ∈ S.resolved, S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2)
          else 0) ∧
        CellScalars.localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
            + CellScalars.sharpForm c K S R B μ x.2.2.2.1 ζ x.1 x.2.1 σ τ
            - ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2
          ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
                + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
            + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p)
            + 2 / (4 * Real.pi) *
                ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)

end CellAnalysis

end CellCert

end Breakdown
