import Breakdown.FracCell.CellSharpBoundSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def strainLin (σ W : Fin 3 → Fin 3 → ℂ) : ℝ :=
  2 * (entryPairing (fun a b => (σ a b + σ b a) / 2) (fun a b => (W a b + W b a) / 2)
    + entryPairing (fun a b => (σ a b - σ b a) / 2) (fun a b => (W a b - W b a) / 2)).re

def velLin (τ W : Fin 3 → ℂ) : ℝ := 2 * (CellScalars.vecPair τ W).re

namespace CellScalars

def rowStrainTarget {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (n : ℤ) (j l : ℕ) : Fin 3 → Fin 3 → ℂ :=
  fun i q => if n ∈ S.resolved ∪ S.band then
      ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n p i q) j l
    else 0

def rowVelocityTarget {k N : ℕ} (c : FracCellData k N) (K : CellBox) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (n : ℤ) (j l : ℕ) : Fin 3 → ℂ :=
  fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingVelocity c K R a n p i) j l

def rowStrainTerm {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (n : ℤ) (j l : ℕ) : ℝ :=
  if n ∉ S.resolved ∨ S.degHigh < max j l then strainLin (σ n j l) (rowStrainTarget c K S R B μ n j l) else 0

def rowVelocityTerm {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (n : ℤ) (j l : ℕ) : ℝ :=
  if S.degHigh ≤ max j l then velLin (τ n j l) (rowVelocityTarget c K R B μ n j l) else 0

def rowFarTerm {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) (jl : ℕ × ℕ) : ℝ :=
  if S.degNear < max jl.1 jl.2 then
    (∑ n ∈ R.yModes, rowStrainTerm c K S R B μ σ n jl.1 jl.2)
      + ∑ n ∈ S.resolved, rowVelocityTerm c K S R B μ τ n jl.1 jl.2
  else 0

def sharpRowForm {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (μ : Fin N → ℝ) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) : ℝ :=
  (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      rowStrainTerm c K S R B μ σ n j l)
    + (∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      rowVelocityTerm c K S R B μ τ n j l)
    + ∑' jl : ℕ × ℕ, rowFarTerm c K S R B μ σ τ jl

end CellScalars

def SharpSplitStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      ∃ (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ),
        Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, (S.symWeight n jl.1 jl.2 * symSq (σ n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (σ n jl.1 jl.2)))
            + ∑ n ∈ S.resolved, S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2)
          else 0) ∧
        ∃ Q : ℝ,
          CellScalars.localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
              + CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1 σ τ + Q
            ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
                  + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
              + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p) ∧
          ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
            CellScalars.sharpRowForm c K S R B μ σ τ - ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2
              ≤ Q + 2 / (4 * Real.pi) *
                  ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)

def sharpStrainCoef {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases) (x : FieldTuple k) :
    ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ :=
  fun n j l a b => B.coef K (gradMode c.order n x.2.1 a b) j l

def sharpVelocityCoef {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases) (x : FieldTuple k) :
    ℤ → ℕ → ℕ → Fin 3 → ℂ :=
  fun n j l a => B.coef K (fun p => modeVec c.order n x.1 p.1 p.2 a) j l

def SharpEnergyStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
          (∑ n ∈ R.yModes, (S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
            + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)))
          + ∑ n ∈ S.resolved, S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2)
        else 0)

def SharpBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      ∃ Q : ℝ,
        CellScalars.localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
            + CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
                (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x) + Q
          ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
                + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
            + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p) ∧
        ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
          CellScalars.sharpRowForm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
              - ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2
            ≤ Q + 2 / (4 * Real.pi) *
                ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)

def SharpCoefTailStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n ∈ R.yModes, ∀ a b : Fin 3, Summable (fun jl : ℕ × ℕ =>
          (1 + (radialEigen K jl.1 + heightEigen K jl.2)) * ‖sharpStrainCoef c K B x n jl.1 jl.2 a b‖ ^ 2)) ∧
      (∀ n ∈ S.resolved, ∀ a : Fin 3, Summable (fun jl : ℕ × ℕ =>
          (1 + (radialEigen K jl.1 + heightEigen K jl.2)) * ‖sharpVelocityCoef c K B x n jl.1 jl.2 a‖ ^ 2))

end CellAnalysis

end CellCert

end Breakdown
