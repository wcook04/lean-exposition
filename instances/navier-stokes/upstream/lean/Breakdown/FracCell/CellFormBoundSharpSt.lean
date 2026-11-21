import Breakdown.FracCell.CellFormBoundSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def strainPen (hs ha : ℝ) (σ Z : Fin 3 → Fin 3 → ℂ) : ℝ :=
  hs * symSq σ + ha * antiSq σ
    + 2 * (entryPairing (fun a b => (σ a b + σ b a) / 2) (fun a b => (Z a b + Z b a) / 2)
      + entryPairing (fun a b => (σ a b - σ b a) / 2) (fun a b => (Z a b - Z b a) / 2)).re

def velPen (hv : ℝ) (σ Z : Fin 3 → ℂ) : ℝ := hv * vecSq σ + 2 * (CellScalars.vecPair σ Z).re

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ} (R : CellRows N slots k)

def targetStrain (B : CellBases) (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (j l : ℕ) : Fin 3 → Fin 3 → ℂ := fun i q =>
  B.coef K (fun p => yFolded c K S κ ζ v G n p i q) j l
    + if n ∈ S.resolved ∪ S.band then
        ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n p i q) j l
      else 0

def targetVelocity (B : CellBases) (μ : Fin N → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (j l : ℕ) : Fin 3 → ℂ := fun i =>
  B.coef K (fun p => yVelocity c K S v G n p i) j l
    + ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingVelocity c K R a n p i) j l

def sharpStrainTerm (B : CellBases) (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (n : ℤ) (j l : ℕ) : ℝ :=
  if n ∉ S.resolved ∨ S.degHigh < max j l then
    strainPen (S.symWeight n j l) (S.antiWeight n j l) (σ n j l) (targetStrain c K S R B μ κ ζ v G n j l)
  else 0

def sharpVelocityTerm (B : CellBases) (μ : Fin N → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) (n : ℤ) (j l : ℕ) : ℝ :=
  if S.degHigh ≤ max j l then
    velPen (S.velWeight n j l) (τ n j l) (targetVelocity c K S R B μ v G n j l)
  else 0

def sharpFarTerm (B : CellBases) (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) (jl : ℕ × ℕ) : ℝ :=
  if S.degNear < max jl.1 jl.2 then
    (∑ n ∈ R.yModes, sharpStrainTerm c K S R B μ κ ζ v G σ n jl.1 jl.2)
      + ∑ n ∈ S.resolved, sharpVelocityTerm c K S R B μ v G τ n jl.1 jl.2
  else 0

def sharpForm (B : CellBases) (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) : ℝ :=
  (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      sharpStrainTerm c K S R B μ κ ζ v G σ n j l)
    + (∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      sharpVelocityTerm c K S R B μ v G τ n j l)
    + ∑' jl : ℕ × ℕ, sharpFarTerm c K S R B μ κ ζ v G σ τ jl

end CellScalars

def CellSharpBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      ∃ (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ),
        Summable (CellScalars.sharpFarTerm c K S R B μ x.2.2.2.1 ζ x.1 x.2.1 σ τ) ∧
        Summable (fun jl : ℕ × ℕ =>
          if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
              symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)
                  / S.symWeight n jl.1 jl.2
                + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)
                  / S.antiWeight n jl.1 jl.2
              else 0)
            + ∑ n ∈ S.resolved,
                vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) jl.1 jl.2)
                  / S.velWeight n jl.1 jl.2
          else 0) ∧
        Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
          (∑ n' ∈ S.resolved ∪ S.band,
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (S.symWeight n' jl.1 jl.2) (S.antiWeight n' jl.1 jl.2)).re)
          + ∑ n' ∈ S.resolved,
            vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n' p i) jl.1 jl.2)
              / S.velWeight n' jl.1 jl.2
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
