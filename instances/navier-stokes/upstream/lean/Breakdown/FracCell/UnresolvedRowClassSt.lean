import Breakdown.FracCell.SharpBoundCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

def unresolvedPairAt {k N : ℕ} (c : FracCellData k N) (K : CellBox) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  ((K.lineWeight p.1 : ℝ) : ℂ) *
    (entryPairing (fun i q => gradMode c.order n x.2.1 i q p) (rowCouplingStrain c K R a n p)
      + vecPair (modeVec c.order n x.1 p.1 p.2) (rowCouplingVelocity c K R a n p))

def unresolvedPairPoint {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else (unresolvedPairAt c K R x a n p).re

def unresolvedChargePoint {k N : ℕ} (c : FracCellData k N) (S : CellScalars) (Cl : CellClasses)
    (x : FieldTuple k) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else
    ∑ i, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 * curlSq (fun a b => gradMode c.order n x.2.1 a b p)
      + Cl.curlDev i p ^ 2 * vecSq (modeVec c.order n x.1 p.1 p.2))

def classRowSq {k N : ℕ} (c : FracCellData k N) {slots : ℕ} (R : CellRows N slots k) (Cl : CellClasses)
    (μ : Fin N → ℝ) (i : Fin Cl.count) (p : ℝ × ℝ) : ℝ :=
  ∑ m ∈ R.rowModes, vecSq (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
    ((μ a : ℝ) : ℂ) * rowMode c a m p b)

end CellScalars

def UnresolvedRowPointStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
    ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ F : Finset ℤ,
      -(2 * ∑ a ∈ R.rowSet, μ a * ∑ n ∈ F, CellScalars.unresolvedPairPoint c K S R x a n p)
        ≤ p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p
          + ∑ i, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i

def UnresolvedPairIntegrableStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet, ∀ n : ℤ, n ∉ S.resolved ∪ S.band →
      IntegrableOn (CellScalars.unresolvedPairAt c K R x a n) K.rect

def ClassRowSqStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ μ : Fin N → ℝ, ∀ i : Fin Cl.count,
      IntegrableOn (fun p => p.1 * CellScalars.classRowSq c R Cl μ i p) K.rect ∧
      ∫ p in K.rect, p.1 * CellScalars.classRowSq c R Cl μ i p
        ≤ ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i), μ a ^ 2 / (4 * Real.pi)

def UnresolvedChargeFiniteStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ F : Finset ℤ,
      IntegrableOn (fun p => p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p) K.rect ∧
      ∫ p in K.rect, p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p
        ≤ CellScalars.unresolvedRowCharge c K S Cl x

end CellAnalysis

end CellCert

end Breakdown
