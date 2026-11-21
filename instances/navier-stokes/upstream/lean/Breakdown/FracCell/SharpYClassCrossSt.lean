import Breakdown.FracCell.SharpYChargeSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

namespace SharpParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

open Classical in
def classCrossDensity (T : Set ℤ) (n n' : ℤ) (p : ℝ × ℝ) : ℝ :=
  (if n' ∈ T then
      pairWave c n n' p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
        + pairWave c n' n p (sharpGrad c K S x n' p) (sharpVel c K S x n' p) (lowGrad c K S x n p) (lowVel c K S x n p)
      else 0).re

end SharpParts

open SharpParts

def ClassPointwiseStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R →
    ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ (F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
      (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ),
      -(∑ n ∈ S.resolved, ∑ i : Fin Cl.count,
          if n ∈ Cl.resolvedPart i then Cl.shareWeight i * Cl.classLoss S.splitLength i p (s n) (v n) else 0)
        - ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
          ∑ i, Cl.classLoss S.splitLength i p (s' n') (v' n') / Cl.shareWeight i)
      ≤ ∑ n ∈ S.resolved, ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
          pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re

def ClassProductSplitStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R →
    ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ (i : Fin Cl.count) (L F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
      (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ),
      -(Cl.shareWeight i * ∑ n ∈ L, Cl.classLoss S.splitLength i p (s n) (v n))
        - (∑ n' ∈ F, Cl.classLoss S.splitLength i p (s' n') (v' n')) / Cl.shareWeight i
      ≤ ∑ n ∈ L, ∑ n' ∈ F, (if n - n' ∈ Cl.modes i then
          (pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re else 0)

def ClassCrossRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n ∈ S.resolved, ∀ n', IntegrableOn (fun p : ℝ × ℝ => p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p) K.rect) ∧
      (∀ n ∈ S.resolved, ∀ i, IntegrableOn (fun p : ℝ × ℝ => p.1 * Cl.classLoss S.splitLength i p
        (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)) K.rect)

end CellAnalysis

end CellCert

end Breakdown
