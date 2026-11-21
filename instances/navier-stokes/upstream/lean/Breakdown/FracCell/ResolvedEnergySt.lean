import Breakdown.FracCell.CellDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def comboGrad (κ : Fin 3 → Fin 3 → ℂ) (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, κ a b * gradMode m n G a b p

def comboThird (κ : Fin 3 → Fin 3 → ℂ) (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, κ a b * modeThird m n H a b c p

def ModeSquareIntegrableStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ),
        AEStronglyMeasurable (comboGrad κ m n G) (volume.restrict K.rect) ∧
        IntegrableOn (fun p => K.lineWeight p.1 * ‖comboGrad κ m n G p‖ ^ 2) K.rect ∧
        ∀ c : Fin 3, AEStronglyMeasurable (comboThird κ m n H c) (volume.restrict K.rect) ∧
          IntegrableOn (fun p => p.1 * ‖comboThird κ m n H c p‖ ^ 2) K.rect

def ModeRadialPartsStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ), ContDiff ℝ 1 ψ →
        (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p
            = -∫ p in K.rect, comboGrad κ m n G p *
                CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p

def ModeHeightPartsStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ), ContDiff ℝ 1 ψ →
        (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p
            = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p

def RadialCrossStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q : ℕ) (F Fr : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict K.rect) → AEStronglyMeasurable Fr (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
    IntegrableOn (fun p => p.1 * ‖Fr p‖ ^ 2) K.rect →
    (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) →
    K.pairOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
      (fun p => Fr p - CellBox.radialDeriv (K.proj Q Q F) p) (CellBox.radialDeriv (K.proj Q Q F)) = 0

def HeightCrossStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q : ℕ) (F Fz : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict K.rect) → AEStronglyMeasurable Fz (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
    IntegrableOn (fun p => p.1 * ‖Fz p‖ ^ 2) K.rect →
    (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p) →
    K.pairOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
      (fun p => Fz p - CellBox.heightDeriv (K.proj Q Q F) p) (CellBox.heightDeriv (K.proj Q Q F)) = 0

def ResolvedComponentStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q q : ℕ) (n : ℤ), (K.IsAxis → n = 0) →
    ∀ (F Fr Fz h : ℝ × ℝ → ℂ),
      AEStronglyMeasurable F (volume.restrict K.rect) → AEStronglyMeasurable Fr (volume.restrict K.rect) →
      AEStronglyMeasurable Fz (volume.restrict K.rect) → AEStronglyMeasurable h (volume.restrict K.rect) →
      IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
      IntegrableOn (fun p => p.1 * ‖Fr p‖ ^ 2) K.rect →
      IntegrableOn (fun p => p.1 * ‖Fz p‖ ^ 2) K.rect →
      IntegrableOn (fun p => p.1 * ‖h p‖ ^ 2) K.rect →
      (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
            = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) →
      (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
            = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p) →
      K.radialEnergy Q q F Fr + K.heightEnergy Q q F Fz + K.angularEnergy Q (fun p => (p.1 : ℂ) * h p)
          + (K.tailGradWeight Q F Fr Fz + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * h p))
        ≤ ∫ p in K.rect, p.1 * (‖Fr p‖ ^ 2 + ‖h p‖ ^ 2 + ‖Fz p‖ ^ 2)

end CellAnalysis

end CellCert

end Breakdown
