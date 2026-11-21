import Breakdown.CellReduction.AdjointEntryDefs

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

def WeakGradientSlopeHolds : Prop :=
  ∀ (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (M : ℝ),
    Continuous f → IsWeakGradient f g → (∀ᵐ y, ‖g y‖ ≤ M) →
      ∀ x y, ‖f x - f y‖ ≤ 3 * M * ‖x - y‖

def WeightedPairingIntegrableHolds : Prop :=
  ∀ (v T : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume →
    (∀ᵐ σ, IsWeakGradient (v σ) (G σ)) →
    (∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤) →
    periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ →
    AEStronglyMeasurable (fun z : ℝ × Space => T z.1 z.2) volume →
    periodLIntegral (fun σ y => ‖y‖ ^ 2 * ‖T σ y‖ ^ 2) < ⊤ →
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (T z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)

def CentreResidualFieldHolds : Prop :=
  ∀ {k : ℕ} (r : AdjointDefectEntry k) (χ : Fin k → ℝ → Space → (Space →L[ℝ] Space))
    (P C γ D C' R₀ : ℝ) (W : ℝ → Space → Space),
    IsAdjointField r.field C γ → IsFlowPiece W D → IsPinData χ r.pins C' R₀ →
      ∃ C'' : ℝ, IsResidualField (adjointTransport P W r.field) r.pinFlux C'' γ

end AdjointDefect

end Breakdown
