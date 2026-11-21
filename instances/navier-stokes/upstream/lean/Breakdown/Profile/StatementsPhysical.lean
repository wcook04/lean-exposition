import Breakdown.Profile.StatementsSlice

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def physicalScale (t : ℝ) : ℝ := Real.sqrt ((1 - t)⁻¹)

def physicalTime (s₀ t : ℝ) : ℝ := s₀ - Real.log (1 - t)

def physicalField (W : ℝ → Space → Space) (s₀ t : ℝ) : Space → Space :=
  dilateField ((1 - t)⁻¹) (W (physicalTime s₀ t))

def physicalPressure (q : ℝ → Space → ℝ) (s₀ t : ℝ) : Space → ℝ :=
  fun x => (1 - t)⁻¹ * q (physicalTime s₀ t) (physicalScale t • x)

def PhysicalTimeDeriv : Prop :=
  ∀ W : ℝ → Space → Space, ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) →
    ∀ s₀ t : ℝ, t < 1 → ∀ x : Space,
      HasDerivAt (fun τ => physicalField W s₀ τ x)
        (physicalScale t ^ 3 •
          (deriv (fun σ => W σ (physicalScale t • x)) (physicalTime s₀ t)
            + (1 / 2 : ℝ) • W (physicalTime s₀ t) (physicalScale t • x)
            + (1 / 2 : ℝ) • fderiv ℝ (W (physicalTime s₀ t)) (physicalScale t • x)
                (physicalScale t • x))) t

def PhysicalMomentum : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀ t : ℝ, t < 1 → ∀ x : Space,
      HasDerivAt (fun τ => physicalField W s₀ τ x)
        (sumSecondPartialsAt (physicalField W s₀ t) x - advectionAt (physicalField W s₀ t) x
          - gradientAt (physicalPressure q s₀ t) x) t

def PhysicalDifference : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀ T : ℝ, T < 1 → ∃ K : ℝ, ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ x : Space,
      ‖physicalField W s₀ t x - physicalField W s₀ t' x‖ ≤ K * |t - t'| / (1 + ‖x‖) ^ 3

def PhysicalL2 : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀ T : ℝ, T < 1 →
      (∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T,
        Integrable (fun x => ‖physicalField W s₀ t x - physicalField W s₀ t' x‖ ^ 2)) ∧
      (∀ t₀ ∈ Icc 0 T, Filter.Tendsto
        (fun t => ∫ x, ‖physicalField W s₀ t x - physicalField W s₀ t₀ x‖ ^ 2)
        (nhdsWithin t₀ (Icc 0 T)) (nhds 0))

def PhysicalPairingDeriv : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀ t : ℝ, t < 1 → ∀ φ, IsTestField φ →
      HasDerivAt (fun τ => fieldPairing (physicalField W s₀ τ) φ)
        (∫ x, inner ℝ (sumSecondPartialsAt (physicalField W s₀ t) x
          - advectionAt (physicalField W s₀ t) x
          - gradientAt (physicalPressure q s₀ t) x) (φ x)) t

def PhysicalWeak : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀ t : ℝ, t < 1 → ∀ φ, IsTestField φ →
      HasDerivAt (fun τ => fieldPairing (physicalField W s₀ τ) φ)
        (-gradientPairing (physicalField W s₀ t) φ
          - advectionPairing (physicalField W s₀ t) φ) t

def PhysicalMild : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ),
    IsSimilarityProfile W q C → Continuous (fun s => Rlz.embed (W s)) →
    ∀ s₀ T : ℝ, 0 < T → T < 1 →
      Rlz.F.IsMildOnIcc (fun t => Rlz.embed (physicalField W s₀ t)) 0 T

end Breakdown
