import Breakdown.Weak.StatementsSlice

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

def SliceMeasurable : Prop :=
  PairingVelocity →
  ∀ (x : ℝ → X) (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (M : ℝ),
    IsSliceCurve x W G M → AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume →
    AEStronglyMeasurable x volume

def ScaledTestField : Prop :=
  ∀ (α : ℝ → ℝ) (s₀ : ℝ) (φ : Space → Space), ContDiff ℝ ∞ α → HasCompactSupport α →
    IsTestField φ → IsSpaceTimeTestField (scaledTest α s₀ φ)

def SliceIntegrand : Prop :=
  PairingVelocity → AdvectionByParts →
  ∀ (w : X) (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (C : ℝ), IsSlice f g C →
    (velocity w : Space → Space) =ᵐ[volume] f →
    (∀ j, (partialX j w : Space → Space) =ᵐ[volume] gradComponent g j) →
    ∀ (α : ℝ → ℝ) (s₀ σ : ℝ) (φ : Space → Space), ContDiff ℝ ∞ α → HasCompactSupport α →
      IsTestField φ →
      ∫ y, weakSimilarityIntegrand (fun _ => f) (fun _ => g) (scaledTest α s₀ φ) (σ, y) =
        similarityRate (fun _ => w) α s₀ φ σ

def SimilarityIdentity : Prop :=
  SliceIntegrand → ScaledTestField → PairingVelocity → AdvectionByParts →
  ∀ (x : ℝ → X) (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (M C : ℝ),
    IsSliceCurve x W G M → (∀ s, IsSlice (W s) (G s) C) →
    (∀ φ, IsSpaceTimeTestField φ →
      Integrable (weakSimilarityIntegrand W G φ) ∧ ∫ z, weakSimilarityIntegrand W G φ z = 0) →
    ∀ (α : ℝ → ℝ) (s₀ : ℝ) (φ : Space → Space), ContDiff ℝ ∞ α → HasCompactSupport α →
      IsTestField φ →
      Integrable (similarityRate x α s₀ φ) ∧ ∫ σ, similarityRate x α s₀ φ σ = 0

def PhysicalIdentity : Prop :=
  PairingDilate → TrilinearDilate →
  ∀ (x : ℝ → X) (M s₀ : ℝ), (∀ σ, ‖x σ‖ ≤ M) → AEStronglyMeasurable x volume →
    (∀ (α : ℝ → ℝ) (φ : Space → Space), ContDiff ℝ ∞ α → HasCompactSupport α → IsTestField φ →
      Integrable (similarityRate x α s₀ φ) ∧ ∫ σ, similarityRate x α s₀ φ σ = 0) →
    IsTensorWeak (physicalCurve x s₀) (-1) 1

def ConstOfWeakDeriv : Prop :=
  ∀ (a b : ℝ → ℝ) (l r : ℝ), l < r → IntegrableOn a (Ioo l r) → IntegrableOn b (Ioo l r) →
    (∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo l r →
      ∫ t, deriv θ t * a t = ∫ t, θ t * b t) →
    ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo l r)), a t = c - ∫ τ in l..t, b τ

def GoodTimes : Prop :=
  ConstOfWeakDeriv →
  ∀ (y : ℝ → X) (l r M : ℝ), l < r → (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) → IsTensorWeak y l r →
    ∃ E, IsGoodSet y l r E

def BilinIntegrable : Prop :=
  ∀ (y : ℝ → X) (l r M : ℝ), (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) →
    ∀ t₀ t ε : ℝ, l < t₀ → t₀ ≤ t → t < r → 0 ≤ ε →
      IntervalIntegrable (fun τ => bilinX (t - τ + ε) (y τ) (y τ)) volume t₀ t

def VarConstInner : Prop :=
  BilinIntegrable →
  ∀ (y : ℝ → X) (l r M : ℝ) (E : Set ℝ), (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) → IsGoodSet y l r E →
    ∀ t₀ ∈ E, ∀ t ∈ E, t₀ ≤ t → ∀ ε : ℝ, 0 < ε → ∀ ψ : X,
      inner ℝ (y t) (heatX ε ψ) = inner ℝ (y t₀) (heatX (t - t₀ + ε) ψ) +
        ∫ τ in t₀..t, inner ℝ (bilinX (t - τ + ε) (y τ) (y τ)) ψ

def VarConstGood : Prop :=
  BilinIntegrable → VarConstInner →
  ∀ (y : ℝ → X) (l r M : ℝ) (E : Set ℝ), (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) → IsGoodSet y l r E →
    ∀ t₀ ∈ E, ∀ t ∈ E, t₀ ≤ t → varConst y t₀ t = y t

def ContinuousVarConst : Prop :=
  BilinIntegrable →
  ∀ (y : ℝ → X) (l r M : ℝ), (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) →
    ∀ t₀ ∈ Ioo l r, ContinuousOn (varConst y t₀) (Ico t₀ r)

def MildFromGood : Prop :=
  BilinIntegrable →
  ∀ (y : ℝ → X) (l r M t₀ : ℝ) (E : Set ℝ), (∀ t ∈ Ioo l r, ‖y t‖ ≤ M) →
    AEStronglyMeasurable y (volume.restrict (Ioo l r)) → E ⊆ Ioo l r →
    volume (Ioo l r \ E) = 0 → t₀ ∈ Ioo l r → ContinuousOn (varConst y t₀) (Ico t₀ r) →
    (∀ t ∈ E, t₀ ≤ t → varConst y t₀ t = y t) →
    ∀ a b, t₀ ≤ a → a < b → b < r → IsMildX (varConst y t₀) a b

end Breakdown.WeakProfile
