import Mathlib

open Matrix

noncomputable section

namespace Breakdown.Held

def testSet {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ) : Set (Fin k → ℝ) :=
  {p | (∀ j ∈ Ja, |p j| ≤ rad j) ∧ ∑ j ∈ Jaᶜ, (s j * p j) ^ 2 ≤ εs ^ 2}

def TestSetZeroStatement : Prop :=
  ∀ {k : ℕ} (Ja : Finset (Fin k)) (rad s : Fin k → ℝ) (εs : ℝ) (U : Matrix (Fin k) (Fin k) ℝ)
    (Φ : (Fin k → ℝ) → Fin k → ℝ),
    (∀ j ∈ Ja, 0 ≤ rad j) → 0 ≤ εs → (∀ j, s j ≠ 0) → IsUnit U.det →
    ContinuousOn Φ (testSet Ja rad s εs) →
    (∀ p ∈ testSet Ja rad s εs, ∀ j ∈ Ja, |(Uᵀ *ᵥ Φ p) j - s j * p j| ≤ |s j| * rad j) →
    (∀ p ∈ testSet Ja rad s εs, ∑ j ∈ Jaᶜ, ((Uᵀ *ᵥ Φ p) j - s j * p j) ^ 2 ≤ εs ^ 2) →
    ∃ p ∈ testSet Ja rad s εs, Φ p = 0

def ConvexCompactFixedPointStatement : Prop :=
  ∀ {k : ℕ} (K : Set (Fin k → ℝ)), Convex ℝ K → IsCompact K → K.Nonempty →
    ∀ f : (Fin k → ℝ) → Fin k → ℝ, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

def AdjointEnclosureStatement : Prop :=
  ∀ {Y V : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (E : V → ℝ) (L : V →ₗ[ℝ] Y) (Q : V → Y) (b : Fin k → Y) (pin : V →ₗ[ℝ] Fin k → ℝ)
    (ζ : Y) (c : Fin k → ℝ) (u₀ : Fin k → ℝ) (δ l μ r : ℝ),
    (∀ v, 0 ≤ E v) → 0 < μ → 0 ≤ δ → 0 ≤ l →
    (∀ v, |inner ℝ (L v) ζ - ∑ j, c j * pin v j| ≤ δ * Real.sqrt (E v)) →
    ∀ (u : V) (κ : Fin k → ℝ) (R : Y), |inner ℝ (Q u) ζ| ≤ l * E u →
    L u + ∑ j, κ j • b j + Q u = -R →
    Real.sqrt (E u + μ ^ 2 * ∑ j, κ j ^ 2) ≤ r →
    |∑ j, u₀ j * κ j + inner ℝ R ζ + ∑ j, c j * pin u j| ≤
      l * r ^ 2 + r * Real.sqrt (δ ^ 2 + (∑ j, (inner ℝ (b j) ζ - u₀ j) ^ 2) / μ ^ 2)

end Breakdown.Held
