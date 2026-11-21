import Mathlib
import Breakdown.CertCell.StatementDefs

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Coupling

def crossForm {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x u : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ u)).re

def signDiag {d : ℕ} (s : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun a => (s a : ℂ))

def sourceForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {G : Type*} [Fintype G]
    (r : G → ℕ) (Λ : E →L[ℂ] E) (Ysum : E) (a : ∀ j, Fin (r j) → ℂ) (R : ∀ j, E →ₗ[ℂ] (Fin (r j) → ℂ))
    (D : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℂ) (σ : E) : ℝ :=
  (inner ℂ (Λ σ) σ).re + 2 * (inner ℂ Ysum σ).re + ∑ j, inverseWeightedSq (D j) (a j + R j σ)

def sourceBracket {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {m : ℕ}
    (share : ℝ) (Λ : E →L[ℂ] E) (Y : E) (port : E) (a : Fin m → ℂ) (R : E →ₗ[ℂ] (Fin m → ℂ))
    (D : Matrix (Fin m) (Fin m) ℂ) (σ : E) : ℝ :=
  share * (inner ℂ (Λ σ) σ).re + 2 * (inner ℂ (Y + port) σ).re + inverseWeightedSq D (a + R σ)

def SourceCopiesHolds : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {G : Type} [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (r : G → ℕ) (Λ : E →L[ℂ] E) (Y : G → E) (a : ∀ j, Fin (r j) → ℂ)
    (R : ∀ j, E →ₗ[ℂ] (Fin (r j) → ℂ)) (D : ∀ j, Matrix (Fin (r j)) (Fin (r j)) ℂ)
    (share : G → ℝ) (port : G → V →ₗ[ℂ] E),
    (∀ σ, 0 ≤ (inner ℂ (Λ σ) σ).re) → (∀ j, 0 < share j) → ∑ j, share j ≤ 1 → ∑ j, port j = 0 →
    ∀ (η : V) (lower : G → ℝ), (∀ j σ', lower j ≤ sourceBracket (share j) Λ (Y j) (port j η) (a j) (R j) (D j) σ') →
      ∀ σ, ∑ j, lower j ≤ sourceForm r Λ (∑ j, Y j) a R D σ

def PortSplitHolds : Prop :=
  ∀ {n : Type} [Fintype n] (T Y₁ Y₂ : Matrix n n ℂ),
    (T + Y₁ + Y₂).PosSemidef →
    ∀ u w : n → ℂ, -quadForm Y₁ u - quadForm Y₂ u + 2 * crossForm (T + Y₁ + Y₂) w u
        - quadForm (T + Y₁ + Y₂) w ≤ quadForm T u

def SumSplitHolds : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {G : Type} [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (share : G → ℝ) (port : G → V →ₗ[ℂ] E),
    (∀ j, 0 < share j) → ∑ j, share j ≤ 1 → ∑ j, port j = 0 →
    ∀ (Y : G → E) (η : V), -∑ j, ‖Y j - port j η‖ ^ 2 / share j ≤ -‖∑ j, Y j‖ ^ 2

def RowSplitHolds : Prop :=
  ∀ {n : ℕ} {G : Type} [Fintype G] (m : G → ℕ) (embed : ∀ j, Matrix (Fin n) (Fin (m j)) ℂ)
    (D₁ D₂ : Matrix (Fin n) (Fin n) ℂ) (M : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ),
    D₁.PosDef → (∀ j, (M j).PosDef) → (D₂ - D₁ - ∑ j, embed j * (M j)⁻¹ * (embed j)ᴴ).PosSemidef →
    ∀ (a : Fin n → ℂ) (w p : ∀ j, Fin (m j) → ℂ),
      inverseWeightedSq D₂ (a + ∑ j, embed j *ᵥ p j) - ∑ j, quadForm (M j) (w j - p j)
        ≤ inverseWeightedSq D₁ (a + ∑ j, embed j *ᵥ w j)

def SharePortSumHolds : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module ℝ V] {G : Type} [Fintype G] (share : G → ℝ) (base : G → V),
    ∑ j, share j = 1 → ∑ j, (share j • ∑ j', base j' - base j) = 0

def PlanePairCancelHolds : Prop :=
  ∀ {I : Type} [Fintype I] {d e : ℕ} (partner : I → I) (s : Fin d → ℝ)
    (g : I → Fin d → ℂ) (B : I → Matrix (Fin d) (Fin d) ℂ) (Ξ : I → Matrix (Fin d) (Fin e) ℂ),
    (∀ i, partner (partner i) = i) → (∀ a, s a ^ 2 = 1) →
    (∀ i, g (partner i) = signDiag s *ᵥ g i) →
    (∀ i, B (partner i) = -(signDiag s * B i * signDiag s)) →
    (∑ i, star (g i) ⬝ᵥ (B i *ᵥ g i) = 0) ∧
      ∀ χ : Fin e → ℂ, ∑ i, star ((Ξ i - signDiag s * Ξ (partner i)) *ᵥ χ) ⬝ᵥ g i = 0

def InverseFormCreditHolds : Prop :=
  ∀ {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (t : Fin N → ℂ) (A : ℝ),
    G.PosDef → 0 ≤ A → (∀ c : Fin N → ℂ, ‖star c ⬝ᵥ t‖ ^ 2 ≤ A * realQuadForm G c) →
    realQuadForm G⁻¹ t ≤ A

def InverseFormFactorHolds : Prop :=
  ∀ {N p : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (L : Matrix (Fin p) (Fin N) ℝ) (ε : ℝ),
    G.PosDef → 0 ≤ ε → ((1 + ε) • (1 : Matrix (Fin p) (Fin p) ℝ) - L * G * Lᵀ).PosSemidef →
    ∀ x : Fin N → ℂ, realQuadForm (Lᵀ * L) x / (1 + ε) ≤ realQuadForm G⁻¹ x

def PairingSquareRemainderHolds : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {G : Type} [Fintype G]
    (X : G → E) (ζ : G → ℂ) (s : E) (γ : ℝ), 0 < γ →
    -γ * ‖s‖ ^ 2 - (∑ g, ∑ g', (starRingEnd ℂ) (ζ g) * ζ g' * inner ℂ (X g) (X g')).re / γ
      ≤ 2 * (inner ℂ (∑ g, ζ g • X g) s).re

def GlobalLeafHolds : Prop :=
  ∀ {k : ℕ} (tw cw : ℝ) (ℓ h κ ζ : Fin k → ℝ), 0 < tw →
    ∑ i, (κ i * ℓ i + 2 * ζ i * h i) - ∑ i, ζ i ^ 2 / tw - cw * ∑ i, κ i ^ 2
      ≤ ∑ i, κ i * ℓ i + tw * ∑ i, h i ^ 2 - cw * ∑ i, κ i ^ 2

def SingleFactorBoundHolds : Prop :=
  ∀ {N : ℕ} (H L : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → ℂ) (ε : ℝ), H.IsHermitian → 0 ≤ ε → ε < 1 →
    (L * H * Lᴴ - ((1 - ε : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef →
    ∀ σ : Fin N → ℂ, -(star (L *ᵥ Z) ⬝ᵥ (L *ᵥ Z)).re / (1 - ε) ≤ quadForm H σ + 2 * (star σ ⬝ᵥ Z).re

end Coupling

end CertCell

end Breakdown
