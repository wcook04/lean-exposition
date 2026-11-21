import Breakdown.Transfer.StatementsDefs

open scoped ENNReal

noncomputable section

namespace Breakdown

def DiscreteDichotomyStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (M Pu : E →L[ℝ] E) (K r₁ r₂ Θ : ℝ), Pu * Pu = Pu → Pu * M = M * Pu → 0 ≤ r₁ → r₁ < Θ → Θ < r₂ →
    (∀ n : ℕ, ‖M ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) →
    (∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖) →
    (∀ y ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), ∃ x ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), M x = y) →
    ∃ (U : lp (fun _ : ℕ => E) ∞ →L[ℝ] E) (K' : ℝ), (∀ c, Pu (U c) = U c) ∧
      ∀ (c : lp (fun _ : ℕ => E) ∞) (x₀ : E), Pu x₀ = U c →
        ∀ n, ‖orbitSeq M Θ (fun m => c m) x₀ n‖ ≤ K' * (‖x₀‖ + ‖c‖)

def PeriodicInverseStatement : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (k : ℕ) (ρ : X ≃ₗᵢ[ℝ] X) (A : ℕ → Y →L[ℝ] Y) (Γ : X →L[ℝ] Y) (Ev : Y →L[ℝ] X)
    (J Pu : X →L[ℝ] X) (K r₁ r₂ θ Cinv : ℝ),
    0 < k → 0 < θ → (∀ n, IsUnit (1 - A n)) → (∀ n, ‖Ring.inverse (1 - A n)‖ ≤ Cinv) →
    (∀ n, stepMap A Γ Ev (n + k) =
      (ρ.toContinuousLinearEquiv : X →L[ℝ] X) * stepMap A Γ Ev n *
        (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X)) →
    Pu * Pu = Pu →
    Pu * ((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd (stepMap A Γ Ev) k) =
      ((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd (stepMap A Γ Ev) k) * Pu →
    0 ≤ r₁ → r₁ < θ ^ k → θ ^ k < r₂ →
    (∀ n : ℕ, ‖((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd (stepMap A Γ Ev) k) ^ n *
      (1 - Pu)‖ ≤ K * r₁ ^ n) →
    (∀ (n : ℕ) (x : X), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n *
      ‖(((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd (stepMap A Γ Ev) k) ^ n) (Pu x)‖) →
    (∀ y ∈ LinearMap.range (Pu : X →ₗ[ℝ] X), ∃ x ∈ LinearMap.range (Pu : X →ₗ[ℝ] X),
      ((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd (stepMap A Γ Ev) k) x = y) →
    Pu * J = Pu →
    ∃ R : lp (fun _ : ℕ => Y) ∞ →L[ℝ] X × lp (fun _ : ℕ => Y) ∞,
      (∀ g, (R g).1 ∈ LinearMap.range (Pu : X →ₗ[ℝ] X)) ∧
      ∀ g n, (R g).2 n - A n ((R g).2 n) -
        (if n = 0 then Γ (J (R g).1) else θ⁻¹ • Γ (Ev ((R g).2 (n - 1)))) = g n

def ContractionStatement : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : ℕ → Y →L[ℝ] Y) (Γ : X →L[ℝ] Y) (Ev : Y →L[ℝ] X) (J : X →L[ℝ] X)
    (N : Y →L[ℝ] Y →L[ℝ] Y) (θ : ℝ) (R : lp (fun _ : ℕ => Y) ∞ →L[ℝ] X × lp (fun _ : ℕ => Y) ∞),
    0 < θ → θ ≤ 1 →
    (∀ g n, (R g).2 n - A n ((R g).2 n) -
      (if n = 0 then Γ (J (R g).1) else θ⁻¹ • Γ (Ev ((R g).2 (n - 1)))) = g n) →
    ∃ ϱ₀ > 0, ∃ C₁ : ℝ, ∀ ξ : X, ‖ξ‖ ≤ ϱ₀ → ∃ (e : X) (z : lp (fun _ : ℕ => Y) ∞),
      ‖e‖ ≤ C₁ * ‖ξ‖ ∧ ∀ n, z n - A n (z n) -
        (if n = 0 then Γ (J e + ξ) else θ⁻¹ • Γ (Ev (z (n - 1)))) = θ ^ n • N (z n) (z n)

def SectionStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (Pu : X →L[ℝ] X) (C' : Submodule ℝ X), Pu * Pu = Pu →
    FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X)) → Dense (C' : Set X) →
    ∃ J : X →L[ℝ] X, Pu * J = Pu ∧ ∀ x, J x ∈ C'

end Breakdown
