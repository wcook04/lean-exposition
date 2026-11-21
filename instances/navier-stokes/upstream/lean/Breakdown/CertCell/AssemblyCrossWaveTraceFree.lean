import Breakdown.CertCell.BridgeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

def classCharge (κ σc γc ℓ : ℝ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  σc * cnormSq (curlOfGrad g) + κ / 2 * γc * (ℓ * cnormSq g + cnormSq a / ℓ)

def CrossWaveTraceFreeBoundHolds : Prop :=
  ∀ (m : ℕ) (A A' B : Finset ℤ) (x x' : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ))
    (wg : ℤ → Fin 3 × Fin 3 → ℂ) (wh : ℤ → Fin 3 × Fin 3 × Fin 3 → ℂ) (σc γc ℓ βc : ℝ),
    1 ≤ m → 0 ≤ σc → 0 ≤ γc → 0 < ℓ → 0 < βc →
    (∀ θ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j : Fin 3,
        (∑ n ∈ B, azimuthPhase m n θ * ((wg n (i, j) + wg n (j, i)) / 2)) * u j) ≤ σc ^ 2 * cnormSq u) →
    (∀ θ (u : Fin 3 → ℂ), cnormSq (fun j => ∑ l : Fin 3,
        (∑ n ∈ B, azimuthPhase m n θ * curlGradOfSecondDeriv (wh n) (j, l)) * u l) ≤ γc ^ 2 * cnormSq u) →
    (∀ θ, ∑ j : Fin 3, ∑ n ∈ B, azimuthPhase m n θ * curlGradOfSecondDeriv (wh n) (j, j) = 0) →
    2 * ‖∑ n ∈ B, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
        stretchTriple (wg n) (wh n) (x n₁).1 (x n₁).2 (star (x' n₂).1) (star (x' n₂).2) else 0‖
      ≤ βc * ∑ n₁ ∈ A, classCharge (Real.sqrt (7 / 2)) σc γc ℓ (x n₁).1 (x n₁).2
        + βc⁻¹ * ∑ n₂ ∈ A', classCharge (Real.sqrt (7 / 2)) σc γc ℓ (x' n₂).1 (x' n₂).2

end Bridge

end CertCell

end Breakdown
