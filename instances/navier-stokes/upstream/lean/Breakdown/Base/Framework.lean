import Breakdown.Defs

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

structure MildFramework (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] where
  G : ℝ → X →L[ℝ] X
  G_zero : G 0 = ContinuousLinearMap.id ℝ X
  G_add : ∀ s t, 0 ≤ s → 0 ≤ t → G (s + t) = (G s).comp (G t)
  G_norm : ∀ t, 0 ≤ t → ‖G t‖ ≤ 1
  G_cont : ∀ x, ContinuousOn (fun t => G t x) (Ici 0)
  K : ℝ → X →L[ℝ] X →L[ℝ] X
  K_symm : ∀ τ u v, K τ u v = K τ v u
  CK : ℝ
  K_bound : ∀ τ, 0 < τ → τ ≤ 1 → ‖K τ‖ ≤ CK * τ ^ (-(3 / 4 : ℝ))
  K_cont : ∀ u v, ContinuousOn (fun τ => K τ u v) (Ioi 0)
  K_shift : ∀ s τ, 0 ≤ s → 0 < τ → ∀ u v, G s (K τ u v) = K (s + τ) u v
  D : ℝ → X →L[ℝ] X
  D_norm : ∀ μ, 0 < μ → ∀ u, ‖D μ u‖ = μ ^ (1 / 4 : ℝ) * ‖u‖
  D_one : D 1 = ContinuousLinearMap.id ℝ X
  D_mul : ∀ μ ν, 0 < μ → 0 < ν → D (μ * ν) = (D μ).comp (D ν)
  D_cont : ∀ u, ContinuousOn (fun μ => D μ u) (Ioi 0)
  D_G : ∀ μ t, 0 < μ → 0 ≤ t → (D μ).comp (G (μ * t)) = (G t).comp (D μ)
  D_K : ∀ μ τ, 0 < μ → 0 < τ → ∀ u v, μ • D μ (K (μ * τ) u v) = K τ (D μ u) (D μ v)
  compact : ∃ S : Set X, Dense S ∧ ∀ f ∈ S, ∀ τ, 0 < τ → IsCompactOperator (K τ f)

namespace MildFramework

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable (F : MildFramework X)

def IsMildOn (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Ico a b) ∧
    ∀ t ∈ Ico a b, IntervalIntegrable (fun s => F.K (t - s) (u s) (u s)) volume a t ∧
      u t = F.G (t - a) (u a) + ∫ s in a..t, F.K (t - s) (u s) (u s)

def IsMildOnIcc (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => F.K (t - s) (u s) (u s)) volume a t ∧
      u t = F.G (t - a) (u a) + ∫ s in a..t, F.K (t - s) (u s) (u s)

def S (τ : ℝ) : X →L[ℝ] X := (F.D (exp (-τ))).comp (F.G (1 - exp (-τ)))

def Ks (τ : ℝ) (u v : X) : X := F.D (exp (-τ)) (F.K (1 - exp (-τ)) u v)

structure Commutes (ρ : X ≃ₗᵢ[ℝ] X) : Prop where
  comm_G : ∀ t x, ρ (F.G t x) = F.G t (ρ x)
  comm_K : ∀ τ u v, ρ (F.K τ u v) = F.K τ (ρ u) (ρ v)
  comm_D : ∀ μ x, ρ (F.D μ x) = F.D μ (ρ x)

structure IsOrbit (ρ : X ≃ₗᵢ[ℝ] X) (w : ℝ → X) (P : ℝ) : Prop where
  cont : Continuous w
  nonzero : ∃ s, w s ≠ 0
  pos : 0 < P
  periodic : ∀ s, w (s + P) = ρ (w s)
  flow : ∀ s' s, s' ≤ s →
    IntervalIntegrable (fun σ => F.Ks (s - σ) (w σ) (w σ)) volume s' s ∧
      w s = F.S (s - s') (w s') + ∫ σ in s'..s, F.Ks (s - σ) (w σ) (w σ)

end MildFramework

def TransferHolds : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (F : MildFramework X) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P →
    ∀ (C' : Submodule ℝ X), Dense (C' : Set X) → ∀ ε : ℝ, 0 < ε →
    ∃ u : ℝ → X, u 0 ∈ C' ∧ ‖u 0 - w 0‖ < ε ∧ F.IsMildOn u 0 1 ∧
      ∃ C κ : ℝ, 0 < κ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
        ‖F.D (1 - t) (u t) - w (-log (1 - t))‖ ≤ C * (1 - t) ^ κ

def DichotomyHolds : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T₀ C : X →L[ℝ] X) (b α β : ℝ), 0 ≤ b → b ≤ α → α < β → ‖T₀‖ ≤ b → IsCompactOperator C →
    ∃ (r₁ r₂ K : ℝ) (Pu : X →L[ℝ] X),
      α < r₁ ∧ r₁ < r₂ ∧ r₂ < β ∧ 0 < K ∧
      Pu * Pu = Pu ∧ Pu * (T₀ + C) = (T₀ + C) * Pu ∧
      FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X)) ∧
      (∀ n : ℕ, ‖(T₀ + C) ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) ∧
      (∀ n : ℕ, ∀ x, ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖((T₀ + C) ^ n) (Pu x)‖) ∧
      (∀ y ∈ LinearMap.range (Pu : X →ₗ[ℝ] X),
        ∃ x ∈ LinearMap.range (Pu : X →ₗ[ℝ] X), (T₀ + C) x = y)

end Breakdown
