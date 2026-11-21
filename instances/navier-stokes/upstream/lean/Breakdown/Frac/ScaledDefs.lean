import Breakdown.Transfer.StatementsDefs

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

structure ScaledMildFramework (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (κ : ℝ) where
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
  D_norm : ∀ μ, 0 < μ → ∀ u, ‖D μ u‖ = μ ^ κ * ‖u‖
  D_one : D 1 = ContinuousLinearMap.id ℝ X
  D_mul : ∀ μ ν, 0 < μ → 0 < ν → D (μ * ν) = (D μ).comp (D ν)
  D_cont : ∀ u, ContinuousOn (fun μ => D μ u) (Ioi 0)
  D_G : ∀ μ t, 0 < μ → 0 ≤ t → (D μ).comp (G (μ * t)) = (G t).comp (D μ)
  D_K : ∀ μ τ, 0 < μ → 0 < τ → ∀ u v, μ • D μ (K (μ * τ) u v) = K τ (D μ u) (D μ v)
  compact : ∃ S : Set X, Dense S ∧ ∀ f ∈ S, ∀ τ, 0 < τ → IsCompactOperator (K τ f)

namespace ScaledMildFramework

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {κ : ℝ}
variable (F : ScaledMildFramework X κ)

def toHeatBilinear : HeatBilinear X where
  G := F.G
  G_zero := F.G_zero
  G_add := F.G_add
  G_norm := F.G_norm
  G_cont := F.G_cont
  K := F.K
  K_symm := F.K_symm
  CK := F.CK
  K_bound := F.K_bound
  K_cont := F.K_cont
  K_shift := F.K_shift

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

def selfSimilar (w : ℝ → X) (s₀ t : ℝ) : X := F.D (1 - t)⁻¹ (w (s₀ - Real.log (1 - t)))

def profilePiece (w : ℝ → X) (P : ℝ) (k n : ℕ) : Piece X (MildFramework.stepLength P k) :=
  toPiece (MildFramework.stepLength P k) (F.selfSimilar w (n * (P / k)))

def stepOp (w : ℝ → X) (P : ℝ) (k n : ℕ) :
    Piece X (MildFramework.stepLength P k) →L[ℝ] Piece X (MildFramework.stepLength P k) :=
  (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n)

def stepFree (P : ℝ) (k : ℕ) : X →L[ℝ] Piece X (MildFramework.stepLength P k) :=
  F.toHeatBilinear.pieceFree (MildFramework.stepLength P k)

def stepEnd (P : ℝ) (k : ℕ) : Piece X (MildFramework.stepLength P k) →L[ℝ] X :=
  (F.D (Real.exp (-(P / k)))).comp (pieceEnd (MildFramework.stepLength P k))

theorem isMildOn_iff (u : ℝ → X) (a b : ℝ) :
    F.IsMildOn u a b ↔ F.toHeatBilinear.IsMildOn u a b := Iff.rfl

theorem isMildOnIcc_iff (u : ℝ → X) (a b : ℝ) :
    F.IsMildOnIcc u a b ↔ F.toHeatBilinear.IsMildOnIcc u a b := Iff.rfl

theorem hasCompactKernel : F.toHeatBilinear.HasCompactKernel := F.compact

def gluePieces (μ : ℝ) (u : ℕ → Piece X (1 - μ)) (t : ℝ) : X :=
  F.D (μ ^ MildFramework.stepIndex μ t)⁻¹
    (extendPiece (u (MildFramework.stepIndex μ t))
      ((t - (1 - μ ^ MildFramework.stepIndex μ t)) / μ ^ MildFramework.stepIndex μ t))

end ScaledMildFramework

end Breakdown
