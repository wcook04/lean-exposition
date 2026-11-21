import Breakdown.Frac.ScaledDefs

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown

def ScaledScaleStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ)
    (F : ScaledMildFramework X κ) (u : ℝ → X) (μ T : ℝ), 0 < μ → 0 ≤ T →
    F.IsMildOnIcc u 0 (μ * T) → F.IsMildOnIcc (fun s => F.D μ (u (μ * s))) 0 T

def ScaledOrbitPhysicalStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (w : ℝ → X), Continuous w →
    (∀ s' s, s' ≤ s →
      IntervalIntegrable (fun σ => F.Ks (s - σ) (w σ) (w σ)) volume s' s ∧
        w s = F.S (s - s') (w s') + ∫ σ in s'..s, F.Ks (s - σ) (w σ) (w σ)) →
    ∀ s₀ : ℝ, F.IsMildOn (F.selfSimilar w s₀) 0 1

def ScaledOrbitBoundStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X) (w : ℝ → X) (P : ℝ),
    F.IsOrbit ρ w P → ∃ M : ℝ, ∀ s, ‖w s‖ ≤ M

def ScaledOrbitNormStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P → ∃ c > 0, ∀ s, c ≤ ‖w s‖

def ScaledProfilePieceStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P → ∀ k : ℕ, 0 < k → ∀ n : ℕ,
      (∀ t : Icc (0 : ℝ) (MildFramework.stepLength P k),
        F.profilePiece w P k n t = F.selfSimilar w (n * (P / k)) t) ∧
      F.IsMildOnIcc (extendPiece (F.profilePiece w P k n)) 0 (MildFramework.stepLength P k) ∧
      F.D (Real.exp (-(P / k))) (pieceEnd (MildFramework.stepLength P k) (F.profilePiece w P k n)) =
        extendPiece (F.profilePiece w P k (n + 1)) 0 ∧
      (∀ t : Icc (0 : ℝ) (MildFramework.stepLength P k),
        F.profilePiece w P k (n + k) t = ρ (F.profilePiece w P k n t)) ∧
      ∀ M : ℝ, (∀ s, ‖w s‖ ≤ M) → ‖F.profilePiece w P k n‖ ≤ Real.exp (κ * (P / k)) * M

def ScaledGlueStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ)
    (F : ScaledMildFramework X κ) (μ : ℝ) (u : ℕ → Piece X (1 - μ)), 0 < μ → μ < 1 →
    (∀ n, F.IsMildOnIcc (extendPiece (u n)) 0 (1 - μ)) →
    (∀ n, extendPiece (u (n + 1)) 0 = F.D μ (extendPiece (u n) (1 - μ))) →
    F.IsMildOn (F.gluePieces μ u) 0 1 ∧
      ∀ t ∈ Ico (0 : ℝ) 1, ∃ (n : ℕ) (s : ℝ), s ∈ Ico 0 (1 - μ) ∧ 1 - t = μ ^ n * (1 - s) ∧
        F.D (1 - t) (F.gluePieces μ u t) = F.D (1 - s) (extendPiece (u n) s)

def ScaledStepDataStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P →
    ∀ C' : Submodule ℝ X, Dense (C' : Set X) → ∀ t₀ : ℝ, 0 < t₀ → ∀ κ₀ : ℝ, 0 < κ₀ →
    ∃ (k : ℕ) (θ : ℝ), 0 < k ∧ MildFramework.stepLength P k ≤ t₀ ∧
      Real.exp (-(P / k)) ^ κ < θ ∧ Real.exp (-(P / k)) ^ κ₀ < θ ∧ θ < 1 ∧
      (∀ n, ‖F.stepOp w P k n‖ ≤ 1 / 4) ∧
      ∃ (V : Submodule ℝ X) (J : X →L[ℝ] X)
        (R : lp (fun _ : ℕ => Piece X (MildFramework.stepLength P k)) ∞ →L[ℝ]
          X × lp (fun _ : ℕ => Piece X (MildFramework.stepLength P k)) ∞),
        FiniteDimensional ℝ V ∧ (∀ x, J x ∈ C') ∧ (∀ g, (R g).1 ∈ V) ∧
        ∀ g n, (R g).2 n - F.stepOp w P k n ((R g).2 n) -
          (if n = 0 then F.stepFree P k (J (R g).1)
            else θ⁻¹ • F.stepFree P k (F.stepEnd P k ((R g).2 (n - 1)))) = g n

def ScaledMonodromyStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P → ∀ k : ℕ, 0 < k →
    (∀ n, ‖F.stepOp w P k n‖ ≤ 1 / 4) →
    (∀ n, IsUnit (1 - F.stepOp w P k n)) ∧
    (∀ n, ‖Ring.inverse (1 - F.stepOp w P k n)‖ ≤ 4 / 3) ∧
    (∀ n, stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k) (n + k) =
      (ρ.toContinuousLinearEquiv : X →L[ℝ] X) *
        stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k) n *
        (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X)) ∧
    IsCompactOperator ((ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) *
        iterProd (stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k)) k -
      (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) *
        ((F.D (Real.exp (-(P / k)))).comp (F.G (MildFramework.stepLength P k))) ^ k) ∧
    ‖(ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) *
        ((F.D (Real.exp (-(P / k)))).comp (F.G (MildFramework.stepLength P k))) ^ k‖ ≤
      Real.exp (-(κ * P))

def ScaledTransferHolds : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ),
    0 < κ → ∀ (F : ScaledMildFramework X κ) (ρ : X ≃ₗᵢ[ℝ] X), F.Commutes ρ →
    ∀ (w : ℝ → X) (P : ℝ), F.IsOrbit ρ w P →
    ∀ (C' : Submodule ℝ X), Dense (C' : Set X) → ∀ ε : ℝ, 0 < ε →
    ∃ u : ℝ → X, u 0 ∈ C' ∧ ‖u 0 - w 0‖ < ε ∧ F.IsMildOn u 0 1 ∧
      ∃ C κ' : ℝ, 0 < κ' ∧ ∀ t ∈ Ico (0 : ℝ) 1,
        ‖F.D (1 - t) (u t) - w (-log (1 - t))‖ ≤ C * (1 - t) ^ κ'

end Breakdown
