import Breakdown.Torus.Mild

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

def KernelSharpBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖kernel τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))

def MildUniqueness : Prop :=
  ∀ (u v : ℝ → V) (a b : ℝ), IsMildOn u a b → IsMildOnIcc v a b → u a = v a → EqOn u v (Ico a b)

def TrilinearBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (u v : V) (φ : Lattice → Coef),
    Summable (fun k => ‖φ k‖) → Summable (fun k => weight k * ‖φ k‖ ^ 2) →
    ‖∑' k, inner ℂ (φ k) (advCoef u v k)‖ ≤
      C * ‖u‖ * ‖v‖ * (∑' k, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) * (∑' k, weight k * ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ)

end Breakdown.Periodic
