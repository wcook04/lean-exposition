import Breakdown.Base.Framework

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def DilateJointContinuous : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (F : MildFramework X), ContinuousOn (fun p : ℝ × X => F.D p.1 p.2) (Ioi 0 ×ˢ univ)

def KernelDilate : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (F : MildFramework X) (a b τ : ℝ) (x : X), 0 < a → 0 < b → 0 < τ →
    F.D a (F.K (b * τ) (F.D b⁻¹ x) (F.D b⁻¹ x)) = b⁻¹ • F.D (a * b⁻¹) (F.K τ x x)

def ExpChangeOfVariables : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (s₀ s : ℝ), s₀ < s →
    IntervalIntegrable g volume 0 (1 - exp (-(s - s₀))) →
      IntervalIntegrable (fun σ => exp (-(σ - s₀)) • g (1 - exp (-(σ - s₀)))) volume s₀ s ∧
      ∫ σ in s₀..s, exp (-(σ - s₀)) • g (1 - exp (-(σ - s₀)))
        = ∫ r in (0 : ℝ)..(1 - exp (-(s - s₀))), g r

def FlowOfMild : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (F : MildFramework X) (w u : ℝ → X) (s₀ s : ℝ), s₀ < s →
    F.IsMildOnIcc u 0 (1 - exp (-(s - s₀))) →
    (∀ r ∈ Icc 0 (1 - exp (-(s - s₀))), u r = F.D (1 - r)⁻¹ (w (s₀ - Real.log (1 - r)))) →
      IntervalIntegrable (fun σ => F.Ks (s - σ) (w σ) (w σ)) volume s₀ s ∧
      w s = F.S (s - s₀) (w s₀) + ∫ σ in s₀..s, F.Ks (s - σ) (w σ) (w σ)

end Breakdown
