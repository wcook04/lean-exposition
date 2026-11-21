import Breakdown.Frac.StOperator

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown

def phaseRemainder (ξ z : Space) : ℂ :=
  Complex.exp (((2 * π * inner ℝ z ξ : ℝ) : ℂ) * Complex.I) - 1
    - ((2 * π * inner ℝ z ξ : ℝ) : ℂ) * Complex.I + ((2 * π ^ 2 * (inner ℝ z ξ) ^ 2 : ℝ) : ℂ)

def RemainderTransformStatement : Prop :=
  ∀ φ : SchwartzMap Space Space, ∀ z ξ : Space,
    FourierTransform.fourier (fun x => Freq.complexifyVec (secondOrderRemainder φ x z)) ξ =
      phaseRemainder ξ z • FourierTransform.fourier (fun x => Freq.complexifyVec (φ x)) ξ

def RemainderProductIntegrableStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ φ : SchwartzMap Space Space,
    Integrable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ p.1 p.2‖)
      (volume.prod volume)

end Breakdown
