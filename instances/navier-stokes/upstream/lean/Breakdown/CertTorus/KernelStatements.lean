import Breakdown.CertTorus.Defs

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

def HeatKernelBounds : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ x : Space,
    heatKernel τ x ≤ C / (‖x‖ + Real.sqrt τ) ^ 3 ∧
    (∀ k : Fin 3, |x k / (2 * τ) * heatKernel τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4) ∧
    ∀ i j k : Fin 3, |heatKernelThird i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 6

def HeatKernelPartials : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ x : Space,
    HasFDerivAt (heatKernel τ)
      (∑ k : Fin 3, (-(x k / (2 * τ)) * heatKernel τ x) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x ∧
    ∀ i j k : Fin 3,
      fderiv ℝ (fun z : Space =>
        (z j * z k / (4 * τ ^ 2) - (if j = k then 1 / (2 * τ) else 0)) * heatKernel τ z) x (unitVector i) =
        heatKernelThird i j k τ x

def LerayKernelBound : Prop :=
  ∃ C : ℝ, ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
    |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4

def LerayKernelJointContinuous : Prop :=
  ∀ i j k : Fin 3, ContinuousOn (fun p : ℝ × Space => lerayKernel i j k p.1 p.2) (Ioi 0 ×ˢ univ)

def LerayKernelMeasurable : Prop :=
  ∀ i j k : Fin 3, Measurable (fun p : ℝ × Space => lerayKernel i j k p.1 p.2)

def LerayKernelC1 : Prop :=
  ∀ i j k : Fin 3, ∀ τ : ℝ, 0 < τ → ContDiff ℝ 1 (lerayKernel i j k τ)

def LerayKernelDivFree : Prop :=
  ∀ j k : Fin 3, ∀ τ : ℝ, 0 < τ → ∀ x : Space,
    ∑ i : Fin 3, fderiv ℝ (lerayKernel i j k τ) x (unitVector i) = 0

def LerayKernelOdd : Prop :=
  ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, lerayKernel i j k τ (-x) = -lerayKernel i j k τ x

def KernelScaling : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ τ : ℝ, 0 < τ → ∀ x : Space,
    heatKernel (μ * τ) (Real.sqrt μ • x) = (μ * Real.sqrt μ)⁻¹ * heatKernel τ x ∧
    ∀ i j k : Fin 3, lerayKernel i j k (μ * τ) (Real.sqrt μ • x) = (μ ^ 2)⁻¹ * lerayKernel i j k τ x

def KernelL1Bound : Prop :=
  ∃ C : ℝ, ∀ i j k : Fin 3, ∀ τ : ℝ, 0 < τ →
    Integrable (lerayKernel i j k τ) ∧ ∫ x, |lerayKernel i j k τ x| ≤ C * τ ^ (-(1 / 2 : ℝ))

def KernelConvSup : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ F : Space → Fin 3 → Fin 3 → ℝ, Measurable F → ∀ A : ℝ,
    (∀ z, ‖F z‖ ≤ A) → ∀ y, ‖kernelConv τ F y‖ ≤ C * τ ^ (-(1 / 2 : ℝ)) * A

end Breakdown.FarField
