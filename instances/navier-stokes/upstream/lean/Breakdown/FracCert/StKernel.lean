import Breakdown.Defs

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown.FracCert

def IsRingCutoff (θ : Space → ℝ) : Prop :=
  ContDiff ℝ ∞ θ ∧ (∀ ξ, 0 ≤ θ ξ ∧ θ ξ ≤ 1) ∧
    (∀ ξ, θ ξ ≠ 0 → 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2) ∧
    ∀ ξ : Space, ξ ≠ 0 → HasSum (fun l : ℤ => θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ)) 1

def RingCutoffStatement : Prop := ∃ θ : Space → ℝ, IsRingCutoff θ

def DyadicSumStatement : Prop :=
  ∀ a N : ℝ, 0 < a → a < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r →
    Summable (fun l : ℤ => (2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N)) ∧
    ∑' l : ℤ, (2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N) ≤ C * r ^ (-a)

def PieceKernelStatement : Prop :=
  ∀ N j : ℕ, ∃ C : ℝ, ∀ (m : Space → ℂ) (B : ℝ), ContDiff ℝ ∞ m →
    (∀ ξ, m ξ ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4) →
    (∀ i ≤ N + j + 4, ∀ ξ, ‖iteratedFDeriv ℝ i m ξ‖ ≤ B) →
    ContDiff ℝ ∞ (FourierTransform.fourierInv m) ∧
    ∀ x, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (FourierTransform.fourierInv m) x‖ ≤ C * B

def projDivSymbol (α t : ℝ) (i j k : Fin 3) (ξ : Space) : ℂ :=
  ((2 * π * ξ k : ℝ) : ℂ) * Complex.I *
    (((if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2 : ℝ) : ℂ) *
    ((Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α))) : ℝ) : ℂ)

def projDivKernel (α t : ℝ) (i j k : Fin 3) (x : Space) : ℂ :=
  FourierTransform.fourierInv (projDivSymbol α t i j k) x

def KernelDecayStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∀ i j k : Fin 3,
    (∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (projDivKernel α t i j k)) ∧
    ∀ n : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x : Space,
      ‖iteratedFDeriv ℝ n (projDivKernel α t i j k) x‖ ≤
        C * (t ^ (1 / (2 * α)) + ‖x‖) ^ (-(4 + n : ℝ))

def KernelScalingStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∀ i j k : Fin 3, ∀ t : ℝ, 0 < t →
    (∀ x : Space, projDivKernel α t i j k x =
      ((t ^ (-(2 / α)) : ℝ) : ℂ) * projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x)) ∧
    (∀ x : Space, (projDivKernel α t i j k x).im = 0) ∧
    Integrable (projDivKernel α t i j k) ∧
    (∫ x, ‖projDivKernel α t i j k x‖) = t ^ (-(1 / (2 * α))) * ∫ x, ‖projDivKernel α 1 i j k x‖ ∧
    MemLp (projDivKernel α t i j k) (3 / 2) ∧
    (eLpNorm (projDivKernel α t i j k) (3 / 2) volume).toReal =
      t ^ (-(1 / α)) * (eLpNorm (projDivKernel α 1 i j k) (3 / 2) volume).toReal

def IsHomogeneousSymbol (σ : Space → ℂ) (d : ℝ) : Prop :=
  ContDiffOn ℝ ∞ σ {ξ | ξ ≠ 0} ∧
    ∀ c : ℝ, 0 < c → ∀ ξ : Space, ξ ≠ 0 → σ (c • ξ) = ((c ^ d : ℝ) : ℂ) * σ ξ

def IsWeightedSmooth (f : Space → ℂ) (β : ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ i : ℕ, ∃ C : ℝ, ∀ y : Space, (1 + ‖y‖) ^ (β + i) * ‖iteratedFDeriv ℝ i f y‖ ≤ C

def IsTransformOf (F f : Space → ℂ) : Prop :=
  LocallyIntegrable F volume ∧ ∀ φ : SchwartzMap Space ℂ,
    (∫ x, f x * FourierTransform.fourier (φ : Space → ℂ) x) = ∫ ξ, F ξ * φ ξ

def HasMomentsInL1 (G : Space → ℂ) : Prop :=
  AEStronglyMeasurable G volume ∧ ∀ n : ℕ, Integrable (fun ξ => ‖ξ‖ ^ n * ‖G ξ‖)

def kernelConv (k f : Space → ℂ) (x : Space) : ℂ := ∫ z, k z * f (x - z)

def dyadicKernel (σ : Space → ℂ) (θ : Space → ℝ) (d : ℝ) (l : ℤ) (z : Space) : ℂ :=
  (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
    FourierTransform.fourierInv (fun ξ => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z)

def DyadicSplitStatement : Prop :=
  ∀ (σ : Space → ℂ) (d β : ℝ) (θ : Space → ℝ), 0 ≤ d → 0 < β → β < 3 →
    IsHomogeneousSymbol σ d → IsRingCutoff θ →
    ∀ f F : Space → ℂ, IsWeightedSmooth f β → IsTransformOf F f →
    HasMomentsInL1 (fun ξ => σ ξ * F ξ) →
    ContDiff ℝ ∞ (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ)) ∧
    ∀ (n : ℕ) (x : Space), HasSum
      (fun l : ℤ => iteratedFDeriv ℝ n (kernelConv (dyadicKernel σ θ d l) f) x)
      (iteratedFDeriv ℝ n (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ)) x)

def DyadicPieceBoundStatement : Prop :=
  ∀ (σ : Space → ℂ) (d β : ℝ) (θ : Space → ℝ), 0 ≤ d → 0 < β → β < 3 →
    IsHomogeneousSymbol σ d → IsRingCutoff θ →
    ∀ f : Space → ℂ, IsWeightedSmooth f β → ∀ n : ℕ, ∃ C : ℝ, ∀ (l : ℤ) (x : Space), 2 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (kernelConv (dyadicKernel σ θ d l) f) x‖ ≤
        C * (if (2 : ℝ) ^ (l : ℝ) * ‖x‖ ≤ 1 then (2 : ℝ) ^ ((d + n + β) * l)
          else (2 : ℝ) ^ ((d - 2 * (⌈d⌉₊ + 1)) * l) * ‖x‖ ^ (-(β + n + 2 * (⌈d⌉₊ + 1)))
            + (2 : ℝ) ^ ((d - 1 - ⌈d⌉₊) * l) * ‖x‖ ^ (-(1 + β + ⌈d⌉₊ + n)))

def HomogeneousMultiplierStatement : Prop :=
  ∀ (σ : Space → ℂ) (d β : ℝ), 0 ≤ d → 0 < β → β < 3 → IsHomogeneousSymbol σ d →
    ∀ f F : Space → ℂ, IsWeightedSmooth f β → IsTransformOf F f →
    HasMomentsInL1 (fun ξ => σ ξ * F ξ) →
    IsWeightedSmooth (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ)) (β + d)

end Breakdown.FracCert
