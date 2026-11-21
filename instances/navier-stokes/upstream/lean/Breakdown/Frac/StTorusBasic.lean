import Breakdown.Torus.Mild
import Breakdown.Torus.StatementsAnalysis
import Breakdown.Frac.Defs

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

def fracLatticeFactor (α t : ℝ) (k : Lattice) : ℝ :=
  Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * max t 0))

def FracTorusHeatSpec (α t : ℝ) (H : V →L[ℝ] V) : Prop :=
  ∀ u k, coeff (H u) k = fracLatticeFactor α t k • coeff u k

open Classical in
def fracTorusHeat (α t : ℝ) : V →L[ℝ] V :=
  if h : ∃ H, FracTorusHeatSpec α t H then h.choose else 0

def fracTorusKernelCoef (α τ : ℝ) (u v : V) (k : Lattice) : Coef :=
  if 0 < τ then (-(1 / 2) * fracLatticeFactor α τ k) • divFree k (advCoef u v k + advCoef v u k)
  else 0

def FracTorusKernelSpec (α τ : ℝ) (B : V →L[ℝ] V →L[ℝ] V) : Prop :=
  ∀ u v k, coeff (B u v) k = fracTorusKernelCoef α τ u v k

open Classical in
def fracTorusKernel (α τ : ℝ) : V →L[ℝ] V →L[ℝ] V :=
  if h : ∃ B, FracTorusKernelSpec α τ B then h.choose else 0

def IsFracTorusMildOn (α : ℝ) (u : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn u (Ico a b) ∧
    ∀ t ∈ Ico a b, IntervalIntegrable (fun s => fracTorusKernel α (t - s) (u s) (u s)) volume a t ∧
      u t = fracTorusHeat α (t - a) (u a) + ∫ s in a..t, fracTorusKernel α (t - s) (u s) (u s)

def IsFracTorusMildOnIcc (α : ℝ) (u : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => fracTorusKernel α (t - s) (u s) (u s)) volume a t ∧
      u t = fracTorusHeat α (t - a) (u a) + ∫ s in a..t, fracTorusKernel α (t - s) (u s) (u s)

def FracTorusHeatExists (α : ℝ) : Prop := ∀ t : ℝ, ∃ H, FracTorusHeatSpec α t H

def FracTorusKernelExists (α : ℝ) : Prop := ∀ τ : ℝ, ∃ B, FracTorusKernelSpec α τ B

def FracTorusHeatAlgebra (α : ℝ) : Prop :=
  (∀ t u k, coeff (fracTorusHeat α t u) k = fracLatticeFactor α t k • coeff u k) ∧
  fracTorusHeat α 0 = ContinuousLinearMap.id ℝ V ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → fracTorusHeat α (s + t) = (fracTorusHeat α s).comp (fracTorusHeat α t)) ∧
  (∀ t, ‖fracTorusHeat α t‖ ≤ 1) ∧
  (∀ t, fracTorusHeat α t = fracTorusHeat α (max t 0)) ∧
  ∀ x : V, Continuous (fun t => fracTorusHeat α t x)

def FracTorusKernelAlgebra (α : ℝ) : Prop :=
  (∀ τ u v k, coeff (fracTorusKernel α τ u v) k = fracTorusKernelCoef α τ u v k) ∧
  (∀ τ u v, fracTorusKernel α τ u v = fracTorusKernel α τ v u) ∧
  (∀ u v, ContinuousOn (fun τ => fracTorusKernel α τ u v) (Ioi 0)) ∧
  ∀ s τ : ℝ, 0 ≤ s → 0 < τ → ∀ u v,
    fracTorusHeat α s (fracTorusKernel α τ u v) = fracTorusKernel α (s + τ) u v

def FracTorusKernelSharpBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖fracTorusKernel α τ‖ ≤ C * τ ^ (-(3 / (4 * α)))

def FracTorusMildUniqueness (α : ℝ) : Prop :=
  ∀ (u v : ℝ → V) (a b : ℝ), IsFracTorusMildOn α u a b → IsFracTorusMildOnIcc α v a b → u a = v a →
    EqOn u v (Ico a b)

end Breakdown.Periodic
