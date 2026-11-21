import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

def kernel (z : Space) : ℝ := -(4 * π)⁻¹ * ‖z‖⁻¹

def kernelGrad (z : Space) : Space := ((4 * π)⁻¹ * ‖z‖⁻¹ ^ 3) • z

def kernelSecondDeriv (i j : Fin 3) (z : Space) : ℝ :=
  (4 * π)⁻¹ * ((if i = j then (1 : ℝ) else 0) * ‖z‖⁻¹ ^ 3 - 3 * z i * z j * ‖z‖⁻¹ ^ 5)

def potential (g : Space → ℝ) : Space → ℝ :=
  convolution g kernel (ContinuousLinearMap.lsmul ℝ ℝ) volume

def secondPartial (θ : Space → ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  iteratedFDeriv ℝ 2 θ x ![unitVector i, unitVector j]

def scalarSumSecondPartials (θ : Space → ℝ) (x : Space) : ℝ := ∑ i, secondPartial θ i i x

def bumpProfile (x : Space) : ℝ := smoothTransition (1 - 2 * ‖x‖ ^ 2)

def mollifier (ρ : ℝ) (x : Space) : ℝ := (ρ ^ 3 * ∫ y, bumpProfile y)⁻¹ * bumpProfile (ρ⁻¹ • x)

def mollify (ρ : ℝ) (ϕ : Space → Space) : Space → Space :=
  convolution (mollifier ρ) ϕ (ContinuousLinearMap.lsmul ℝ ℝ) volume

end Breakdown.FundSol
