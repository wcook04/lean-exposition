import Breakdown.Frac.StTorusReduce

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracTorusForceCoef (α τ : ℝ) (F : Space → Space) (k : Lattice) : Coef :=
  if 0 < τ then fracLatticeFactor α τ k • divFree k (freqTrCoef F k) else 0

def FracTorusForceSpec (α τ : ℝ) (F : Space → Space) (w : V) : Prop :=
  ∀ k, coeff w k = fracTorusForceCoef α τ F k

open Classical in
def fracTorusForce (α τ : ℝ) (F : Space → Space) : V :=
  if h : ∃ w, FracTorusForceSpec α τ F w then h.choose else 0

def FracTorusForceExists (α : ℝ) : Prop :=
  ∀ (τ : ℝ) (F : Space → Space), ∃ w, FracTorusForceSpec α τ F w

def FracTorusForceAlgebra (α : ℝ) : Prop :=
  (∀ τ F k, coeff (fracTorusForce α τ F) k = fracTorusForceCoef α τ F k) ∧
  (∀ σ τ : ℝ, 0 < σ → σ ≤ τ → ∀ F,
    fracTorusForce α τ F = fracTorusHeat α (τ - σ) (fracTorusForce α σ F)) ∧
  ∀ F, ContinuousOn (fun τ => fracTorusForce α τ F) (Ioi 0)

def FracForceSmoothing (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ F : Space → Space, Continuous F → IsPeriodic F →
    ‖fracTorusForce α τ F‖ ≤ C * τ ^ (-(1 / (2 * α))) * Real.sqrt (∫ x in cell, ‖F x‖ ^ 2)

def IsFracTorusForcedMildOnIcc (α : ℝ) (u : ℝ → V) (F : ℝ → Space → Space) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => fracTorusKernel α (t - s) (u s) (u s)) volume a t ∧
      IntervalIntegrable (fun s => fracTorusForce α (t - s) (F s)) volume a t ∧
      u t = fracTorusHeat α (t - a) (u a) + (∫ s in a..t, fracTorusKernel α (t - s) (u s) (u s)) +
        ∫ s in a..t, fracTorusForce α (t - s) (F s)

def IsFracForcedPeriodicSolution (α : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ)
    (F : ℝ → Space → Space) (a b : ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc a b ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Icc a b ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (Icc a b ×ˢ univ) ∧
    (∀ t ∈ Icc a b, IsPeriodic (u t) ∧ IsPeriodic (p t) ∧ IsPeriodic (F t)) ∧
    (∀ t ∈ Icc a b, ∀ x, divergenceAt (u t) x = 0) ∧
    ∀ t ∈ Ioo a b, ∀ x, deriv (fun τ => u τ x) t + advectionAt (u t) x
      + fractionalPowerAt α (u t) x + gradientAt (p t) x = F t x

def FracForcedPeriodicIsMild (α : ℝ) : Prop :=
  ∀ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) (F : ℝ → Space → Space) (a b : ℝ), a < b →
    IsFracForcedPeriodicSolution α u p F a b → IsFracTorusForcedMildOnIcc α (fun t => toV (u t)) F a b

end Breakdown.Periodic
