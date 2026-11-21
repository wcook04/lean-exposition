import Breakdown.Torus.Mild

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def IsPeriodic {E : Type*} (f : Space → E) : Prop := ∀ i x, f (x + unitVector i) = f x

def cell : Set Space := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

def complexify (x : Space) : Coef := WithLp.toLp 2 (fun i => ((x i : ℝ) : ℂ))

def character (k : Lattice) (x : Space) : ℂ :=
  Complex.exp (-(2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)))

def freqTrCoef (f : Space → Space) (k : Lattice) : Coef :=
  ∫ x in cell, character k x • complexify (f x)

def scalarCoef (g : Space → ℝ) (k : Lattice) : ℂ :=
  ∫ x in cell, character k x * (g x : ℂ)

def weightedCoef (f : Space → Space) (k : Lattice) : Coef := Real.sqrt (weight k) • freqTrCoef f k

open Classical in
def toV (f : Space → Space) : V :=
  if h : ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace then
    ⟨⟨weightedCoef f, h.choose⟩, h.choose_spec⟩
  else 0

def SmoothPeriodicIsMild : Prop :=
  ∀ (u₀ : Space → Space) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsSmoothSolution 1 u₀ u p → (∀ t ≥ 0, IsPeriodic (u t)) → (∀ t ≥ 0, IsPeriodic (p t)) →
      ∀ T : ℝ, 0 < T → IsMildOnIcc (fun t => toV (u t)) 0 T

def MovingFrameReduction : Prop :=
  ∀ (u₀ : Space → Space) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsSmoothSolution 1 u₀ u p → (∀ t ≥ 0, IsPeriodic (u t)) →
      ∃ (u' : ℝ → Space → Space) (p' : ℝ → Space → ℝ), IsSmoothSolution 1 u₀ u' p' ∧
        (∀ t ≥ 0, IsPeriodic (u' t)) ∧ ∀ t ≥ 0, IsPeriodic (p' t)

def TorusBlowup : Prop :=
  ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergenceAt u₀ x = 0) ∧
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → V, u 0 = toV u₀ ∧ IsMildOn u 0 T ∧
      ¬ BddAbove ((fun t => ‖u t‖) '' Ico 0 T)

end Breakdown.Periodic
