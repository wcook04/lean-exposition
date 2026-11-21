import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def cutoffPow (r : ℝ) (x : Space) : ℝ := radialCutoff r x ^ 4

def cutoffEnergy (r : ℝ) (w : Space → Space) : ℝ := (1 / 2) * ∫ x, cutoffPow r x * ‖w x‖ ^ 2

def cutoffDissipation (r : ℝ) (w : Space → Space) : ℝ :=
  ∫ x, cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2

def cutoffSixthNorm (r : ℝ) (w : Space → Space) : ℝ :=
  (∫ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ 6) ^ (1 / 6 : ℝ)

def cutoffFlux (r : ℝ) (w : Space → Space) (x : Space) : ℝ := fderiv ℝ (radialCutoff r) x (w x)

def cutoffSource (r : ℝ) (w : Space → Space) : Space → ℝ :=
  divergenceAt (fun x => cutoffPow r x • w x)

def stressPairing (a b : Space → Space) (θ : Space → ℝ) : ℝ :=
  ∫ x, ∑ i, ∑ j, a x i * b x j * FundSol.secondPartial θ i j x

def pressureDefect (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (t : ℝ) (ϕ : Space → Space) : ℝ :=
  (∫ x, inner ℝ (gradientAt (q t) x) (ϕ x)) -
    stressPairing (v t) (v t) (FundSol.potential (divergenceAt ϕ))

def differenceRHS (r : ℝ) (u w : Space → Space) : ℝ :=
  -cutoffDissipation r w
    + (1 / 2) * (∫ x, ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x)
    + (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x + w x) (gradientAt (cutoffPow r) x))
    - (∫ x, cutoffPow r x * inner ℝ (w x) (fderiv ℝ u x (w x)))
    - (stressPairing w w (FundSol.potential (cutoffSource r w))
      + stressPairing u w (FundSol.potential (cutoffSource r w))
      + stressPairing w u (FundSol.potential (cutoffSource r w)))

structure IsFiniteEnergyField (A : ℝ) (w : Space → Space) : Prop where
  smooth : ContDiff ℝ ∞ w
  div_free : ∀ x, divergenceAt w x = 0
  nonneg : 0 ≤ A
  energy : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2)

structure IsDifferenceData (A U₀ U₁ : ℝ) (u w : Space → Space) : Prop where
  field : IsFiniteEnergyField A w
  smooth_u : ContDiff ℝ ∞ u
  div_u : ∀ x, divergenceAt u x = 0
  bound_u : ∀ x, ‖u x‖ ≤ U₀
  bound_du : ∀ x, ‖fderiv ℝ u x‖ ≤ U₁

end Breakdown
