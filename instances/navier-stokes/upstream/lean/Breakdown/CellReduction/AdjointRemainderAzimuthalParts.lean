import Breakdown.Cert.Statement
import Breakdown.FracCell.ReductionAdjointFrameInverseSquare
import Breakdown.FracCell.ReductionAdjointWeightedInverseSquare

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

open CellCert.Reduction FracInternal.FrameInverseSquareParts

def modeWeight (k : ℤ) : ℝ := |(k : ℝ)| + 1 / 2

def modeInverseSquare (u : Space → ℂ) (k : ℤ) : ℝ≥0∞ :=
  ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 * ‖angularMode u k q.1 q.2‖ ^ 2 / (q.1 ^ 2 + q.2 ^ 2))

def SmoothModeInverseSquareHolds : Prop :=
  ∀ u : Space → Space, ContDiff ℝ ∞ u → HasCompactSupport u → ∀ k : ℤ,
    ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart u) k ≤
      modeGradientSide (fun y => fderiv ℝ u y) k

def WeakClassApproxHolds : Prop :=
  ∀ (V : Space → Space) (D : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable V volume → AEStronglyMeasurable D volume → IsWeakGradient V D →
    ∫⁻ y, ENNReal.ofReal (‖V y‖ ^ 6) < ⊤ → ∫⁻ y, ENNReal.ofReal (matSq (D y)) < ⊤ →
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (u n) y - D y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R,
        ENNReal.ofReal (‖u n y - V y‖ ^ 2)) atTop (𝓝 0)

def GradientModeTotalHolds : Prop :=
  ∀ D : Space → (Space →L[ℝ] Space), AEStronglyMeasurable D volume →
    ∑' k : ℤ, modeGradientSide D k ≤ ∫⁻ y, ENNReal.ofReal (matSq (D y))

def ModePairingHolds : Prop :=
  ∀ (u B : Space → ℂ) (k : ℤ), AEStronglyMeasurable u volume → AEStronglyMeasurable B volume →
    (∀ ρ θ z : ℝ, B (ringPoint ρ θ z) = Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * B (ringPoint ρ 0 z)) →
    ENNReal.ofReal ‖∫ y, starRingEnd ℂ (u y) * B y‖ ^ 2 ≤
      modeInverseSquare u k * ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2)

def TimeModeSumHolds : Prop :=
  ∀ {N : ℕ} (a : Fin N → Space → ℂ) (f : Fin N → ℤ) (S : Finset (Fin N)), Set.InjOn f S →
    (∀ p, AEStronglyMeasurable (a p) volume) →
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 *
        ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * a p y‖ ^ 2)) ≤
      ∑ p ∈ S, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖a p y‖ ^ 2)

def ModeInverseSquareWeakHolds : Prop :=
  ∀ (V : Space → Space) (D : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable V volume → AEStronglyMeasurable D volume → IsWeakGradient V D →
    ∫⁻ y, ENNReal.ofReal (‖V y‖ ^ 6) < ⊤ → ∫⁻ y, ENNReal.ofReal (matSq (D y)) < ⊤ →
    ∑' k : ℤ, ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart V) k ≤
      ∫⁻ y, ENNReal.ofReal (matSq (D y))

end AzimuthalParts

end AdjointDefect

end Breakdown
