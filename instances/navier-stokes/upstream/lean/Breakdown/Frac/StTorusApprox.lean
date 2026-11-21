import Breakdown.Torus.StatementsApprox
import Breakdown.Frac.StProfile
import Breakdown.Frac.StTorusForce

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def latticePeriodize {E : Type*} [NormedAddCommGroup E] (f : Space → E) (x : Space) : E :=
  ∑' j : Lattice, f (x + freq j)

def fracSelfSimilar (α a : ℝ) (U : Space → Space) (T t : ℝ) (x : Space) : Space :=
  (T - t) ^ (-(1 - 1 / (2 * α))) •
    rotatingSlice a U (similarityTime T t) ((T - t) ^ (-(1 / (2 * α))) • (x - center))

def fracSelfSimilarPressure (α a : ℝ) (P : Space → ℝ) (T t : ℝ) (x : Space) : ℝ :=
  (T - t) ^ (-(2 - 1 / α)) *
    P (axialRotation (a * similarityTime T t) ((T - t) ^ (-(1 / (2 * α))) • (x - center)))

def fracApproxField (α a : ℝ) (U : Space → Space) (T t : ℝ) (x : Space) : Space :=
  cutoffField centralCut center (fracSelfSimilar α a U T t) x

def fracApproxPressure (α a : ℝ) (P : Space → ℝ) (T t : ℝ) (x : Space) : ℝ :=
  centralCut x * (fracSelfSimilarPressure α a P T t x - fracSelfSimilarPressure α a P T t pressureAnchor)

def fracSpaceResidual (α a : ℝ) (U : Space → Space) (P : Space → ℝ) (T t : ℝ) (x : Space) : Space :=
  deriv (fun τ => fracApproxField α a U T τ x) t + advectionAt (fracApproxField α a U T t) x
    + fractionalPowerAt α (fracApproxField α a U T t) x + gradientAt (fracApproxPressure α a P T t) x

def fracApproxResidual (α a : ℝ) (U : Space → Space) (P : Space → ℝ) (T t : ℝ) (x : Space) : Space :=
  deriv (fun τ => latticePeriodize (fracApproxField α a U T τ) x) t
    + advectionAt (latticePeriodize (fracApproxField α a U T t)) x
    + fractionalPowerAt α (latticePeriodize (fracApproxField α a U T t)) x
    + gradientAt (latticePeriodize (fracApproxPressure α a P T t)) x

def FracSelfSimilarSolves (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∀ T : ℝ, 0 < T →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracSelfSimilar α a U T z.1 z.2) (Iio T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracSelfSimilarPressure α a P T z.1 z.2) (Iio T ×ˢ univ) ∧
    ∀ t < T, ∀ x, divergenceAt (fracSelfSimilar α a U T t) x = 0 ∧
      deriv (fun τ => fracSelfSimilar α a U T τ x) t + advectionAt (fracSelfSimilar α a U T t) x
        + fractionalPowerAt α (fracSelfSimilar α a U T t) x
        + gradientAt (fracSelfSimilarPressure α a P T t) x = 0

def FracSelfSimilarDecay (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ C : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      (∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j))) ∧
      ‖deriv (fun τ => fracSelfSimilar α a U T τ x) t‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) ∧
      ‖gradientAt (fracSelfSimilarPressure α a P T t) x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1))

def FracApproxFieldProperties (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∀ T : ℝ, 0 < T →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracApproxField α a U T z.1 z.2) (Iio T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracApproxPressure α a P T z.1 z.2) (Iio T ×ˢ univ) ∧
    ∀ t < T, ∀ x, divergenceAt (fracApproxField α a U T t) x = 0 ∧
      (centralRadius / 2 ≤ dist x center →
        fracApproxField α a U T t x = 0 ∧ fracApproxPressure α a P T t x = 0) ∧
      (dist x center ≤ centralRadius / 4 → fracApproxField α a U T t x = fracSelfSimilar α a U T t x)

def FracPointwiseBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : Space → Space), ContDiff ℝ 3 f → ∀ (x : Space) (r A B L : ℝ), 0 < r → r ≤ 1 →
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z) →
    (∀ y ∈ Metric.closedBall x r, ‖iteratedFDeriv ℝ 3 f y‖ ≤ B) →
    ‖f x‖ ≤ A → ‖fderiv ℝ f x‖ ≤ A → ‖iteratedFDeriv ℝ 2 f x‖ ≤ A →
    IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖f (x + z)‖) {z | r < ‖z‖} →
    ∫ z in {z | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) * ‖f (x + z)‖ ≤ L →
    ‖fractionalPowerAt α f x‖ ≤ C * (B * r ^ (3 - 2 * α) + A * r ^ (-(2 * α)) + L)

def FracPeriodizationTail (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : Space → Space, ContDiff ℝ ∞ f →
    (∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) → ∀ x ∈ cell,
      ‖fractionalPowerAt α (latticePeriodize f) x - fractionalPowerAt α f x‖ ≤ C * ∫ y, ‖f y‖

def FracSpaceResidualBound (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ K : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      ‖fracSpaceResidual α a U P T t x‖ ≤ K * (T - t) ^ (-(2 - 3 / (2 * α)))

def FracResidualRegionBound (α : ℝ) (region : Space → Prop) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ K : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, region x →
      ‖fracSpaceResidual α a U P T t x‖ ≤ K * (T - t) ^ (-(2 - 3 / (2 * α)))

def coreRegion (x : Space) : Prop := dist x center ≤ centralRadius / 4

def shellRegion (x : Space) : Prop := centralRadius / 4 ≤ dist x center ∧ dist x center ≤ centralRadius / 2

def outerRegion (x : Space) : Prop := centralRadius / 2 ≤ dist x center

def FracApproxResidualBound (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ K : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      ‖fracApproxResidual α a U P T t x‖ ≤ K * (T - t) ^ (-(2 - 3 / (2 * α)))

def FracApproxForcedSolution (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P →
    ∀ T t₁ t₂ : ℝ, 0 < T → t₁ < t₂ → t₂ < T →
      IsFracForcedPeriodicSolution α (fun t => latticePeriodize (fracApproxField α a U T t))
        (fun t => latticePeriodize (fracApproxPressure α a P T t)) (fracApproxResidual α a U P T) t₁ t₂

end Breakdown.Periodic
