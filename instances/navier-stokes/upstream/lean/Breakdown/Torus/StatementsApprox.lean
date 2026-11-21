import Breakdown.Torus.StatementsCutoff
import Breakdown.Profile.StatementsSlice

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def center : Space := ∑ i, (1 / 2 : ℝ) • unitVector i

def centralRadius : ℝ := 1 / 4

def centralBump : ContDiffBump center where
  rIn := centralRadius / 4
  rOut := centralRadius / 2
  rIn_pos := by norm_num [centralRadius]
  rIn_lt_rOut := by norm_num [centralRadius]

def centralCut (x : Space) : ℝ := centralBump x

def similarityTime (T t : ℝ) : ℝ := -Real.log ((T - t) / T)

def selfSimilar (W : ℝ → Space → Space) (T t : ℝ) (x : Space) : Space :=
  (T - t) ^ (-(1 / 2 : ℝ)) • W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))

def selfSimilarPressure (q : ℝ → Space → ℝ) (T t : ℝ) (x : Space) : ℝ :=
  (T - t)⁻¹ * q (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))

def pressureAnchor : Space := center + ((3 / 8 : ℝ) * centralRadius) • unitVector 0

def approxField (W : ℝ → Space → Space) (T t : ℝ) (x : Space) : Space :=
  cutoffField centralCut center (selfSimilar W T t) x

def approxPressure (q : ℝ → Space → ℝ) (T t : ℝ) (x : Space) : ℝ :=
  centralCut x * (selfSimilarPressure q T t x - selfSimilarPressure q T t pressureAnchor)

def approxResidual (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (T t : ℝ) (x : Space) : Space :=
  deriv (fun τ => approxField W T τ x) t + advectionAt (approxField W T t) x
    - sumSecondPartialsAt (approxField W T t) x + gradientAt (approxPressure q T t) x

def SelfSimilarSolves : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C T : ℝ), IsSimilarityProfile W q C → 0 < T →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilar W T z.1 z.2) (Iio T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilarPressure q T z.1 z.2) (Iio T ×ˢ univ) ∧
    ∀ t < T, ∀ x, divergenceAt (selfSimilar W T t) x = 0 ∧
      deriv (fun τ => selfSimilar W T τ x) t + advectionAt (selfSimilar W T t) x
        - sumSecondPartialsAt (selfSimilar W T t) x + gradientAt (selfSimilarPressure q T t) x = 0

def ApproxFieldProperties : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C T : ℝ), IsSimilarityProfile W q C → 0 < T →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => approxField W T z.1 z.2) (Iio T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => approxPressure q T z.1 z.2) (Iio T ×ˢ univ) ∧
    ∀ t < T, ∀ x, divergenceAt (approxField W T t) x = 0 ∧
      (centralRadius / 2 ≤ dist x center → approxField W T t x = 0 ∧ approxPressure q T t x = 0) ∧
      (dist x center ≤ centralRadius / 4 → approxField W T t x = selfSimilar W T t x)

def ApproxResidualBound : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∃ K : ℝ, ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x,
      ‖approxResidual W q T t x‖ ≤ K * (T - t) ^ (-(1 / 2 : ℝ)) ∧
      (approxResidual W q T t x ≠ 0 → centralRadius / 4 ≤ dist x center ∧ dist x center ≤ centralRadius / 2)

end Breakdown.Periodic
