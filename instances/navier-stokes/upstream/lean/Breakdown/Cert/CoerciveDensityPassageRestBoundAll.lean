import Breakdown.Cert.CoerciveDensityPassageRestBoundEps
import Breakdown.Cert.CoerciveDensityPassageRestBoundMu

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRestBound

theorem rest_pointwise_bound {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwB : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ σ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W v G H ι σ y|)
        ≤ ENNReal.ofReal K * ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)
          + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) + cnormSq (modeGrad ι G σ y)
          + cnormSq (curlOfGrad (modeGrad ι G σ y)) + cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2)) ∧
      ∀ t : ℝ, 0 < t → ∀ (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
        (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) σ y,
        ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W u Gu Hu ι σ y - modeRest m w W v G H ι σ y|)
          ≤ ENNReal.ofReal (K * (1 + 1 / t)) * ∑' ι : ℤ × ℤ, ENNReal.ofReal
              (cnormSq (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
              + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
              + cnormSq (modeGrad ι Gu σ y - modeGrad ι G σ y)
              + cnormSq (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
              + cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2)
            + ENNReal.ofReal (K * t) * ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)
              + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) + cnormSq (modeGrad ι G σ y)
              + cnormSq (curlOfGrad (modeGrad ι G σ y)) + cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2) :=
  ((base_bound hA hwB v G H).add (epsRest_bound hA hWs hWp hWdec v G H)).add (muRest_bound hA hWs hWdec v G H)

end Internal.DensityPassageRestBound

end Coercive

end Breakdown
