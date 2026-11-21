import Breakdown.FracCert.HeldStateLimitBParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def LocalStrongSubseqStatement : Prop :=
  ∀ (m : ℕ) (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
    (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (w₀ : Space → Space) (B : ℝ),
    (∀ n, IsSecondOrderField m (u n) (G n) (H n)) →
    (∀ n, (∫ y, entrySq (G n y)) + (∫ y, ‖secondTrace (H n y)‖ ^ 2) ≤ B) → MemLp w₀ 2 volume →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r : ℝ,
      Filter.Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u (φ n) y - ‖y‖ • w₀ y‖ ^ 2)
        Filter.atTop (nhds 0)

end SteadyCert

end Breakdown
