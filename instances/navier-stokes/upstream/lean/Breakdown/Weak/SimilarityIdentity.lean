import Breakdown.Weak.StatementsTime

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

theorem similarityIdentity_holds : SimilarityIdentity := by
  intro hSI hST hPV hAB x W G M C hx hslice hweak α s₀ φ hα hαc hφ
  obtain ⟨hint, hzero⟩ := hweak _ (hST α s₀ φ hα hαc hφ)
  rw [Measure.volume_eq_prod] at hint hzero
  have hfun : (fun σ => ∫ y, weakSimilarityIntegrand W G (scaledTest α s₀ φ) (σ, y)) =
      similarityRate x α s₀ φ := by
    funext σ
    exact hSI hPV hAB (x σ) (W σ) (G σ) C (hslice σ) (hx.vel σ) (hx.part σ) α s₀ σ φ hα hαc hφ
  refine ⟨hfun ▸ hint.integral_prod_left, ?_⟩
  rw [← hfun, ← integral_prod _ hint]
  exact hzero

end Breakdown.WeakProfile
