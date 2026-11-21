import Breakdown.Frac.StSpace

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem fracRestrict : FracRestrictStatement := by
  intro α u₀ v q hv hdiv T
  have hsub : Icc (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ici 0 ×ˢ univ :=
    prod_mono Icc_subset_Ici_self subset_rfl
  refine ⟨hv.smooth_velocity.mono hsub, hv.smooth_pressure.mono hsub, ?_, ?_⟩
  · intro t ht x
    have h := hv.momentum t ht.1 x
    rwa [one_smul] at h
  · intro t ht x
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      have hfun : v 0 = u₀ := funext hv.initial
      rw [hfun]
      exact hdiv x
    · exact hv.incompressible t hpos x

end Breakdown
