import Breakdown.Profile.StatementsEmbed

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem embeddedOrbitOfParts_holds : EmbeddedOrbitOfParts := by
  intro hsub hslice hcont hmild hflow X _ _ _ Rlz W q P R C hP h hper hne
  have hD : ∀ s, IsDecayField (W s) := hslice W q C h
  have hc : Continuous (fun s => Rlz.embed (W s)) := by
    rw [continuous_iff_continuousAt]
    intro s₀
    have h2 : Filter.Tendsto (fun s => ‖Rlz.embed (W s) - Rlz.embed (W s₀)‖ ^ 2)
        (nhds s₀) (nhds 0) := by
      have e : (fun s => ‖Rlz.embed (W s) - Rlz.embed (W s₀)‖ ^ 2) = fun s =>
          ∫ y, ∑ i : Fin 3, ‖fderiv ℝ (W s - W s₀) y (unitVector i)‖ ^ 2 := by
        funext s
        rw [← Rlz.embed_sub _ _ (hD s) (hD s₀), Rlz.embed_norm _ (hsub _ _ (hD s) (hD s₀))]
      rw [e]
      exact hcont W q C h s₀
    have h3 := h2.sqrt
    rw [Real.sqrt_zero] at h3
    simp only [Real.sqrt_sq (norm_nonneg _)] at h3
    exact tendsto_iff_norm_sub_tendsto_zero.mpr h3
  refine ⟨hc, ?_, hP, ?_, ?_⟩
  · obtain ⟨s, y, hy⟩ := hne
    exact ⟨s, Rlz.embed_ne_zero (W s) (hD s) ⟨y, hy⟩⟩
  · intro s
    have hWP : W (s + P) = pushForward R (W s) := by
      funext y
      exact hper s y
    rw [hWP, Rlz.embed_rot R (W s) (hD s)]
  · intro s' s hss
    rcases eq_or_lt_of_le hss with heq | hlt
    · subst heq
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp [MildFramework.S, Rlz.F.D_one, Rlz.F.G_zero]
    · have hT0 : 0 < 1 - exp (-(s - s')) := by
        rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      have hT1 : 1 - exp (-(s - s')) < 1 := by
        have := Real.exp_pos (-(s - s'))
        linarith
      have hm := hmild X Rlz W q C h hc s' _ hT0 hT1
      refine hflow X Rlz.F (fun s => Rlz.embed (W s))
        (fun t => Rlz.embed (physicalField W s' t)) s' s hlt hm ?_
      intro r hr
      have hr1 : 0 < (1 - r)⁻¹ := by
        apply inv_pos.mpr
        linarith [hr.2]
      simp only [physicalField, physicalTime]
      rw [Rlz.embed_dilate _ _ hr1 (hD _)]

theorem orbitOfParts_holds : OrbitOfParts := by
  intro hsub hslice hcont hmild hflow X _ _ _ Rlz hex
  obtain ⟨W, q, P, R, C, hP, hW, hq, hres, hdiv, hper, hne, hdec, hqdec⟩ := hex
  exact ⟨fun s => Rlz.embed (W s), P, R,
    embeddedOrbitOfParts_holds hsub hslice hcont hmild hflow X Rlz W q P R C hP
      ⟨hW, hq, hres, hdiv, hdec, hqdec⟩ hper hne⟩

end Breakdown
