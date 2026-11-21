import Breakdown.CellReduction.InstFieldPotentialParts

open scoped ContDiff Interval

open MeasureTheory Set Metric

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

namespace Internal

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]

theorem fixedIntervalIntegral_contDiff (h : H × ℝ → ℂ) (hh : ContDiff ℝ 1 h) (a b : ℝ) :
    ContDiff ℝ 1 (fun p : H => ∫ s in a..b, h (p, s)) := by
  have hcont : Continuous h := hh.continuous
  have hdcont : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  let D : H → ℝ → H →L[ℝ] ℂ := fun p s => (fderiv ℝ h (p, s)).comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hDcont : Continuous (Function.uncurry D) :=
    ((ContinuousLinearMap.compL ℝ H (H × ℝ) ℂ).flip (ContinuousLinearMap.inl ℝ H ℝ)).continuous.comp
      hdcont
  have hsec : ∀ p : H, Continuous (fun s : ℝ => h (p, s)) := fun p =>
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun p => ∫ s in a..b, D p s, ?_, fun p₀ => ?_⟩
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hDcont a b
  · obtain ⟨C, hC⟩ : ∃ C, ∀ q ∈ closedBall p₀ 1 ×ˢ uIcc a b, ‖Function.uncurry D q‖ ≤ C :=
      ((isCompact_closedBall p₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
        hDcont.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (F' := D) (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun p => (hsec p).aestronglyMeasurable
    · exact (hsec p₀).intervalIntegrable _ _
    · exact (hDcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t ht p hp => hC (p, t) ⟨hp, uIoc_subset_uIcc ht⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ p _ =>
        (hdiff (p, t)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p t)

end Internal

theorem primitiveSmooth_holds : PrimitiveSmoothHolds := by
  intro g hg
  have hcont := hg.continuous
  have hsplit : (fun z : ℝ × ℝ => ∫ u in (-1 : ℝ)..z.2, g (z.1, u)) =
      fun z => (∫ u in (-1 : ℝ)..0, g (z.1, u)) + z.2 • (∫ s in (0 : ℝ)..1, g (z.1, z.2 * s)) := by
    funext z
    have hint : ∀ c d : ℝ, IntervalIntegrable (fun u => g (z.1, u)) volume c d := fun c d =>
      (hcont.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable c d
    have hsub := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun u => g (z.1, u)) z.2
    simp only [mul_zero, mul_one] at hsub
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 z.2), hsub]
  rw [hsplit]
  have h1 : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × ℝ => g (q.1.1, q.2)) :=
    hg.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have h2 : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × ℝ => g (q.1.1, q.1.2 * q.2)) :=
    hg.comp ((contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).mul contDiff_snd))
  exact (Internal.fixedIntervalIntegral_contDiff _ h1 (-1) 0).add
    (contDiff_snd.smul (Internal.fixedIntervalIntegral_contDiff _ h2 0 1))

end Instantiation

end CellReduction

end Breakdown
