import Breakdown.Profile.StatementsSlice

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma slice_eq_comp (W : ℝ → Space → Space) (s : ℝ) :
    W s = (fun z : ℝ × Space => W z.1 z.2) ∘ (fun y : Space => (s, y)) := rfl

private lemma slice_contDiff {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) :
    ContDiff ℝ ∞ (W s) := by
  rw [slice_eq_comp W s]
  exact hW.comp (contDiff_prodMk_right s)

private lemma slice_differentiable {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) :
    Differentiable ℝ (W s) :=
  (slice_contDiff hW s).differentiable (by simp)

private lemma slice_fderiv_apply {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) (y v : Space) :
    fderiv ℝ (W s) y v = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (0, v) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) :=
    (hW.differentiable (by simp)) _
  have h := hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) s y)
  rw [slice_eq_comp W s, h.fderiv]
  rfl

private lemma slice_fderiv_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (y v : Space) :
    Continuous (fun s : ℝ => fderiv ℝ (W s) y v) := by
  have e : (fun s : ℝ => fderiv ℝ (W s) y v) =
      fun s : ℝ => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (0, v) :=
    funext fun s => slice_fderiv_apply hW s y v
  rw [e]
  have hc : Continuous (fun s : ℝ => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y)) :=
    (hW.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)
  exact (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), v)).continuous.comp hc

private lemma slice_fderiv_diff_sq_le {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (h : IsSimilarityProfile W q C) (s s₀ : ℝ) (y : Space) (i : Fin 3) :
    ‖fderiv ℝ (W s - W s₀) y (unitVector i)‖ ^ 2 ≤ 4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  rw [fderiv_sub (slice_differentiable h.smooth s y) (slice_differentiable h.smooth s₀ y),
    sub_apply]
  have hb : ∀ t, ‖fderiv ℝ (W t) y (unitVector i)‖ ≤ C / (1 + ‖y‖) ^ 2 := by
    intro t
    have h1 := h.decay t y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    norm_num at h1
    calc ‖fderiv ℝ (W t) y (unitVector i)‖ ≤ ‖fderiv ℝ (W t) y‖ * ‖unitVector i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (W t) y‖ := by simp [unitVector]
      _ ≤ C / (1 + ‖y‖) ^ 2 := h1
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h2 : ‖fderiv ℝ (W s) y (unitVector i) - fderiv ℝ (W s₀) y (unitVector i)‖ ≤
      2 * (C / (1 + ‖y‖) ^ 2) := by
    calc _ ≤ ‖fderiv ℝ (W s) y (unitVector i)‖ + ‖fderiv ℝ (W s₀) y (unitVector i)‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith [hb s, hb s₀]
  have h3 : (1 + ‖y‖) ^ (-(4 : ℝ)) = 1 / (1 + ‖y‖) ^ 4 := by
    rw [Real.rpow_neg hpos.le, one_div]
    norm_cast
  calc _ ≤ (2 * (C / (1 + ‖y‖) ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = 4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      rw [h3]
      field_simp
      ring

theorem sliceGradientContinuous_holds : SliceGradientContinuous := by
  intro W q C h s₀
  have hW := h.smooth
  have key : ContinuousAt
      (fun s => ∫ y, ∑ i : Fin 3, ‖fderiv ℝ (W s - W s₀) y (unitVector i)‖ ^ 2) s₀ := by
    apply continuousAt_of_dominated (bound := fun y => 12 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)))
    · refine Filter.Eventually.of_forall (fun s => ?_)
      apply Continuous.aestronglyMeasurable
      have hc : Continuous (fderiv ℝ (W s - W s₀)) :=
        ((slice_contDiff hW s).sub (slice_contDiff hW s₀)).continuous_fderiv (by simp)
      exact continuous_finsetSum _ (fun i _ =>
        (((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp hc).norm).pow 2)
    · refine Filter.Eventually.of_forall (fun s => Filter.Eventually.of_forall (fun y => ?_))
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => by positivity))]
      calc _ ≤ ∑ _i : Fin 3, 4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
            Finset.sum_le_sum (fun i _ => slice_fderiv_diff_sq_le h s s₀ y i)
        _ = _ := by simp; ring
    · exact (integrable_one_add_norm (by simp; norm_num)).const_mul _
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have e : (fun s => ∑ i : Fin 3, ‖fderiv ℝ (W s - W s₀) y (unitVector i)‖ ^ 2) =
          fun s => ∑ i : Fin 3,
            ‖fderiv ℝ (W s) y (unitVector i) - fderiv ℝ (W s₀) y (unitVector i)‖ ^ 2 := by
        funext s
        rw [fderiv_sub (slice_differentiable hW s y) (slice_differentiable hW s₀ y)]
        rfl
      rw [e]
      exact (continuous_finsetSum _ (fun i _ =>
        (((slice_fderiv_continuous hW y (unitVector i)).sub continuous_const).norm).pow 2)).continuousAt
  have h0 : (∫ y, ∑ i : Fin 3, ‖fderiv ℝ (W s₀ - W s₀) y (unitVector i)‖ ^ 2) = 0 := by
    simp
  have ht := key.tendsto
  rw [h0] at ht
  exact ht

end Breakdown
