import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma physicalField_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s₀ t : ℝ) :
    Continuous (physicalField W s₀ t) := by
  have h1 : Continuous (fun y : Space => W (physicalTime s₀ t) y) :=
    hW.continuous.comp (continuous_const.prodMk continuous_id)
  unfold physicalField dilateField
  exact (h1.comp (continuous_id.const_smul (Real.sqrt (1 - t)⁻¹))).const_smul (Real.sqrt (1 - t)⁻¹)

private lemma integrable_one_add_norm_rpow_neg_six :
    Integrable (fun x : Space => (1 + ‖x‖) ^ (-(6:ℝ))) := by
  apply integrable_one_add_norm
  rw [finrank_euclideanSpace, Fintype.card_fin]
  norm_num

private lemma sq_norm_le_of_le {a b : ℝ} (x : Space) (K : ℝ) {u : Space}
    (h : ‖u‖ ≤ K * |a - b| / (1 + ‖x‖) ^ 3) :
    ‖u‖ ^ 2 ≤ (K * |a - b|) ^ 2 * (1 + ‖x‖) ^ (-(6:ℝ)) := by
  have hx : 0 < 1 + ‖x‖ := by positivity
  have e : (1 + ‖x‖) ^ (-(6:ℝ)) = 1 / ((1 + ‖x‖) ^ 3) ^ 2 := by
    rw [Real.rpow_neg hx.le, show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc ‖u‖ ^ 2 ≤ (K * |a - b| / (1 + ‖x‖) ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [e, div_pow]; ring

theorem physicalL2_holds (hdiff : PhysicalDifference) : PhysicalL2 := by
  intro W q C h s₀ T hT
  obtain ⟨K, hK⟩ := hdiff W q C h s₀ T hT
  have hint : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T,
      Integrable (fun x => ‖physicalField W s₀ t x - physicalField W s₀ t' x‖ ^ 2) := by
    intro t ht t' ht'
    refine (integrable_one_add_norm_rpow_neg_six.const_mul ((K * |t - t'|) ^ 2)).mono' ?_ ?_
    · exact (((physicalField_continuous h.smooth s₀ t).sub
        (physicalField_continuous h.smooth s₀ t')).norm.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact sq_norm_le_of_le x K (hK t ht t' ht' x)
  refine ⟨hint, fun t₀ ht₀ => ?_⟩
  have hg : Filter.Tendsto (fun t => (K * |t - t₀|) ^ 2 * ∫ x : Space, (1 + ‖x‖) ^ (-(6:ℝ)))
      (nhdsWithin t₀ (Icc 0 T)) (nhds 0) := by
    have hc : Continuous (fun t : ℝ => (K * |t - t₀|) ^ 2 * ∫ x : Space, (1 + ‖x‖) ^ (-(6:ℝ))) := by
      fun_prop
    have h0 := hc.tendsto t₀
    simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · exact Filter.Eventually.of_forall (fun t => integral_nonneg (fun x => by positivity))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← integral_const_mul]
    exact integral_mono (hint t ht t₀ ht₀) (integrable_one_add_norm_rpow_neg_six.const_mul _)
      (fun x => sq_norm_le_of_le x K (hK t ht t₀ ht₀ x))

end Breakdown
