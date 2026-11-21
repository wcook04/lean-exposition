import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem physicalScale_bounds {τ T : ℝ} (hT : T < 1) (h0 : 0 ≤ τ) (hτ : τ ≤ T) :
    1 ≤ physicalScale τ ∧ physicalScale τ ≤ physicalScale T := by
  have h1 : 0 < 1 - T := by linarith
  have h2 : 1 - T ≤ 1 - τ := by linarith
  have h3 : 0 < 1 - τ := by linarith
  refine ⟨?_, ?_⟩
  · unfold physicalScale
    rw [Real.one_le_sqrt]
    exact (one_le_inv₀ h3).2 (by linarith)
  · unfold physicalScale
    exact Real.sqrt_le_sqrt (inv_anti₀ h1 h2)

theorem physicalDifference_holds (htime : PhysicalTimeDeriv) (hbound : SimilarityDerivBound) :
    PhysicalDifference := by
  intro W q C hW s₀ T hT
  obtain ⟨K₀, hK₀⟩ := hbound W q C hW
  refine ⟨physicalScale T ^ 3 * max K₀ 0, ?_⟩
  intro t ht t' ht' x
  have hx0 : 0 < 1 + ‖x‖ := by positivity
  have key : ‖physicalField W s₀ t x - physicalField W s₀ t' x‖ ≤
      physicalScale T ^ 3 * max K₀ 0 / (1 + ‖x‖) ^ 3 * ‖t - t'‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => physicalField W s₀ τ x)
      (fun τ hτ => (htime W hW.smooth s₀ τ (lt_of_le_of_lt hτ.2 hT) x).hasDerivWithinAt)
      ?_ (convex_Icc 0 T) ht' ht
    intro τ hτ
    obtain ⟨hs1, hs2⟩ := physicalScale_bounds hT hτ.1 hτ.2
    have hs0 : 0 ≤ physicalScale τ := by linarith
    have hy : 1 + ‖x‖ ≤ 1 + ‖physicalScale τ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      nlinarith [norm_nonneg x]
    have hD := hK₀ (physicalTime s₀ τ) (physicalScale τ • x)
    have h1 : K₀ / (1 + ‖physicalScale τ • x‖) ^ 3 ≤ max K₀ 0 / (1 + ‖x‖) ^ 3 := by
      calc K₀ / (1 + ‖physicalScale τ • x‖) ^ 3
          ≤ max K₀ 0 / (1 + ‖physicalScale τ • x‖) ^ 3 := by
            gcongr
            exact le_max_left _ _
        _ ≤ max K₀ 0 / (1 + ‖x‖) ^ 3 :=
            div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
              (pow_le_pow_left₀ hx0.le hy 3)
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hs0]
    calc physicalScale τ ^ 3 * _
        ≤ physicalScale T ^ 3 * (max K₀ 0 / (1 + ‖x‖) ^ 3) :=
          mul_le_mul (pow_le_pow_left₀ hs0 hs2 3) (hD.trans h1) (norm_nonneg _)
            (pow_nonneg (hs0.trans hs2) 3)
      _ = physicalScale T ^ 3 * max K₀ 0 / (1 + ‖x‖) ^ 3 := by ring
  calc ‖physicalField W s₀ t x - physicalField W s₀ t' x‖
      ≤ physicalScale T ^ 3 * max K₀ 0 / (1 + ‖x‖) ^ 3 * ‖t - t'‖ := key
    _ = physicalScale T ^ 3 * max K₀ 0 * |t - t'| / (1 + ‖x‖) ^ 3 := by
      rw [Real.norm_eq_abs]
      ring

end Breakdown
