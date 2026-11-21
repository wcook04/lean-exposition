import TorusEuler.AffinePropagation
import TorusEuler.LinearFlowExistence

open Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The affine-wave equations (2.1) admit wave-vector and amplitude paths on the full
closed interval. The paths preserve nonzero perpendicular initial data. -/
theorem affineWave_exists_Icc {D : ℝ → E →L[ℝ] E} {l r t₀ : ℝ} {k₀ a₀ : E}
    (ht₀ : t₀ ∈ Icc l r) (hD : ContinuousOn D (Icc l r))
    (hk₀ : k₀ ≠ 0) (ha₀ : a₀ ≠ 0) (hperp₀ : ⟪k₀, a₀⟫_ℝ = 0) :
    ∃ k a : ℝ → E, k t₀ = k₀ ∧ a t₀ = a₀ ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt k (-((D t).adjoint (k t))) (Icc l r) t) ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt a
        (-((D t) (a t)) + (2 * ⟪k t, D t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 := by
  have hDadj : ContinuousOn (fun t => -(D t).adjoint) (Icc l r) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hD).neg
  obtain ⟨k, hk_init, hk_linear⟩ := linearODE_exists_Icc_of_mem ht₀ hDadj k₀
  have hk_ne₀ : k t₀ ≠ 0 := by rwa [hk_init]
  have hk_ne := linearODE_ne_zero_of_mem ordConnected_Icc ht₀ hDadj hk_linear hk_ne₀
  have hk_cont : ContinuousOn k (Icc l r) := fun t ht => (hk_linear t ht).continuousWithinAt
  have hA := continuousOn_affineWaveAmplitudeOperator hD hk_cont hk_ne
  obtain ⟨a, ha_init, ha_linear⟩ := linearODE_exists_Icc_of_mem ht₀ hA a₀
  have hk (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt k (-((D t).adjoint (k t))) (Icc l r) t := by
    simpa only [neg_apply] using hk_linear t ht
  have ha (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt a
        (-((D t) (a t)) + (2 * ⟪k t, D t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t := by
    simpa only [affineWaveAmplitudeOperator_apply] using ha_linear t ht
  refine ⟨k, a, hk_init, ha_init, hk, ha,
    affineWave_propagation ordConnected_Icc ht₀ hD hk ha hk_ne₀ ?_ ?_⟩
  · rwa [ha_init]
  · rwa [hk_init, ha_init]

end TorusEuler
