import TorusEuler.AffineIdentities
import TorusEuler.LinearFlow

open Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear amplitude operator for a prescribed wave vector. -/
noncomputable def affineWaveAmplitudeOperator (D : E →L[ℝ] E) (k : E) : E →L[ℝ] E :=
  -D + (2 / ‖k‖ ^ 2) • (InnerProductSpace.rankOne ℝ k k).comp D

theorem affineWaveAmplitudeOperator_apply (D : E →L[ℝ] E) (k a : E) :
    affineWaveAmplitudeOperator D k a = -(D a) + (2 * ⟪k, D a⟫_ℝ / ‖k‖ ^ 2) • k := by
  simp only [affineWaveAmplitudeOperator, add_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, smul_smul,
    div_mul_eq_mul_div]

theorem continuousOn_affineWaveAmplitudeOperator {D : ℝ → E →L[ℝ] E} {k : ℝ → E}
    {J : Set ℝ} (hD : ContinuousOn D J) (hk : ContinuousOn k J) (hk_ne : ∀ t ∈ J, k t ≠ 0) :
    ContinuousOn (fun t => affineWaveAmplitudeOperator (D t) (k t)) J := by
  have hRank : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (k t) (k t)) J := by
    have hInner : ContinuousOn (fun t => innerSL ℝ (k t)) J :=
      (innerSL ℝ).continuous.comp_continuousOn hk
    exact (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E) (F := E)).continuous
      |>.comp_continuousOn (hInner.prodMk hk)
  have hScale : ContinuousOn (fun t => (2 : ℝ) / ‖k t‖ ^ 2) J :=
    continuousOn_const.div (hk.norm.pow 2)
      (fun t ht => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hk_ne t ht)))
  exact hD.neg.add (hScale.smul (hRank.clm_comp hD))

variable [CompleteSpace E]

/-- Nonzero perpendicular data stay nonzero and perpendicular along solutions of the
affine-wave equations on an interval, including its endpoints when present. -/
theorem affineWave_propagation {D : ℝ → E →L[ℝ] E} {k a : ℝ → E} {J : Set ℝ}
    {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hD : ContinuousOn D J)
    (hk : ∀ t ∈ J, HasDerivWithinAt k (-((D t).adjoint (k t))) J t)
    (ha : ∀ t ∈ J, HasDerivWithinAt a
      (-((D t) (a t)) + (2 * ⟪k t, D t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) J t)
    (hk₀ : k t₀ ≠ 0) (ha₀ : a t₀ ≠ 0) (hperp₀ : ⟪k t₀, a t₀⟫_ℝ = 0) :
    ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 := by
  have hDadj : ContinuousOn (fun t => -(D t).adjoint) J :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hD).neg
  have hk_ne : ∀ t ∈ J, k t ≠ 0 :=
    linearODE_ne_zero_of_mem hJ ht₀ hDadj
      (fun t ht => by simpa only [neg_apply] using hk t ht) hk₀
  have hk_cont : ContinuousOn k J := fun t ht => (hk t ht).continuousWithinAt
  have hA := continuousOn_affineWaveAmplitudeOperator hD hk_cont hk_ne
  have ha_ne : ∀ t ∈ J, a t ≠ 0 := by
    refine linearODE_ne_zero_of_mem hJ ht₀ hA (fun t ht => ?_) ha₀
    simpa only [affineWaveAmplitudeOperator_apply] using ha t ht
  have hperp : EqOn (fun t => ⟪k t, a t⟫_ℝ) (fun _ => (0 : ℝ)) J :=
    linearODE_unique_of_mem (A := fun _ => 0) hJ ht₀ continuousOn_const
      (fun t ht => by simpa only [zero_apply] using
        hasDerivWithinAt_affineWavePairing_zero (hk_ne t ht) (hk t ht) (ha t ht))
      (fun t _ => by simpa only [zero_apply] using
        hasDerivWithinAt_const t J (0 : ℝ)) hperp₀
  exact fun t ht => ⟨hk_ne t ht, ha_ne t ht, hperp ht⟩

end TorusEuler
