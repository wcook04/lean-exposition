import TorusEuler.LocalizedAmplitudeComparison

/-! The positive normalized amplitude of the selected central wave. -/

open Set

namespace TorusEuler.LocalizedAmplitude

/-- The selected central solution supplies the exact time weight and its
continuous slab derivative, with the prescribed peak normalization. -/
theorem CenterWaveOn.normalizedWeight
    {M : ℝ → Vec3 →L[ℝ] Vec3} {κ center : ℝ → Vec3} {t₀ T D freq : ℝ}
    (c : CenterWaveOn M κ center t₀ T D) (hf : 0 < freq)
    (hM : ContinuousOn M (Icc t₀ T))
    (hPeak : ∀ t ∈ Icc t₀ T, ‖center t‖ ≤ freq ^ (-(3 / 4) : ℝ)) :
    let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
    ContinuousOn γ (Icc t₀ T) ∧ (∀ t ∈ Icc t₀ T, 0 < γ t ∧ γ t ≤ 1) ∧
      ∃ dγ : ℝ → ℝ, ContinuousOn dγ (Icc t₀ T) ∧
        ∀ t ∈ Icc t₀ T, HasDerivWithinAt γ (dγ t) (Icc t₀ T) t := by
  intro γ
  have hk := HasDerivWithinAt.continuousOn c.covector
  have hc := HasDerivWithinAt.continuousOn c.amplitude
  have hoperator := continuousOn_affineWaveAmplitudeOperator hM hk (fun t ht => (c.nonzero t ht).1)
  obtain ⟨dγ, hdc, hderiv⟩ := norm_hasContinuous_derivative c.amplitude
    (hoperator.clm_apply hc) (fun t ht => (c.nonzero t ht).2.1)
  refine ⟨continuousOn_const.mul hc.norm, ?_, fun t => freq ^ (3 / 4 : ℝ) * dγ t,
    continuousOn_const.mul hdc, fun t ht => (hderiv t ht).const_mul _⟩
  intro t ht
  refine ⟨mul_pos (Real.rpow_pos_of_pos hf _) (norm_pos_iff.mpr (c.nonzero t ht).2.1), ?_⟩
  dsimp [γ]
  calc
    _ ≤ freq ^ (3 / 4 : ℝ) * freq ^ (-(3 / 4) : ℝ) :=
      mul_le_mul_of_nonneg_left (hPeak t ht) (Real.rpow_nonneg hf.le _)
    _ = 1 := by rw [← Real.rpow_add hf, add_neg_cancel, Real.rpow_zero]

end TorusEuler.LocalizedAmplitude
