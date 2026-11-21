import TorusEuler.PeriodicLerayHolderLift

/-! A pointwise estimate for the actual Leray projection from spatial jets. -/

open Set

namespace TorusEuler

/-- Uniform zeroth and first spatial jet bounds control the half-Hölder norm
on the Euclidean lift. -/
theorem spatialHolderHalf_zero_of_uniform_value_and_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec3 → E} (hf : Differentiable ℝ f)
    {A B : ℝ} (hSup : ∀ x, ‖f x‖ ≤ A) (hFDeriv : ∀ x, ‖fderiv ℝ f x‖ ≤ B) :
    SpatialHolderHalf 0 f ∧ spatialHolderHalfNorm 0 f ≤ 3 * A + B := by
  have hA : 0 ≤ A := (norm_nonneg (f 0)).trans (hSup 0)
  have hB : 0 ≤ B := (norm_nonneg (fderiv ℝ f 0)).trans (hFDeriv 0)
  have hK : 0 ≤ 2 * A + B := by positivity
  have hIncrement (x v : Vec3) : ‖f (x + v) - f x‖ ≤ (2 * A + B) * Real.sqrt ‖v‖ := by
    by_cases hSmall : ‖v‖ ≤ 1
    · have hDer : ‖f (x + v) - f x‖ ≤ B * ‖v‖ := by
        simpa only [add_sub_cancel_left] using
          (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
            (fun y _ => hf y) (fun y _ => hFDeriv y) (mem_univ x) (mem_univ (x + v))
      have hsqrt : ‖v‖ ≤ Real.sqrt ‖v‖ :=
        Real.le_sqrt_of_sq_le (by
          simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hSmall (norm_nonneg v))
      exact hDer.trans (mul_le_mul (by linarith only [hA]) hsqrt (norm_nonneg v) hK)
    · have hsqrt : 1 ≤ Real.sqrt ‖v‖ := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_not_ge hSmall)
      calc
        ‖f (x + v) - f x‖ ≤ ‖f (x + v)‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ A + A := add_le_add (hSup _) (hSup _)
        _ = 2 * A * 1 := by ring
        _ ≤ (2 * A + B) * Real.sqrt ‖v‖ :=
          mul_le_mul (le_add_of_nonneg_right hB) hsqrt zero_le_one hK
  have hQuot (p : Vec3 × Vec3) : spatialHolderHalfQuotient f p ≤ 2 * A + B := by
    obtain ⟨x, v⟩ := p
    by_cases hv : v = 0
    · simpa only [spatialHolderHalfQuotient, hv, add_zero, sub_self, norm_zero, zero_div] using hK
    · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).mpr (hIncrement x v)
  refine ⟨(spatialHolderHalf_zero_iff f).2 ⟨hf.continuous,
    ⟨A, forall_mem_range.mpr hSup⟩, ⟨2 * A + B, forall_mem_range.mpr hQuot⟩⟩, ?_⟩
  rw [spatialHolderHalfNorm_zero_eq]
  exact (add_le_add (ciSup_le hSup) (ciSup_le hQuot)).trans_eq (by ring)

/-- The fixed torus Leray projection admits a pointwise bound in terms of a
spatial supremum and a supremum of the Fréchet derivative. -/
theorem norm_periodicLerayHolderLift_le_sup_and_fderiv {f : Vec3 → Vec3}
    (hf : Differentiable ℝ f) (hper : SpatiallyPeriodic f)
    {A B : ℝ} (hSup : ∀ x, ‖f x‖ ≤ A) (hFDeriv : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (x : Vec3) :
    ‖periodicLerayHolderLift f x‖ ≤
      (Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) * (3 * A + B) := by
  obtain ⟨hHolder, hNorm⟩ := spatialHolderHalf_zero_of_uniform_value_and_fderiv hf hSup hFDeriv
  obtain ⟨u, hU, hNormU⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper hHolder
  rw [← funext hU, periodicLerayHolderLift_pullback]
  calc
    _ ≤ ‖endpointStrongSpatialLeray u‖ :=
      ((HalfHolder.norm_le_iff (norm_nonneg (endpointStrongSpatialLeray u))).mp le_rfl).1 (toUnitTorus x)
    _ ≤ ‖endpointStrongSpatialLeray‖ * ‖u‖ := endpointStrongSpatialLeray.le_opNorm u
    _ ≤ ‖endpointStrongSpatialLeray‖ * (Real.sqrt 2 * (3 * A + B)) :=
      mul_le_mul_of_nonneg_left (hNormU.trans (mul_le_mul_of_nonneg_left hNorm (Real.sqrt_nonneg 2)))
        (norm_nonneg endpointStrongSpatialLeray)
    _ = _ := by ring

end TorusEuler
