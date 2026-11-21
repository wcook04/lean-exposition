import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace RotationInternal

theorem axialRot_apply_zero (φ : ℝ) (y : Space) :
    axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by
  simp [axialRot, unitVector]

theorem axialRot_apply_one (φ : ℝ) (y : Space) :
    axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by
  simp [axialRot, unitVector]

theorem axialRot_apply_two (φ : ℝ) (y : Space) : axialRot φ y 2 = y 2 := by
  simp [axialRot, unitVector]

theorem space_ext {x y : Space} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem axialRot_add (φ ψ : ℝ) (y : Space) :
    axialRot (φ + ψ) y = axialRot φ (axialRot ψ y) := by
  apply space_ext
  · simp only [axialRot_apply_zero, axialRot_apply_one, Real.cos_add, Real.sin_add]
    ring
  · simp only [axialRot_apply_zero, axialRot_apply_one, Real.cos_add, Real.sin_add]
    ring
  · simp only [axialRot_apply_two]

theorem axialRot_zero (y : Space) : axialRot 0 y = y := by
  apply space_ext
  · simp [axialRot_apply_zero]
  · simp [axialRot_apply_one]
  · simp [axialRot_apply_two]

theorem axialRot_map_add (φ : ℝ) (x y : Space) :
    axialRot φ (x + y) = axialRot φ x + axialRot φ y := by
  apply space_ext
  · simp only [axialRot_apply_zero, PiLp.add_apply]
    ring
  · simp only [axialRot_apply_one, PiLp.add_apply]
    ring
  · simp only [axialRot_apply_two, PiLp.add_apply]

theorem axialRot_map_smul (φ c : ℝ) (y : Space) :
    axialRot φ (c • y) = c • axialRot φ y := by
  apply space_ext
  · simp only [axialRot_apply_zero, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [axialRot_apply_one, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [axialRot_apply_two, PiLp.smul_apply, smul_eq_mul]

theorem axialRot_neg_self (φ : ℝ) (y : Space) : axialRot (-φ) (axialRot φ y) = y := by
  rw [← axialRot_add, neg_add_cancel, axialRot_zero]

theorem axialRot_self_neg (φ : ℝ) (y : Space) : axialRot φ (axialRot (-φ) y) = y := by
  rw [← axialRot_add, add_neg_cancel, axialRot_zero]

theorem axialRot_norm (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, axialRot_apply_zero,
    axialRot_apply_one, axialRot_apply_two]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ

def axialRotLinear (φ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := axialRot φ
  map_add' := axialRot_map_add φ
  map_smul' := axialRot_map_smul φ

def axialRotEquiv (φ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv :=
    { axialRotLinear φ with
      invFun := axialRot (-φ)
      left_inv := axialRot_neg_self φ
      right_inv := axialRot_self_neg φ }
  norm_map' := axialRot_norm φ

end RotationInternal

open RotationInternal in
theorem axialRotationHolds_proof : AxialRotationHolds := by
  refine ⟨fun φ => ⟨axialRotEquiv φ, fun y => rfl⟩, axialRot_add, axialRot_zero, ?_, ?_⟩
  · intro φ y
    apply space_ext
    · simp only [axialRot_apply_zero, Real.cos_add_two_pi, Real.sin_add_two_pi]
    · simp only [axialRot_apply_one, Real.cos_add_two_pi, Real.sin_add_two_pi]
    · simp only [axialRot_apply_two]
  · intro φ y
    refine ⟨?_, axialRot_apply_two φ y⟩
    unfold cylRadius
    congr 1
    rw [axialRot_apply_zero, axialRot_apply_one]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ

end Coercive

end Breakdown
