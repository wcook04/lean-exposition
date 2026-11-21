import Breakdown.Frac.StProfile

noncomputable section

namespace Breakdown

namespace FracInternal

namespace Axial

theorem axialFormula_zero_coord (θ : ℝ) (y : Space) :
    axialRotationFormula θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 := by
  simp [axialRotationFormula]

theorem axialFormula_one_coord (θ : ℝ) (y : Space) :
    axialRotationFormula θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 := by
  simp [axialRotationFormula]

theorem axialFormula_two_coord (θ : ℝ) (y : Space) : axialRotationFormula θ y 2 = y 2 := by
  simp [axialRotationFormula]

theorem turn_zero_coord (y : Space) : axialTurn y 0 = -(y 1) := by
  simp [axialTurn]

theorem turn_one_coord (y : Space) : axialTurn y 1 = y 0 := by
  simp [axialTurn]

theorem turn_two_coord (y : Space) : axialTurn y 2 = 0 := by
  simp [axialTurn]

theorem space_coord_ext {x y : Space} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem axialFormula_add (θ θ' : ℝ) (y : Space) :
    axialRotationFormula (θ + θ') y = axialRotationFormula θ (axialRotationFormula θ' y) := by
  apply space_coord_ext
  · simp only [axialFormula_zero_coord, axialFormula_one_coord, Real.cos_add, Real.sin_add]
    ring
  · simp only [axialFormula_zero_coord, axialFormula_one_coord, Real.cos_add, Real.sin_add]
    ring
  · simp only [axialFormula_two_coord]

theorem axialFormula_zero (y : Space) : axialRotationFormula 0 y = y := by
  apply space_coord_ext
  · simp [axialFormula_zero_coord]
  · simp [axialFormula_one_coord]
  · simp [axialFormula_two_coord]

theorem axialFormula_map_add (θ : ℝ) (x y : Space) :
    axialRotationFormula θ (x + y) = axialRotationFormula θ x + axialRotationFormula θ y := by
  apply space_coord_ext
  · simp only [axialFormula_zero_coord, PiLp.add_apply]
    ring
  · simp only [axialFormula_one_coord, PiLp.add_apply]
    ring
  · simp only [axialFormula_two_coord, PiLp.add_apply]

theorem axialFormula_map_smul (θ c : ℝ) (y : Space) :
    axialRotationFormula θ (c • y) = c • axialRotationFormula θ y := by
  apply space_coord_ext
  · simp only [axialFormula_zero_coord, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [axialFormula_one_coord, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [axialFormula_two_coord, PiLp.smul_apply, smul_eq_mul]

theorem axialFormula_neg_self (θ : ℝ) (y : Space) :
    axialRotationFormula (-θ) (axialRotationFormula θ y) = y := by
  rw [← axialFormula_add, neg_add_cancel, axialFormula_zero]

theorem axialFormula_self_neg (θ : ℝ) (y : Space) :
    axialRotationFormula θ (axialRotationFormula (-θ) y) = y := by
  rw [← axialFormula_add, add_neg_cancel, axialFormula_zero]

theorem axialFormula_norm (θ : ℝ) (y : Space) : ‖axialRotationFormula θ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, axialFormula_zero_coord,
    axialFormula_one_coord, axialFormula_two_coord]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ

def axialFormulaLinear (θ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := axialRotationFormula θ
  map_add' := axialFormula_map_add θ
  map_smul' := axialFormula_map_smul θ

def axialFormulaEquiv (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv :=
    { axialFormulaLinear θ with
      invFun := axialRotationFormula (-θ)
      left_inv := axialFormula_neg_self θ
      right_inv := axialFormula_self_neg θ }
  norm_map' := axialFormula_norm θ

theorem axialRotation_eq_formula (θ : ℝ) (y : Space) :
    axialRotation θ y = axialRotationFormula θ y := by
  have h : ∃ E : Space ≃ₗᵢ[ℝ] Space, ∀ y, E y = axialRotationFormula θ y :=
    ⟨axialFormulaEquiv θ, fun _ => rfl⟩
  unfold axialRotation
  rw [dif_pos h]
  exact h.choose_spec y

def axialCosPart (y : Space) : Space :=
  EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1)

def axialSinPart (y : Space) : Space :=
  EuclideanSpace.single 0 (-(y 1)) + EuclideanSpace.single 1 (y 0)

theorem axialFormula_split (θ : ℝ) (y : Space) :
    axialRotationFormula θ y = (Real.cos θ • axialCosPart y + Real.sin θ • axialSinPart y)
      + EuclideanSpace.single 2 (y 2) := by
  apply space_coord_ext
  · simp [axialFormula_zero_coord, axialCosPart, axialSinPart]
    ring
  · simp [axialFormula_one_coord, axialCosPart, axialSinPart]
    ring
  · simp [axialFormula_two_coord, axialCosPart, axialSinPart]

theorem axialRotation_hasDerivAt (θ : ℝ) (y : Space) :
    HasDerivAt (fun θ' => axialRotation θ' y) (axialTurn (axialRotation θ y)) θ := by
  have hfun : (fun θ' => axialRotation θ' y) = fun θ' =>
      (Real.cos θ' • axialCosPart y + Real.sin θ' • axialSinPart y)
        + EuclideanSpace.single 2 (y 2) := by
    funext θ'
    rw [axialRotation_eq_formula, axialFormula_split]
  rw [hfun]
  have hd := (((Real.hasDerivAt_cos θ).smul_const (axialCosPart y)).add
    ((Real.hasDerivAt_sin θ).smul_const (axialSinPart y))).add_const
      (EuclideanSpace.single 2 (y 2))
  refine hd.congr_deriv ?_
  rw [axialRotation_eq_formula]
  apply space_coord_ext
  · simp [turn_zero_coord, axialFormula_one_coord, axialCosPart, axialSinPart]
    ring
  · simp [turn_one_coord, axialFormula_zero_coord, axialCosPart, axialSinPart]
    ring
  · simp [turn_two_coord, axialCosPart, axialSinPart]

end Axial

end FracInternal

open FracInternal.Axial in
theorem axialRotationSpec : AxialRotationSpec := by
  refine ⟨axialRotation_eq_formula, ?_, ?_, ?_, ?_, axialRotation_hasDerivAt⟩
  · ext y
    rw [axialRotation_eq_formula, axialFormula_zero]
    rfl
  · intro θ θ' y
    simp only [axialRotation_eq_formula, axialFormula_add]
  · intro θ
    refine LinearIsometryEquiv.ext fun y => ?_
    rw [LinearIsometryEquiv.symm_apply_eq, axialRotation_eq_formula, axialRotation_eq_formula,
      axialFormula_self_neg]
  · intro y
    exact continuous_iff_continuousAt.2 fun θ => (axialRotation_hasDerivAt θ y).continuousAt

end Breakdown
