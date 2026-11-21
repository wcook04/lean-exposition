import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (weightPoly heightRatio radialVec polarVecQ azimVecQ qOf)

namespace Internal

theorem rot_apply_zero (φ : ℝ) (y : Space) :
    axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by
  simp [axialRot, unitVector]

theorem rot_apply_one (φ : ℝ) (y : Space) :
    axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by
  simp [axialRot, unitVector]

theorem rot_apply_two (φ : ℝ) (y : Space) : axialRot φ y 2 = y 2 := by
  simp [axialRot, unitVector]

theorem rot_norm (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, rot_apply_zero, rot_apply_one, rot_apply_two]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ

theorem rot_heightRatio (φ : ℝ) (y : Space) : heightRatio (axialRot φ y) = heightRatio y := by
  simp only [heightRatio, rot_apply_two, rot_norm]

theorem rot_chartCoord (P : ShapeParams) (φ : ℝ) (y : Space) :
    chartCoord P (axialRot φ y) = chartCoord P y := by
  simp only [chartCoord, rot_norm]

theorem rot_of_axis (φ : ℝ) (y : Space) (h0 : y 0 = 0) (h1 : y 1 = 0) : axialRot φ y = y := by
  ext i
  fin_cases i
  · simp [rot_apply_zero, h0, h1]
  · simp [rot_apply_one, h0, h1]
  · simp [rot_apply_two]

theorem rot_plane (φ : ℝ) (y : Space) :
    ((axialRot φ y 0 : ℂ) + (axialRot φ y 1 : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
  rw [rot_apply_zero, rot_apply_one, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  linear_combination (-(Complex.sin (φ : ℂ) * (y 1 : ℂ))) * Complex.I_sq

theorem exp_arg_rotate (z : ℂ) (hz : z ≠ 0) (φ : ℝ) :
    Complex.exp ((Complex.arg (Complex.exp ((φ : ℂ) * Complex.I) * z) : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have h1 := Complex.norm_mul_exp_arg_mul_I (Complex.exp ((φ : ℂ) * Complex.I) * z)
  have h2 := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at h1
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  apply mul_left_cancel₀ hn
  rw [h1]
  nth_rewrite 1 [← h2]
  ring

theorem phase_split (U V θ : ℝ) (a : ℤ) :
    Complex.exp (((U + (a : ℝ) * θ + V : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((U + V : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) ^ a := by
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rot_keyPhase (P : ShapeParams) (κ : FieldKey) (σ φ : ℝ) (y : Space) (hz : ¬ (y 0 = 0 ∧ y 1 = 0)) :
    keyPhase P κ σ (axialRot φ y) =
      Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * φ : ℝ) : ℂ) * Complex.I) * keyPhase P κ σ y := by
  have hz' : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hz
    have h0 := congrArg Complex.re h
    have h1 := congrArg Complex.im h
    simp at h0 h1
    exact ⟨h0, h1⟩
  unfold keyPhase pointAngle
  rw [rot_norm, phase_split, phase_split, rot_plane, exp_arg_rotate _ hz', mul_zpow,
    show ((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I =
      ((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℂ) * ((φ : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul]
  ring

theorem axis_third_zero (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (y : Space)
    (h0 : y 0 = 0) (h1 : y 1 = 0) (hl : κ.label.1 ≠ 0) (hA : 1 ≤ A.lowOrder) :
    reducedComps P κ A (chartCoord P y) (heightRatio y) 0 * (radialVec y 2 : ℂ) +
      reducedComps P κ A (chartCoord P y) (heightRatio y) 1 * (polarVecQ y 2 : ℂ) = 0 := by
  have hAx : axisFactor (heightRatio y) = 0 ∨ weightPoly A.lowOrder A.highOrder (chartCoord P y) = 0 := by
    by_cases hy : y = 0
    · right
      subst hy
      have : (A.lowOrder) ≠ 0 := by omega
      simp [weightPoly, chartCoord, zero_pow this]
    · left
      have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      have hsq : ‖y‖ ^ 2 = y 2 ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        simp [Fin.sum_univ_three, h0, h1]
      have hx : heightRatio y ^ 2 = 1 := by
        rw [heightRatio, div_pow, ← hsq, div_self (pow_ne_zero 2 hn)]
      simp [axisFactor, hx]
  simp only [reducedComps, if_neg hl, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hAx with h | h <;> simp [h]

theorem keyRotation_of_lowOrder_pos (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ φ : ℝ) (y : Space)
    (hA : κ.label.1 ≠ 0 → 1 ≤ A.lowOrder) :
    keyVector P κ A σ (axialRot φ y) =
      fun i => Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        rotateVec φ (keyVector P κ A σ y) i := by
  by_cases hz : y 0 = 0 ∧ y 1 = 0
  · rw [rot_of_axis φ y hz.1 hz.2]
    funext i
    fin_cases i
    · simp [keyVector, rotateVec, radialVec, polarVecQ, azimVecQ, hz.1, hz.2]
    · simp [keyVector, rotateVec, radialVec, polarVecQ, azimVecQ, hz.1, hz.2]
    · simp only [rotateVec, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Fin.reduceFinMk]
      by_cases hl : κ.label.1 = 0
      · simp [labelAzimuth, hl]
      · have hv := axis_third_zero P κ A y hz.1 hz.2 hl (hA hl)
        have hk : keyVector P κ A σ y 2 = 0 := by
          simp only [keyVector]
          rw [show (azimVecQ y 2 : ℂ) = 0 by simp [azimVecQ], mul_zero, add_zero, hv, mul_zero]
        rw [hk, mul_zero]
  · unfold keyVector
    rw [rot_keyPhase P κ σ φ y hz, rot_chartCoord, rot_heightRatio]
    generalize reducedComps P κ A (chartCoord P y) (heightRatio y) = R
    funext i
    fin_cases i <;>
      simp [rotateVec, radialVec, polarVecQ, azimVecQ, qOf, rot_apply_zero, rot_apply_one, rot_apply_two,
        rot_norm, rot_heightRatio] <;>
      ring

end Internal

theorem keyRotation : KeyRotation := by
  intro P D κ σ φ y hD hκ
  exact Internal.keyRotation_of_lowOrder_pos P κ (D.amp κ) σ φ y
    (fun hl => le_trans (by norm_num) (hD.lowOrder_ge κ hκ hl))

end GivenShape

end CertCell

end Breakdown
