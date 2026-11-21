import Breakdown.CertCell.ShapeKeyRotation
import Breakdown.CertCell.ShapeKeyTime

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem realPartVec_coord (w : Fin 3 → ℂ) (i : Fin 3) : realPartVec w i = (w i).re := rfl

theorem realPartVec_flipVec (w : Fin 3 → ℂ) : realPartVec (flipVec w) = flipPoint (realPartVec w) := by
  ext i
  fin_cases i <;> simp [realPartVec_coord, flipVec, flipPoint, unitVector]

theorem realPartVec_rotateVec (φ : ℝ) (w : Fin 3 → ℂ) :
    realPartVec (rotateVec φ w) = axialRot φ (realPartVec w) := by
  ext i
  fin_cases i <;> simp [realPartVec_coord, rotateVec, axialRot, unitVector, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem flipVec_sum {α : Type*} (s : Finset α) (v : α → Fin 3 → ℂ) :
    flipVec (∑ a ∈ s, v a) = ∑ a ∈ s, flipVec (v a) := by
  funext i
  fin_cases i <;> simp [flipVec, Finset.sum_apply]

theorem rotateVec_sum {α : Type*} (φ : ℝ) (s : Finset α) (v : α → Fin 3 → ℂ) :
    rotateVec φ (∑ a ∈ s, v a) = ∑ a ∈ s, rotateVec φ (v a) := by
  funext i
  fin_cases i <;>
    simp [rotateVec, Finset.sum_apply, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem flipKey_flipKey (κ : FieldKey) : κ.flipKey.flipKey = κ := by
  obtain ⟨⟨a, b⟩, j⟩ := κ
  simp [FieldKey.flipKey, labelFlip]

theorem exp_whole_turns (θ : ℝ) (n : ℤ) (h : θ = n * (2 * Real.pi)) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [h]
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  ring

theorem complexField_flip (hflip : KeyFlip) (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D)
    (σ : ℝ) (y : Space) : complexField P D σ (flipPoint y) = flipVec (complexField P D σ y) := by
  unfold complexField
  rw [flipVec_sum]
  refine Finset.sum_nbij' FieldKey.flipKey FieldKey.flipKey ?_ ?_ ?_ ?_ ?_
  · intro κ hκ
    exact (hD.keys_flip κ).1 hκ
  · intro κ hκ
    exact (hD.keys_flip κ).1 hκ
  · intro κ _
    exact flipKey_flipKey κ
  · intro κ _
    exact flipKey_flipKey κ
  · intro κ hκ
    have h := hflip P D κ.flipKey σ y hD ((hD.keys_flip κ).1 hκ)
    rw [flipKey_flipKey] at h
    exact h

theorem keyVector_turn (hrot : KeyRotation) (htime : KeyTimeShift) (P : ShapeParams) (D : TimeFieldData)
    (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (σ τ φ : ℝ) (y : Space)
    (hturn : ∃ n : ℤ, 2 * Real.pi * (labelTime κ.label : ℝ) * τ + (labelAzimuth P.azimuthOrder κ.label : ℝ) * φ =
      n * (2 * Real.pi)) :
    keyVector P κ (D.amp κ) (σ + τ) (axialRot φ y) = rotateVec φ (keyVector P κ (D.amp κ) σ y) := by
  obtain ⟨n, hn⟩ := hturn
  funext i
  rw [htime P κ (D.amp κ) σ τ (axialRot φ y)]
  simp only
  rw [hrot P D κ σ φ y hD hκ]
  simp only
  rw [← mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, exp_whole_turns _ n hn, one_mul]

theorem complexField_turn (hrot : KeyRotation) (htime : KeyTimeShift) (P : ShapeParams) (D : TimeFieldData)
    (hD : IsTimeFieldData D) (σ τ φ : ℝ) (y : Space)
    (hturn : ∀ κ ∈ D.keys, ∃ n : ℤ, 2 * Real.pi * (labelTime κ.label : ℝ) * τ +
      (labelAzimuth P.azimuthOrder κ.label : ℝ) * φ = n * (2 * Real.pi)) :
    complexField P D (σ + τ) (axialRot φ y) = rotateVec φ (complexField P D σ y) := by
  unfold complexField
  rw [rotateVec_sum]
  exact Finset.sum_congr rfl fun κ hκ => keyVector_turn hrot htime P D hD κ hκ σ τ φ y (hturn κ hκ)

end Internal

theorem fieldClassInvariant_of (hrot : KeyRotation) (hflip : KeyFlip) (htime : KeyTimeShift) :
    FieldClassInvariant := by
  intro P D hP hD
  have hm : (P.azimuthOrder : ℝ) ≠ 0 := by exact_mod_cast hP.azimuthOrder_pos.ne'
  refine ⟨fun σ y => ?_, fun σ y => ?_, fun σ y => ?_⟩
  · simp only [shapeInfoField]
    rw [Internal.complexField_flip hflip P D hD σ y, Internal.realPartVec_flipVec]
  · simp only [shapeInfoField]
    rw [Internal.complexField_turn hrot htime P D hD σ (1 / 2) _ y, Internal.realPartVec_rotateVec]
    intro κ _
    refine ⟨κ.label.2, ?_⟩
    simp only [labelTime, labelAzimuth]
    push_cast
    field_simp
    ring
  · simp only [shapeInfoField]
    have h := Internal.complexField_turn hrot htime P D hD σ 0 (2 * Real.pi / P.azimuthOrder) y
      (fun κ _ => ⟨κ.label.1, by simp only [labelAzimuth]; push_cast; field_simp; ring⟩)
    rw [add_zero] at h
    rw [h, Internal.realPartVec_rotateVec]

theorem fieldClassInvariant_of_keyFlip (hflip : KeyFlip) : FieldClassInvariant :=
  fieldClassInvariant_of keyRotation hflip keyTimeShift_holds

end GivenShape

end CertCell

end Breakdown
