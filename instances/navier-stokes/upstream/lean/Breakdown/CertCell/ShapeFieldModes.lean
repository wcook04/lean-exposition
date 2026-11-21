import Breakdown.CertCell.ShapeKeyTime
import Breakdown.CertCell.ShapeKeyRotation
import Breakdown.CertCell.ShapeKeyConj

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

def fieldModesWave (a b : ℤ) (τ φ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (a : ℝ) * τ + (b : ℝ) * φ : ℝ) : ℂ) * Complex.I)

theorem fieldModesWave_split (a b : ℤ) (τ φ : ℝ) :
    fieldModesWave a b τ φ = Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((((b : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
  unfold fieldModesWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fieldModesWave_mul (a b a' b' : ℤ) (τ φ : ℝ) :
    fieldModesWave a b τ φ * fieldModesWave a' b' τ φ = fieldModesWave (a + a') (b + b') τ φ := by
  unfold fieldModesWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fieldModesWave_conj (a b : ℤ) (τ φ : ℝ) :
    starRingEnd ℂ (fieldModesWave a b τ φ) = fieldModesWave (-a) (-b) τ φ := by
  unfold fieldModesWave
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem fieldModes_angle_integral (b : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((((b : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
      if b = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp
  · rw [if_neg hb]
    have hc : ((b : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hb) Complex.I_ne_zero
    have e : ∀ φ : ℝ, Complex.exp ((((b : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((b : ℂ) * Complex.I) * (φ : ℂ)) := fun φ => by
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((b : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I b]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem fieldModes_time_integral (a : ℤ) :
    ∫ τ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I) =
      if a = 0 then 1 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [if_neg ha]
    have hc : ((2 * Real.pi * (a : ℝ) : ℝ) : ℂ) * Complex.I ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      have : (2 * Real.pi * (a : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast ha)
      exact_mod_cast this
    have e : ∀ τ : ℝ, Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((((2 * Real.pi * (a : ℝ) : ℝ) : ℂ) * Complex.I) * (τ : ℂ)) := fun τ => by
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((2 * Real.pi * (a : ℝ) : ℝ) : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I a]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem fieldModesWave_continuous (a b : ℤ) (τ : ℝ) : Continuous (fun φ => fieldModesWave a b τ φ) := by
  unfold fieldModesWave
  fun_prop

theorem fieldModes_time_continuous (a : ℤ) :
    Continuous (fun τ : ℝ => Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I)) := by
  fun_prop

theorem fieldModesWave_intervalIntegrable (c : ℂ) (a b : ℤ) (τ : ℝ) :
    IntervalIntegrable (fun φ => c * fieldModesWave a b τ φ) volume 0 (2 * Real.pi) :=
  (continuous_const.mul (fieldModesWave_continuous a b τ)).intervalIntegrable _ _

theorem fieldModes_time_intervalIntegrable (c : ℂ) (a : ℤ) :
    IntervalIntegrable (fun τ : ℝ => c * Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I))
      volume 0 1 :=
  (continuous_const.mul (fieldModes_time_continuous a)).intervalIntegrable _ _

theorem fieldModes_inner_integral (a b : ℤ) (τ : ℝ) (c : ℂ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), c * fieldModesWave a b τ φ =
      (c * if b = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) *
        Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I) := by
  simp_rw [fieldModesWave_split]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, fieldModes_angle_integral]
  ring

theorem fieldModes_delta (a b : ℤ) (K c : ℂ) :
    (c * if b = 0 then K else 0) * (if a = 0 then 1 else 0) = if a = 0 ∧ b = 0 then K * c else 0 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, mul_comm]

theorem fieldModes_double_integral {ι : Type*} (s : Finset ι) (c d : ι → ℂ) (a b a' b' : ι → ℤ) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ i ∈ s, (c i * fieldModesWave (a i) (b i) τ φ + d i * fieldModesWave (a' i) (b' i) τ φ) =
      ∑ i ∈ s, ((if a i = 0 ∧ b i = 0 then ((2 * Real.pi : ℝ) : ℂ) * c i else 0) +
        (if a' i = 0 ∧ b' i = 0 then ((2 * Real.pi : ℝ) : ℂ) * d i else 0)) := by
  have hin : ∀ τ : ℝ, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ∑ i ∈ s, (c i * fieldModesWave (a i) (b i) τ φ + d i * fieldModesWave (a' i) (b' i) τ φ) =
      ∑ i ∈ s, ((c i * if b i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (a i : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
        (d i * if b' i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (a' i : ℝ) * τ : ℝ) : ℂ) * Complex.I)) := by
    intro τ
    rw [intervalIntegral.integral_finsetSum (f := fun i φ =>
      c i * fieldModesWave (a i) (b i) τ φ + d i * fieldModesWave (a' i) (b' i) τ φ) fun i _ =>
      ((continuous_const.mul (fieldModesWave_continuous _ _ τ)).add
        (continuous_const.mul (fieldModesWave_continuous _ _ τ))).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_add (fieldModesWave_intervalIntegrable _ _ _ τ)
      (fieldModesWave_intervalIntegrable _ _ _ τ),
      fieldModes_inner_integral, fieldModes_inner_integral]
  rw [intervalIntegral.integral_congr fun τ _ => hin τ]
  rw [intervalIntegral.integral_finsetSum (f := fun i τ =>
    (c i * if b i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) *
      Complex.exp (((2 * Real.pi * (a i : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
    (d i * if b' i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) *
      Complex.exp (((2 * Real.pi * (a' i : ℝ) * τ : ℝ) : ℂ) * Complex.I)) fun i _ =>
    ((continuous_const.mul (fieldModes_time_continuous _)).add
      (continuous_const.mul (fieldModes_time_continuous _))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_add (fieldModes_time_intervalIntegrable _ _)
    (fieldModes_time_intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fieldModes_time_integral, fieldModes_time_integral, fieldModes_delta, fieldModes_delta]

theorem fieldModes_realPart_apply (v : Fin 3 → ℂ) (j : Fin 3) : realPartVec v j = (v j).re := rfl

theorem fieldModes_rotate_mul (φ : ℝ) (c : ℂ) (u : Fin 3 → ℂ) :
    rotateVec φ (fun j => c * u j) = fun j => c * rotateVec φ u j := by
  funext j
  fin_cases j <;> simp [rotateVec] <;> ring

theorem fieldModes_rotate_sum {ι : Type*} (φ : ℝ) (s : Finset ι) (f : ι → Fin 3 → ℂ) :
    rotateVec φ (fun j => ∑ κ ∈ s, f κ j) = ∑ κ ∈ s, rotateVec φ (f κ) := by
  funext j
  rw [Finset.sum_apply]
  fin_cases j <;> simp [rotateVec, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem fieldModes_unrotate_re (φ : ℝ) (u : Fin 3 → ℂ) (i : Fin 3) :
    axialRot (-φ) (realPartVec (rotateVec φ u)) i = (u i).re := by
  have h0 : axialRot (-φ) (realPartVec (rotateVec φ u)) 0 = (u 0).re := by
    rw [rot_apply_zero, fieldModes_realPart_apply, fieldModes_realPart_apply]
    simp only [rotateVec, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.sub_re, Complex.add_re,
      Complex.re_ofReal_mul, Real.cos_neg, Real.sin_neg]
    linear_combination (u 0).re * Real.sin_sq_add_cos_sq φ
  have h1 : axialRot (-φ) (realPartVec (rotateVec φ u)) 1 = (u 1).re := by
    rw [rot_apply_one, fieldModes_realPart_apply, fieldModes_realPart_apply]
    simp only [rotateVec, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.sub_re, Complex.add_re,
      Complex.re_ofReal_mul, Real.cos_neg, Real.sin_neg]
    linear_combination (u 1).re * Real.sin_sq_add_cos_sq φ
  have h2 : axialRot (-φ) (realPartVec (rotateVec φ u)) 2 = (u 2).re := by
    rw [rot_apply_two, fieldModes_realPart_apply]
    rfl
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem fieldModes_pointwise (hT : KeyTimeShift) (hR : KeyRotation) (P : ShapeParams) (D : TimeFieldData)
    (hD : IsTimeFieldData D) (σ τ φ : ℝ) (y : Space) (i : Fin 3) :
    ((axialRot (-φ) (shapeInfoField P D (σ + τ) (axialRot φ y)) i : ℝ) : ℂ) =
      (((∑ κ ∈ D.keys, fieldModesWave (labelTime κ.label) (labelAzimuth P.azimuthOrder κ.label) τ φ *
        keyVector P κ (D.amp κ) σ y i).re : ℝ) : ℂ) := by
  have hk : ∀ κ ∈ D.keys, keyVector P κ (D.amp κ) (σ + τ) (axialRot φ y) =
      rotateVec φ (fun j => fieldModesWave (labelTime κ.label) (labelAzimuth P.azimuthOrder κ.label) τ φ *
        keyVector P κ (D.amp κ) σ y j) := by
    intro κ hκ
    rw [hR P D κ (σ + τ) φ y hD hκ, hT P κ (D.amp κ) σ τ y, fieldModes_rotate_mul, fieldModes_rotate_mul,
      fieldModesWave_split]
    funext j
    ring
  have hc : complexField P D (σ + τ) (axialRot φ y) =
      rotateVec φ (fun j => ∑ κ ∈ D.keys,
        fieldModesWave (labelTime κ.label) (labelAzimuth P.azimuthOrder κ.label) τ φ *
          keyVector P κ (D.amp κ) σ y j) := by
    rw [fieldModes_rotate_sum φ D.keys (fun κ j =>
      fieldModesWave (labelTime κ.label) (labelAzimuth P.azimuthOrder κ.label) τ φ *
        keyVector P κ (D.amp κ) σ y j)]
    unfold complexField
    exact Finset.sum_congr rfl hk
  show ((axialRot (-φ) (realPartVec (complexField P D (σ + τ) (axialRot φ y))) i : ℝ) : ℂ) = _
  rw [hc, fieldModes_unrotate_re]

theorem fieldModes_negKey_negKey (κ : FieldKey) : κ.negKey.negKey = κ := by
  cases κ
  simp [FieldKey.negKey]

theorem fieldModes_harmonic_neg (m : ℕ) (ι : ℤ × ℤ) : labelHarmonic m (-ι) = -labelHarmonic m ι := by
  ext
  · simp only [labelHarmonic, labelTime, Prod.fst_neg, Prod.snd_neg]
    ring
  · simp only [labelHarmonic, labelAzimuth, Prod.fst_neg, Prod.snd_neg]
    ring

end Internal

open Internal in
theorem fieldModeFormula_of (hT : KeyTimeShift) (hR : KeyRotation) (hC : KeyConjugate) : FieldModeFormula := by
  intro P D _ hD ξ σ y
  funext i
  rw [Finset.sum_apply]
  unfold keysOfHarmonic
  rw [Finset.sum_filter]
  set m := P.azimuthOrder with hm
  have hpt : ∀ τ φ : ℝ, Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
      ((axialRot (-φ) (shapeInfoField P D (σ + τ) (axialRot φ y)) i : ℝ) : ℂ) =
      ∑ κ ∈ D.keys, ((keyVector P κ (D.amp κ) σ y i / 2) *
          fieldModesWave (labelTime κ.label - ξ.1) (labelAzimuth m κ.label - ξ.2) τ φ +
        (starRingEnd ℂ (keyVector P κ (D.amp κ) σ y i) / 2) *
          fieldModesWave (-labelTime κ.label - ξ.1) (-labelAzimuth m κ.label - ξ.2) τ φ) := by
    intro τ φ
    rw [fieldModes_pointwise hT hR P D hD σ τ φ y i, Complex.re_eq_add_conj, map_sum]
    have e0 : Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) =
        fieldModesWave (-ξ.1) (-ξ.2) τ φ := by
      unfold fieldModesWave
      congr 1
      push_cast
      ring
    rw [e0, ← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [map_mul, fieldModesWave_conj,
      show labelTime κ.label - ξ.1 = -ξ.1 + labelTime κ.label by ring,
      show labelAzimuth m κ.label - ξ.2 = -ξ.2 + labelAzimuth m κ.label by ring,
      show -labelTime κ.label - ξ.1 = -ξ.1 + -labelTime κ.label by ring,
      show -labelAzimuth m κ.label - ξ.2 = -ξ.2 + -labelAzimuth m κ.label by ring,
      ← fieldModesWave_mul, ← fieldModesWave_mul]
    ring
  have hmv : modeVel ξ (shapeInfoField P D) σ y i = (1 / (2 * Real.pi) : ℂ) *
      ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
          ((axialRot (-φ) (shapeInfoField P D (σ + τ) (axialRot φ y)) i : ℝ) : ℂ) := rfl
  rw [hmv, intervalIntegral.integral_congr fun τ _ =>
    intervalIntegral.integral_congr fun φ _ => hpt τ φ, fieldModes_double_integral]
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
  have hsplit : ∀ κ : FieldKey, (1 / (2 * Real.pi) : ℂ) *
      ((if labelTime κ.label - ξ.1 = 0 ∧ labelAzimuth m κ.label - ξ.2 = 0 then
          ((2 * Real.pi : ℝ) : ℂ) * (keyVector P κ (D.amp κ) σ y i / 2) else 0) +
        (if -labelTime κ.label - ξ.1 = 0 ∧ -labelAzimuth m κ.label - ξ.2 = 0 then
          ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ (keyVector P κ (D.amp κ) σ y i) / 2) else 0)) =
      (if labelHarmonic m κ.label = ξ then keyVector P κ (D.amp κ) σ y i / 2 else 0) +
        (if labelHarmonic m κ.label = -ξ then starRingEnd ℂ (keyVector P κ (D.amp κ) σ y i) / 2 else 0) := by
    intro κ
    have hc1 : (labelTime κ.label - ξ.1 = 0 ∧ labelAzimuth m κ.label - ξ.2 = 0) ↔
        labelHarmonic m κ.label = ξ := by
      rw [Prod.ext_iff]
      simp only [labelHarmonic, sub_eq_zero]
    have hc2 : (-labelTime κ.label - ξ.1 = 0 ∧ -labelAzimuth m κ.label - ξ.2 = 0) ↔
        labelHarmonic m κ.label = -ξ := by
      rw [Prod.ext_iff]
      simp only [labelHarmonic, Prod.fst_neg, Prod.snd_neg]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    have key : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
      push_cast
      have hπ' : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast hπ
      field_simp
    have hfac : ∀ (p q : Prop) [Decidable p] [Decidable q] (u v : ℂ),
        (1 / (2 * Real.pi) : ℂ) * ((if p then ((2 * Real.pi : ℝ) : ℂ) * u else 0) +
          (if q then ((2 * Real.pi : ℝ) : ℂ) * v else 0)) =
        ((1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) * ((if p then u else 0) + (if q then v else 0)) := by
      intro p q _ _ u v
      split_ifs <;> ring
    rw [hfac, key, one_mul]
    simp only [hc1, hc2]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun κ _ => hsplit κ, Finset.sum_add_distrib]
  have hneg : ∑ κ ∈ D.keys,
      (if labelHarmonic m κ.label = -ξ then starRingEnd ℂ (keyVector P κ (D.amp κ) σ y i) / 2 else 0) =
      ∑ κ ∈ D.keys, (if labelHarmonic m κ.label = ξ then keyVector P κ (D.amp κ) σ y i / 2 else 0) := by
    refine Finset.sum_nbij' FieldKey.negKey FieldKey.negKey (fun κ hκ => (hD.keys_neg κ).1 hκ)
      (fun κ hκ => (hD.keys_neg κ).1 hκ) (fun κ _ => fieldModes_negKey_negKey κ)
      (fun κ _ => fieldModes_negKey_negKey κ) fun κ hκ => ?_
    have hv := congrFun (hC P D κ σ y hD hκ) i
    have hl : labelHarmonic m κ.negKey.label = -labelHarmonic m κ.label := fieldModes_harmonic_neg m κ.label
    rw [hv, hl]
    by_cases h : labelHarmonic m κ.label = -ξ
    · rw [if_pos h, if_pos (by rw [h, neg_neg])]
    · rw [if_neg h, if_neg fun h' => h (by rw [← h', neg_neg])]
  rw [hneg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs <;> ring

theorem fieldModeFormula : FieldModeFormula :=
  fieldModeFormula_of keyTimeShift_holds keyRotation keyConjugate

end GivenShape

end CertCell

end Breakdown
