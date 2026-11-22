/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardComposition
import PCP.Algebraic.BinaryPolynomialEmbedding

/-!
# Absorbing field weights into homogeneous Hadamard queries

Multiplication by a known field scalar is binary linear. Its transpose acts on
the binary coefficient labels of homogeneous Hadamard queries. Nonzero scalars
permute these labels, preserving uniform error probabilities; zero scalars give
the zero label. Weighted field equations can therefore be checked by an ordinary
sum of binary answers at the transformed labels.
-/

namespace PCP.Algebraic.HadamardWeights

open Finset BinaryPolynomialSpace Hadamard

variable {t r : ℕ}

theorem linearEncode_comm (x w : Fin t → ZMod 2) : linearEncode x w = linearEncode w x := by
  simp only [linearEncode_apply, mul_comm]

@[simp] theorem linearEncode_single_left (i : Fin t) (w : Fin t → ZMod 2) :
    linearEncode (Pi.single i 1) w = w i := by
  rw [linearEncode_comm, linearEncode_single]

/-- Homogeneous query labels are determined by their values on all messages. -/
theorem label_ext {w z : Fin t → ZMod 2}
    (h : ∀ x, linearEncode x w = linearEncode x z) : w = z := by
  funext i
  simpa only [linearEncode_single_left] using h (Pi.single i 1)

/-- The transpose action of a binary linear message map on homogeneous query labels. -/
noncomputable def pullbackLabel (T : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2) where
  toFun w i := linearEncode (T (Pi.single i 1)) w
  map_add' w z := by ext i; simp
  map_smul' a w := by ext i; simp

/-- Pulling back a label is equivalent to applying the message map before evaluation. -/
theorem linearEncode_pullbackLabel
    (T : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) (x w : Fin t → ZMod 2) :
    linearEncode x (pullbackLabel T w) = linearEncode (T x) w := by
  have hx : x = ∑ i : Fin t, x i • Pi.single i (1 : ZMod 2) := by
    funext j
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  have hmap : linearEncode w (T x) =
      ∑ i : Fin t, x i * linearEncode w (T (Pi.single i 1)) := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ = ∑ i : Fin t, x i * linearEncode (T (Pi.single i 1)) w := by
      rw [linearEncode_apply]
      rfl
    _ = ∑ i : Fin t, x i * linearEncode w (T (Pi.single i 1)) := by
      simp only [linearEncode_comm]
    _ = linearEncode w (T x) := hmap.symm
    _ = _ := linearEncode_comm _ _

@[simp] theorem pullbackLabel_id (w : Fin t → ZMod 2) :
    pullbackLabel (LinearMap.id : (Fin t → ZMod 2) →ₗ[ZMod 2] _) w = w := by
  apply label_ext
  intro x
  simp only [linearEncode_pullbackLabel, LinearMap.id_apply]

theorem pullbackLabel_comp
    (S T : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) (w : Fin t → ZMod 2) :
    pullbackLabel S (pullbackLabel T w) = pullbackLabel (T.comp S) w := by
  apply label_ext
  intro x
  simp only [linearEncode_pullbackLabel, LinearMap.comp_apply]

section Field

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- Multiplication by a field weight, expressed in the chosen binary coordinates. -/
noncomputable def coordinateScale (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2) :=
  ρ.toLinearMap.comp ((LinearMap.mulLeft (ZMod 2) a).comp ρ.symm.toLinearMap)

@[simp] theorem coordinateScale_apply (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : F) (x : Fin t → ZMod 2) : coordinateScale ρ a x = ρ (a * ρ.symm x) := rfl

/-- The actual binary coefficient label for an observation of a weighted field value. -/
noncomputable def scaleLabel (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2) :=
  pullbackLabel (coordinateScale ρ a)

theorem linearEncode_scaleLabel (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a y : F) (w : Fin t → ZMod 2) :
    linearEncode (ρ y) (scaleLabel ρ a w) = linearEncode (ρ (a * y)) w := by
  simp only [scaleLabel, linearEncode_pullbackLabel, coordinateScale_apply,
    LinearEquiv.symm_apply_apply]

@[simp] theorem scaleLabel_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (w : Fin t → ZMod 2) : scaleLabel ρ 0 w = 0 := by
  apply label_ext
  intro x
  change linearEncode x (pullbackLabel (coordinateScale ρ 0) w) = linearEncode x 0
  rw [linearEncode_pullbackLabel, coordinateScale_apply, zero_mul, map_zero]
  simp only [linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero]

@[simp] theorem scaleLabel_one (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (w : Fin t → ZMod 2) : scaleLabel ρ 1 w = w := by
  apply label_ext
  intro x
  simp only [scaleLabel, linearEncode_pullbackLabel, coordinateScale_apply, one_mul,
    LinearEquiv.apply_symm_apply]

theorem scaleLabel_mul (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a b : F) (w : Fin t → ZMod 2) :
    scaleLabel ρ a (scaleLabel ρ b w) = scaleLabel ρ (a * b) w := by
  apply label_ext
  intro x
  simp only [scaleLabel, linearEncode_pullbackLabel, coordinateScale_apply,
    LinearEquiv.symm_apply_apply]
  rw [mul_left_comm b a, ← mul_assoc]

/-- A nonzero field weight permutes the uniformly sampled homogeneous labels. -/
noncomputable def scaleLabelEquiv (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : F) (ha : a ≠ 0) : (Fin t → ZMod 2) ≃ₗ[ZMod 2] (Fin t → ZMod 2) where
  __ := scaleLabel ρ a
  invFun := scaleLabel ρ a⁻¹
  left_inv w := by
    change scaleLabel ρ a⁻¹ (scaleLabel ρ a w) = w
    rw [scaleLabel_mul, inv_mul_cancel₀ ha, scaleLabel_one]
  right_inv w := by
    change scaleLabel ρ a (scaleLabel ρ a⁻¹ w) = w
    rw [scaleLabel_mul, mul_inv_cancel₀ ha, scaleLabel_one]

@[simp] theorem scaleLabelEquiv_apply (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : F) (ha : a ≠ 0) (w : Fin t → ZMod 2) :
    scaleLabelEquiv ρ a ha w = scaleLabel ρ a w := rfl

/-- Arbitrary words have unchanged normalized distance after nonzero weight transport. -/
theorem relativeDistance_scaleLabel {A : Type*} [DecidableEq A]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F) (ha : a ≠ 0)
    (f g : (Fin t → ZMod 2) → A) :
    relativeDistance (fun w => f (scaleLabel ρ a w)) (fun w => g (scaleLabel ρ a w)) =
      relativeDistance f g :=
  relativeDistance_comp_equiv (scaleLabelEquiv ρ a ha).toEquiv f g

/-- A weighted field evaluation uses one homogeneous query in the original oracle domain. -/
theorem encode_scaled_homogeneousIndex (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : F) (w : Fin t → ZMod 2) :
    encode r (ρ y) (homogeneousIndex hr (scaleLabel ρ a w)) =
      linearEncode (ρ (a * y)) w := by
  rw [encode_homogeneousIndex, linearEncode_scaleLabel]

/-- Zero coefficients return zero directly, bypassing a potentially corrupted zero query. -/
noncomputable def weightedRead (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Coefficients t r → ZMod 2)
    (a : F) (w : Fin t → ZMod 2) : ZMod 2 := by
  classical
  exact if a = 0 then 0 else H (homogeneousIndex hr (scaleLabel ρ a w))

@[simp] theorem weightedRead_zero (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Coefficients t r → ZMod 2)
    (w : Fin t → ZMod 2) : weightedRead hr ρ H 0 w = 0 := by
  simp [weightedRead]

theorem weightedRead_of_ne (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Coefficients t r → ZMod 2)
    (a : F) (ha : a ≠ 0) (w : Fin t → ZMod 2) :
    weightedRead hr ρ H a w = H (homogeneousIndex hr (scaleLabel ρ a w)) := by
  simp [weightedRead, ha]

/-- The zero-safe read has the intended value on every honest encoding, for every weight. -/
theorem weightedRead_encode (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : F) (w : Fin t → ZMod 2) :
    weightedRead hr ρ (encode r (ρ y)) a w = linearEncode (ρ (a * y)) w := by
  by_cases ha : a = 0
  · subst a
    simp only [weightedRead_zero, zero_mul, map_zero, linearEncode_apply,
      Pi.zero_apply, zero_mul, sum_const_zero]
  · rw [weightedRead_of_ne hr ρ _ a ha, encode_scaled_homogeneousIndex]

/-- Nonzero-weight reads preserve the error rate on homogeneous queries exactly. -/
theorem relativeDistance_weightedRead_of_ne (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H G : Coefficients t r → ZMod 2)
    (a : F) (ha : a ≠ 0) :
    relativeDistance (weightedRead hr ρ H a) (weightedRead hr ρ G a) =
      relativeDistance (fun w => H (homogeneousIndex hr w))
        (fun w => G (homogeneousIndex hr w)) := by
  have hH : weightedRead hr ρ H a =
      fun w => H (homogeneousIndex hr (scaleLabel ρ a w)) :=
    funext (weightedRead_of_ne hr ρ H a ha)
  have hG : weightedRead hr ρ G a =
      fun w => G (homogeneousIndex hr (scaleLabel ρ a w)) :=
    funext (weightedRead_of_ne hr ρ G a ha)
  rw [hH, hG]
  exact relativeDistance_scaleLabel ρ a ha
    (fun w => H (homogeneousIndex hr w)) (fun w => G (homogeneousIndex hr w))

/-- Zero-safe weighting never increases a pair of oracles' homogeneous-query error rate. -/
theorem relativeDistance_weightedRead_le (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H G : Coefficients t r → ZMod 2) (a : F) :
    relativeDistance (weightedRead hr ρ H a) (weightedRead hr ρ G a) ≤
      relativeDistance (fun w => H (homogeneousIndex hr w))
        (fun w => G (homogeneousIndex hr w)) := by
  by_cases ha : a = 0
  · subst a
    have hH : weightedRead hr ρ H 0 = fun _ => 0 := funext (weightedRead_zero hr ρ H)
    have hG : weightedRead hr ρ G 0 = fun _ => 0 := funext (weightedRead_zero hr ρ G)
    rw [hH, hG, relativeDistance_self]
    exact relativeDistance_nonneg _ _
  · exact (relativeDistance_weightedRead_of_ne hr ρ H G a ha).le

/-- Field weights become label transformations; the verifier still sums binary answers. -/
theorem weighted_sum_identity {I : Type*} [Fintype I] (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : I → F) (w : Fin t → ZMod 2) :
    (∑ i, encode r (ρ (y i)) (homogeneousIndex hr (scaleLabel ρ (a i) w))) =
      linearEncode (ρ (∑ i, a i * y i)) w := by
  simp only [encode_scaled_homogeneousIndex, linearEncode_comm, map_sum]

/-- The weighted check identity also holds for the reads that omit zero-weight queries. -/
theorem weightedRead_sum_identity {I : Type*} [Fintype I] (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : I → F) (w : Fin t → ZMod 2) :
    (∑ i, weightedRead hr ρ (encode r (ρ (y i))) (a i) w) =
      linearEncode (ρ (∑ i, a i * y i)) w := by
  simp only [weightedRead_encode, linearEncode_comm, map_sum]

/-- The binary check detects a nonzero weighted field residual on exactly half of labels. -/
theorem weighted_sum_rejection_eq_half {I : Type*} [Fintype I] (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : I → F)
    (h : (∑ i, a i * y i) ≠ 0) :
    relativeDistance
      (fun w => ∑ i, encode r (ρ (y i)) (homogeneousIndex hr (scaleLabel ρ (a i) w)))
      (fun _ => 0) = (1 : ℚ) / 2 := by
  simp only [weighted_sum_identity]
  have hρ : ρ (∑ i, a i * y i) ≠ 0 := by
    intro hz
    apply h
    apply ρ.injective
    simpa only [map_zero] using hz
  have hz : (linearEncode (0 : Fin t → ZMod 2) : (Fin t → ZMod 2) → ZMod 2) =
      fun _ => 0 := by
    funext w
    simp only [linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero]
  change relativeDistance (linearEncode (ρ (∑ i, a i * y i))) (fun _ => 0) = (1 : ℚ) / 2
  rw [← hz]
  exact relativeDistance_linearEncode _ _ hρ

theorem weightedRead_sum_rejection_eq_half {I : Type*} [Fintype I] (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a y : I → F)
    (h : (∑ i, a i * y i) ≠ 0) :
    relativeDistance (fun w => ∑ i, weightedRead hr ρ (encode r (ρ (y i))) (a i) w)
      (fun _ => 0) = (1 : ℚ) / 2 := by
  have he : (fun w => ∑ i, weightedRead hr ρ (encode r (ρ (y i))) (a i) w) =
      fun w => ∑ i, encode r (ρ (y i)) (homogeneousIndex hr (scaleLabel ρ (a i) w)) := by
    funext w
    rw [weightedRead_sum_identity, weighted_sum_identity]
  rw [he]
  exact weighted_sum_rejection_eq_half hr ρ a y h

end Field

end PCP.Algebraic.HadamardWeights
