/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryWordMaterialization

/-!
# A binary extension field with materialized coefficient arrays

Each element owns a fixed-length array. Addition, multiplication and scalar
multiplication store their coefficient results; inversion uses materialized binary
powering. The earlier concrete field supplies only the algebraic-law proofs.
Coordinates read the array directly and their inverse stores every supplied bit.

This implementation prevents recursive reevaluation of function-valued coefficient
expressions. It does not assert a compiled-code or concrete-machine time bound.
-/

namespace PCP.Algebraic.BinaryMaterializedField

/-- A wrapper gives reduced field operations to a stored coefficient array. -/
@[ext] structure Element (t : ℕ) where
  coefficients : BinaryWordMaterialization.Word t
  deriving DecidableEq

/-- Expose the stored cells in increasing-degree order. -/
def coefficientEquiv (t : ℕ) : Element t ≃ (Fin t → ZMod 2) where
  toFun a := BinaryWordMaterialization.toWord a.coefficients
  invFun v := ⟨BinaryWordMaterialization.ofWord v⟩
  left_inv a := by cases a; simp
  right_inv v := BinaryWordMaterialization.toWord_ofWord v

instance (t : ℕ) : Fintype (Element t) := Fintype.ofEquiv _ (coefficientEquiv t).symm

@[simp] theorem card_element (t : ℕ) : Fintype.card (Element t) = 2 ^ t := by
  rw [Fintype.card_congr (coefficientEquiv t)]
  simp

instance (t : ℕ) : Zero (Element t) := ⟨⟨BinaryWordMaterialization.zero t⟩⟩
instance (t : ℕ) : One (Element t) := ⟨⟨BinaryWordMaterialization.one t⟩⟩
instance (t : ℕ) : Add (Element t) :=
  ⟨fun a b => ⟨BinaryWordMaterialization.add a.coefficients b.coefficients⟩⟩
instance (t : ℕ) : Neg (Element t) := ⟨id⟩

/-- The reference concrete field is used only to prove algebraic laws. -/
def reference {t : ℕ} (a : Element t) : BinaryConcreteField.Element t :=
  BinaryWordMaterialization.toField a.coefficients

theorem reference_injective {t : ℕ} : Function.Injective (reference (t := t)) := by
  intro a b h
  apply Element.ext
  exact BinaryWordMaterialization.toField_injective h

@[simp] theorem reference_zero (t : ℕ) : reference (0 : Element t) = 0 :=
  BinaryWordMaterialization.toField_zero

@[simp] theorem reference_one (t : ℕ) : reference (1 : Element t) = 1 :=
  BinaryWordMaterialization.toField_one

@[simp] theorem reference_add {t : ℕ} (a b : Element t) :
    reference (a + b) = reference a + reference b :=
  BinaryWordMaterialization.toField_add _ _

@[simp] theorem reference_neg {t : ℕ} (a : Element t) : reference (-a) = -reference a := by
  apply BinaryConcreteField.Element.ext
  funext i
  change BinaryWordMaterialization.toWord a.coefficients i =
    -BinaryWordMaterialization.toWord a.coefficients i
  simp

variable {t : ℕ} [NeZero t]

instance : Mul (Element t) :=
  ⟨fun a b => ⟨BinaryWordMaterialization.fieldMul a.coefficients b.coefficients⟩⟩

instance : Inv (Element t) := ⟨fun a => ⟨BinaryWordMaterialization.inverse a.coefficients⟩⟩

@[simp] theorem reference_mul (a b : Element t) :
    reference (a * b) = reference a * reference b :=
  BinaryWordMaterialization.toField_fieldMul _ _

@[simp] theorem reference_inv (a : Element t) : reference a⁻¹ = (reference a)⁻¹ :=
  BinaryWordMaterialization.toField_inverse _

/-- Every computational field operation uses stored coefficient arrays. -/
instance instField : Field (Element t) :=
  Field.ofMinimalAxioms (Element t)
    (fun a b c => reference_injective (by simp only [reference_add, add_assoc]))
    (fun a => reference_injective (by simp only [reference_add, reference_zero, zero_add]))
    (fun a => reference_injective (by simp only
      [reference_add, reference_neg, reference_zero, neg_add_cancel]))
    (fun a b c => reference_injective (by simp only [reference_mul, mul_assoc]))
    (fun a b => reference_injective (by simp only [reference_mul, mul_comm]))
    (fun a => reference_injective (by simp only [reference_mul, reference_one, one_mul]))
    (fun a ha => reference_injective (by
      have h : reference a ≠ 0 := fun h => ha
        (reference_injective (h.trans (reference_zero t).symm))
      simp only [reference_mul, reference_inv, reference_one, mul_inv_cancel₀ h]))
    (reference_injective (by simp only [reference_inv, reference_zero, inv_zero]))
    (fun a b c => reference_injective (by simp only [reference_add, reference_mul, mul_add]))
    ⟨0, 1, fun h => zero_ne_one (by
      simpa only [reference_zero, reference_one] using congrArg reference h)⟩

/-- The law-proving map into the earlier concrete field. -/
def referenceHom : Element t →+* BinaryConcreteField.Element t where
  toFun := reference
  map_zero' := reference_zero t
  map_one' := reference_one t
  map_add' := reference_add
  map_mul' := reference_mul

instance : CharP (Element t) 2 :=
  (referenceHom (t := t)).charP reference_injective 2

/-- Scalar multiplication materializes each scaled binary coefficient. -/
instance : SMul (ZMod 2) (Element t) :=
  ⟨fun c a => ⟨BinaryWordMaterialization.scale c a.coefficients⟩⟩

instance : Module (ZMod 2) (Element t) :=
  Function.Injective.module (R := ZMod 2)
    { toFun := coefficientEquiv t
      map_zero' := BinaryWordMaterialization.toWord_zero
      map_add' := fun a b => BinaryWordMaterialization.toWord_add a.coefficients b.coefficients }
    (coefficientEquiv t).injective
    (fun c a => BinaryWordMaterialization.toWord_scale c a.coefficients)

instance : Algebra (ZMod 2) (Element t) := ZMod.algebraOfModule 2 (Element t)

/-- Direct array reads and materialization are inverse binary linear coordinates. -/
def coordinates (t : ℕ) [NeZero t] : Element t ≃ₗ[ZMod 2] (Fin t → ZMod 2) where
  toEquiv := coefficientEquiv t
  map_add' a b := BinaryWordMaterialization.toWord_add a.coefficients b.coefficients
  map_smul' c a := BinaryWordMaterialization.toWord_scale c a.coefficients

@[simp] theorem coordinates_apply (a : Element t) :
    coordinates t a = BinaryWordMaterialization.toWord a.coefficients := rfl

@[simp] theorem coordinates_symm_apply (v : Fin t → ZMod 2) :
    (coordinates t).symm v = ⟨BinaryWordMaterialization.ofWord v⟩ := rfl

end PCP.Algebraic.BinaryMaterializedField
