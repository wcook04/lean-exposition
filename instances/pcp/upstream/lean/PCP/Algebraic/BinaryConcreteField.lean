/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryWordArithmetic
import PCP.Algebraic.BinaryQuotientModel
import PCP.Algebraic.FiniteFieldInverse
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Algebra.ZMod

/-!
# A computable binary field with explicit coefficient coordinates

Elements are fixed-length coefficient words. Multiplication uses reduced shifts
for the computed irreducible polynomial, and inversion uses repeated multiplication.
The polynomial quotient is used only to prove the field axioms. No quotient
representative or chosen basis is consulted by the operations or coordinates.
This file proves the field structure and coordinate identities. The production
verifier uses the materialized field implementation with binary powering; its
concrete machine-time certificate is `PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.BinaryConcreteField


/-- A wrapper separates reduced field multiplication from pointwise word multiplication. -/
@[ext] structure Element (t : ℕ) where
  coefficients : Fin t → ZMod 2
  deriving DecidableEq

/-- Forget the wrapper without any enumeration or choice. -/
def coefficientEquiv (t : ℕ) : Element t ≃ (Fin t → ZMod 2) where
  toFun := Element.coefficients
  invFun := Element.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (t : ℕ) : Fintype (Element t) := Fintype.ofEquiv _ (coefficientEquiv t).symm

@[simp] theorem card_element (t : ℕ) : Fintype.card (Element t) = 2 ^ t := by
  rw [Fintype.card_congr (coefficientEquiv t)]
  simp

instance (t : ℕ) : Zero (Element t) := ⟨⟨0⟩⟩
instance (t : ℕ) : One (Element t) := ⟨⟨BinaryWordArithmetic.one t⟩⟩
instance (t : ℕ) : Add (Element t) := ⟨fun a b => ⟨a.coefficients + b.coefficients⟩⟩
instance (t : ℕ) : Neg (Element t) := ⟨fun a => ⟨-a.coefficients⟩⟩

variable {t : ℕ} [NeZero t]

private theorem positive : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)

instance : Mul (Element t) :=
  ⟨fun a b => ⟨BinaryWordArithmetic.mul positive (BinaryQuotientModel.lowerCoefficients t positive)
    a.coefficients b.coefficients⟩⟩

instance : Inv (Element t) := ⟨FiniteFieldInverse.inverse (2 ^ t)⟩

/-- The semantic reference map is used only in correctness proofs. -/
noncomputable def modelMap (a : Element t) : BinaryQuotientModel.Model t positive :=
  BinaryQuotientModel.toModel t positive a.coefficients

theorem modelMap_injective : Function.Injective (modelMap (t := t)) := by
  intro a b h
  exact Element.ext (BinaryQuotientModel.toModel_injective t positive h)

@[simp] theorem modelMap_zero : modelMap (0 : Element t) = 0 :=
  BinaryWordArithmetic.evalWord_zero _

@[simp] theorem modelMap_one : modelMap (1 : Element t) = 1 :=
  BinaryWordArithmetic.evalWord_one _ positive

@[simp] theorem modelMap_add (a b : Element t) :
    modelMap (a + b) = modelMap a + modelMap b := BinaryWordArithmetic.evalWord_add _ _ _

@[simp] theorem modelMap_neg (a : Element t) : modelMap (-a) = -modelMap a :=
  BinaryWordArithmetic.evalWord_neg _ _

@[simp] theorem modelMap_mul (a b : Element t) :
    modelMap (a * b) = modelMap a * modelMap b :=
  BinaryWordArithmetic.evalWord_mul _ positive _ _ _ (BinaryQuotientModel.root_relation t positive)

private theorem model_card : Nat.card (BinaryQuotientModel.Model t positive) = 2 ^ t := by
  rw [Nat.card_eq_fintype_card, BinaryQuotientModel.card_model]

@[simp] theorem modelMap_inv (a : Element t) : modelMap a⁻¹ = (modelMap a)⁻¹ :=
  FiniteFieldInverse.map_inverse modelMap modelMap_injective modelMap_zero modelMap_one
    modelMap_mul model_card a

/-- Every data field is computable; the abstract quotient supplies only the proofs. -/
instance instField : Field (Element t) :=
  Field.ofMinimalAxioms (Element t)
    (fun a b c => modelMap_injective (by simp only [modelMap_add, add_assoc]))
    (fun a => modelMap_injective (by simp only [modelMap_add, modelMap_zero, zero_add]))
    (fun a => modelMap_injective (by simp only
      [modelMap_add, modelMap_neg, modelMap_zero, neg_add_cancel]))
    (fun a b c => modelMap_injective (by simp only [modelMap_mul, mul_assoc]))
    (fun a b => modelMap_injective (by simp only [modelMap_mul, mul_comm]))
    (fun a => modelMap_injective (by simp only [modelMap_mul, modelMap_one, one_mul]))
    (fun a ha => FiniteFieldInverse.mul_inverse_cancel modelMap modelMap_injective
      modelMap_zero modelMap_one modelMap_mul model_card ha)
    (FiniteFieldInverse.inverse_zero _)
    (fun a b c => modelMap_injective (by simp only [modelMap_add, modelMap_mul, mul_add]))
    ⟨0, 1, fun h => zero_ne_one (by
      simpa only [modelMap_zero, modelMap_one] using congrArg (modelMap (t := t)) h)⟩

/-- A bundled semantic map for transporting characteristic and algebraic facts. -/
noncomputable def modelHom : Element t →+* BinaryQuotientModel.Model t positive where
  toFun := modelMap
  map_zero' := modelMap_zero
  map_one' := modelMap_one
  map_add' := modelMap_add
  map_mul' := modelMap_mul

instance : CharP (Element t) 2 :=
  (modelHom (t := t)).charP modelMap_injective 2

/-- Binary scalar multiplication acts directly on the coefficient cells. -/
instance : SMul (ZMod 2) (Element t) := ⟨fun c a => ⟨c • a.coefficients⟩⟩

instance : Module (ZMod 2) (Element t) :=
  Function.Injective.module (R := ZMod 2)
    { toFun := Element.coefficients
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (coefficientEquiv t).injective (fun _ _ => rfl)

instance : Algebra (ZMod 2) (Element t) := ZMod.algebraOfModule 2 (Element t)

/-- Field coordinates are the stored coefficient word itself. -/
def coordinates (t : ℕ) [NeZero t] : Element t ≃ₗ[ZMod 2] (Fin t → ZMod 2) where
  toEquiv := coefficientEquiv t
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem coordinates_apply (a : Element t) : coordinates t a = a.coefficients := rfl

@[simp] theorem coordinates_symm_apply (v : Fin t → ZMod 2) :
    (coordinates t).symm v = Element.mk v := rfl

end PCP.Algebraic.BinaryConcreteField
