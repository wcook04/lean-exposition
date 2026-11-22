/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryConcreteField
import Init.Data.Vector.OfFn
import Mathlib.Data.Nat.Size

/-!
# Materialized binary coefficient arithmetic

Words are arrays of exactly `t` stored coefficients. Every elementary operation
constructs a new stored array. Multiplication carries an accumulator and a shifted
word through exactly `t` stages, so later coefficient reads access stored results
rather than recursively evaluating a function-valued arithmetic expression.

The function-view and concrete-field equalities certify the arithmetic. No array
access cost, compiled-code running time, or concrete machine bound is asserted.
-/

namespace PCP.Algebraic.BinaryWordMaterialization

/-- A fixed-length array of binary coefficients. -/
abbrev Word (t : ℕ) := Vector (ZMod 2) t

variable {t : ℕ}

/-- Read the stored coefficients as the earlier function representation. -/
def toWord (v : Word t) : BinaryWordArithmetic.Word t := fun i => v[i.val]

/-- Evaluate and store every coefficient of a function representation. -/
def ofWord (v : BinaryWordArithmetic.Word t) : Word t := Vector.ofFn v

@[simp] theorem toWord_ofWord (v : BinaryWordArithmetic.Word t) :
    toWord (ofWord v) = v := by
  funext i
  simp [toWord, ofWord]

@[simp] theorem ofWord_toWord (v : Word t) : ofWord (toWord v) = v := by
  apply Vector.ext
  intro i hi
  simp [ofWord, toWord]

/-- Store the zero coefficient word. -/
def zero (t : ℕ) : Word t := ofWord 0

/-- Store the coefficient word of the constant one. -/
def one (t : ℕ) : Word t := ofWord (BinaryWordArithmetic.one t)

/-- Materialize each coefficient sum once. -/
def add (v w : Word t) : Word t := ofWord (toWord v + toWord w)

/-- Materialize each coefficient product with a scalar once. -/
def scale (a : ZMod 2) (v : Word t) : Word t := ofWord (a • toWord v)

/-- Store the result of one reduction-register shift. -/
def shift (ht : 0 < t) (m v : Word t) : Word t :=
  ofWord (BinaryWordArithmetic.shift ht (toWord m) (toWord v))

@[simp] theorem toWord_zero : toWord (zero t) = 0 := toWord_ofWord _
@[simp] theorem toWord_one : toWord (one t) = BinaryWordArithmetic.one t := toWord_ofWord _
@[simp] theorem toWord_add (v w : Word t) : toWord (add v w) = toWord v + toWord w :=
  toWord_ofWord _
@[simp] theorem toWord_scale (a : ZMod 2) (v : Word t) :
    toWord (scale a v) = a • toWord v := toWord_ofWord _
@[simp] theorem toWord_shift (ht : 0 < t) (m v : Word t) :
    toWord (shift ht m v) = BinaryWordArithmetic.shift ht (toWord m) (toWord v) :=
  toWord_ofWord _

/-- Process a prefix of coefficients, retaining only the two materialized state words. -/
def mulState (ht : 0 < t) (m v w : Word t) :
    (n : ℕ) → n ≤ t → Word t × Word t
  | 0, _ => (zero t, w)
  | n + 1, hn =>
    let state := mulState ht m v w n (by omega)
    (add state.1 (scale (toWord v ⟨n, by omega⟩) state.2), shift ht m state.2)

/-- Multiply using exactly one stored shift and accumulation per input coefficient. -/
def mul (ht : 0 < t) (m v w : Word t) : Word t := (mulState ht m v w t le_rfl).1

/-- The stored shift register is precisely the indicated iterate. -/
theorem toWord_mulState_snd (ht : 0 < t) (m v w : Word t) (n : ℕ) (hn : n ≤ t) :
    toWord (mulState ht m v w n hn).2 =
      (BinaryWordArithmetic.shift ht (toWord m))^[n] (toWord w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mulState, toWord_shift, ih, Function.iterate_succ_apply']

/-- The stored accumulator contains exactly the processed prefix product. -/
theorem toWord_mulState_fst (ht : 0 < t) (m v w : Word t) (n : ℕ) (hn : n ≤ t) :
    toWord (mulState ht m v w n hn).1 =
      ∑ i : Fin n, toWord v ⟨i.val, by omega⟩ •
        (BinaryWordArithmetic.shift ht (toWord m))^[i.val] (toWord w) := by
  induction n with
  | zero => simp [mulState]
  | succ n ih =>
    simp only [mulState, toWord_add, toWord_scale, ih, toWord_mulState_snd,
      Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- The materialized multiplication is exactly the original coefficient multiplication. -/
@[simp] theorem toWord_mul (ht : 0 < t) (m v w : Word t) :
    toWord (mul ht m v w) =
      BinaryWordArithmetic.mul ht (toWord m) (toWord v) (toWord w) := by
  simpa only [mul, BinaryWordArithmetic.mul] using toWord_mulState_fst ht m v w t le_rfl

/-- Interpret a least-significant-first Boolean exponent list. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

@[simp] theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih => simp only [Nat.bits_append_bit n b hn, bitsValue, ih]

/-- Binary powering retains each materialized square before optionally multiplying
by the base. The second component counts the actual calls to `mul`. -/
def powBits (ht : 0 < t) (m v : Word t) : List Bool → Word t × ℕ
  | [] => (one t, 0)
  | b :: bs =>
    let state := powBits ht m v bs
    let square := mul ht m state.1 state.1
    if b then (mul ht m square v, state.2 + 2) else (square, state.2 + 1)

/-- Materialized repeated squaring over the actual binary exponent digits. -/
def power (ht : 0 < t) (m v : Word t) (n : ℕ) : Word t :=
  (powBits ht m v n.bits).1

/-- Binary powering makes at most two multiplication calls per exponent digit. -/
theorem powBits_multiplications_le (ht : 0 < t) (m v : Word t) (bs : List Bool) :
    (powBits ht m v bs).2 ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [powBits]
  | cons b bs ih => cases b <;> simp only [powBits, Bool.false_eq_true, ite_false,
      ite_true, List.length_cons] <;> omega

/-- The explicit call counter grows linearly in the exponent's binary length.
This is a call count, not a compiled-code or machine-step bound. -/
theorem power_multiplications_le (ht : 0 < t) (m v : Word t) (n : ℕ) :
    (powBits ht m v n.bits).2 ≤ 2 * n.size := by
  simpa only [Nat.size_eq_bits_len] using powBits_multiplications_le ht m v n.bits

/-- Wrap a stored word in the existing concrete field representation. -/
def toField (v : Word t) : BinaryConcreteField.Element t := ⟨toWord v⟩

/-- Materialize the coefficients of an existing concrete field element. -/
def ofField (v : BinaryConcreteField.Element t) : Word t := ofWord v.coefficients

@[simp] theorem toField_ofField (v : BinaryConcreteField.Element t) :
    toField (ofField v) = v := by
  cases v
  simp [toField, ofField]

@[simp] theorem ofField_toField (v : Word t) : ofField (toField v) = v :=
  ofWord_toWord v

@[simp] theorem toField_zero : toField (zero t) = 0 := by
  apply BinaryConcreteField.Element.ext
  exact toWord_zero

@[simp] theorem toField_one : toField (one t) = 1 := by
  apply BinaryConcreteField.Element.ext
  exact toWord_one

@[simp] theorem toField_add (v w : Word t) : toField (add v w) = toField v + toField w := by
  apply BinaryConcreteField.Element.ext
  exact toWord_add v w

section Field

variable [NeZero t]

/-- The chosen irreducible modulus, with all lower coefficients stored once. -/
def modulus (t : ℕ) [NeZero t] : Word t :=
  ofWord (BinaryQuotientModel.lowerCoefficients t (Nat.pos_of_ne_zero (NeZero.ne t)))

/-- Materialized multiplication for the chosen concrete field. -/
def fieldMul (v w : Word t) : Word t :=
  mul (Nat.pos_of_ne_zero (NeZero.ne t)) (modulus t) v w

@[simp] theorem toField_fieldMul (v w : Word t) :
    toField (fieldMul v w) = toField v * toField w := by
  apply BinaryConcreteField.Element.ext
  exact (toWord_mul _ _ v w).trans (by rw [modulus, toWord_ofWord]; rfl)

/-- Multiplication with a stored copy of the chosen modulus agrees with the field. -/
theorem toField_mul_modulus (ht : 0 < t) (m v w : Word t)
    (hm : toWord m = BinaryQuotientModel.lowerCoefficients t ht) :
    toField (mul ht m v w) = toField v * toField w := by
  apply BinaryConcreteField.Element.ext
  exact (toWord_mul ht m v w).trans (by rw [hm]; rfl)

/-- The materialized binary power has exactly the semantic field value. -/
theorem toField_powBits (ht : 0 < t) (m v : Word t)
    (hm : toWord m = BinaryQuotientModel.lowerCoefficients t ht) (bs : List Bool) :
    toField (powBits ht m v bs).1 = toField v ^ bitsValue bs := by
  induction bs with
  | nil => simp [powBits, bitsValue]
  | cons b bs ih =>
    cases b <;> simp only [powBits, Bool.false_eq_true, ite_false, ite_true, bitsValue,
      toField_mul_modulus ht m _ _ hm, ih]
    · simp [Nat.bit_val, pow_mul, pow_two, mul_pow]
    · simp [Nat.bit_val, pow_add, pow_mul, pow_two, mul_pow, mul_assoc]

@[simp] theorem toField_power (ht : 0 < t) (m v : Word t)
    (hm : toWord m = BinaryQuotientModel.lowerCoefficients t ht) (n : ℕ) :
    toField (power ht m v n) = toField v ^ n := by
  simp only [power, toField_powBits ht m v hm, bitsValue_bits]

/-- Powering in the chosen field materializes its modulus only once at entry. -/
def fieldPower (v : Word t) (n : ℕ) : Word t :=
  power (Nat.pos_of_ne_zero (NeZero.ne t)) (modulus t) v n

@[simp] theorem toField_fieldPower (v : Word t) (n : ℕ) :
    toField (fieldPower v n) = toField v ^ n :=
  toField_power _ _ v (toWord_ofWord _) n

/-- Invert by binary powering, with zero handled before any multiplications. -/
def inverse (v : Word t) : Word t :=
  if v = zero t then zero t else fieldPower v (2 ^ t - 2)

omit [NeZero t] in
/-- Array equality and function-view equality describe the same field value. -/
theorem toField_injective : Function.Injective (toField (t := t)) := by
  intro v w h
  simpa only [ofField_toField] using congrArg ofField h

@[simp] theorem toField_inverse (v : Word t) : toField (inverse v) = (toField v)⁻¹ := by
  by_cases hv : v = zero t
  · simp [inverse, hv]
  · have hf : toField v ≠ 0 := by
      intro h
      exact hv (toField_injective (h.trans toField_zero.symm))
    rw [inverse, ite_eq_right hv, toField_fieldPower]
    apply FiniteFieldInverse.pow_card_sub_two_eq_inv _ hf
    rw [Nat.card_eq_fintype_card, BinaryConcreteField.card_element]

end Field

end PCP.Algebraic.BinaryWordMaterialization
