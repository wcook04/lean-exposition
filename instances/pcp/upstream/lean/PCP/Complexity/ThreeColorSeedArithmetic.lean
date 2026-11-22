import PCP.Complexity.ArithmeticExpressionCost
import PCP.Algebraic.ThreeColorSeedIndex

/-!
# Arithmetic expressions for the actual seven sampler radices

These are fixed expressions over the verifier's stored dimensions. Each produces
the exact exponent of two in its structural branch codec, including both unused
fair-choice seeds and all four whole-field correction draws.
-/

namespace PCP.Lang.SeedArithmetic

open ArithmeticExpression PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize

private def add := Term.bin (n := 4) .add
private def mul := Term.bin (n := 4) .mul
private def sub := Term.bin (n := 4) .sub
private def div := Term.bin (n := 4) .div

def chooseTwo : Term 4 := div (mul (.input 3) (sub (.input 3) (.const 1))) (.const 2)
def chooseThree : Term 4 := div
  (mul (mul (.input 3) (sub (.input 3) (.const 1))) (sub (.input 3) (.const 2))) (.const 6)
def coefficientOne : Term 4 := add (.const 1) (.input 3)
def coefficientThree : Term 4 := add (add coefficientOne chooseTwo) chooseThree

def hadamard (cubic : Bool) : Term 4 :=
  if cubic then add (add (add (.const 5) (mul (.const 5) (.input 3)))
    (mul (.const 3) chooseTwo)) (mul (.const 2) chooseThree)
  else mul (.const 3) coefficientOne

def inner : Term 4 := add (add (add (.const 1)
  (mul (mul (.const 3) (.input 3)) (mul (.input 2) (.input 1))))
  (mul (.const 2) (.input 3))) (hadamard false)

def outer (d : Term 4) (cubic : Bool) : Term 4 := add (add (add (add
  (mul (mul (.const 2) (.input 3)) d) (mul (.const 2) (.input 3)))
  (mul (.input 3) (mul (.input 2) (.input 1)))) (hadamard cubic)) inner

def derived (d : Term 4) : Term 4 := add (add (add (add
  (mul (mul (.const 5) (.input 3)) d) (mul (.const 3) (.input 3)))
  (mul (mul (.const 2) (.input 3)) (mul (.input 2) (.input 1))))
  (mul (.const 2) inner)) coefficientThree

def branchTerm : Fin 7 → Term 4 :=
  ![outer (.input 0) true, outer (add (.input 0) (.input 0)) false,
    outer (add (.input 0) (.input 0)) true,
    outer (add (add (.input 0) (.input 0)) (add (.input 0) (.input 0))) false,
    derived (.input 0), derived (add (.input 0) (.input 0)),
    add (mul (mul (.const 2) (.input 3)) (.input 0)) (.input 3)]

def branchBits (n m c t : ℕ) : Fin 7 → ℕ :=
  ![outerBits n m c t 3, outerBits (n + n) m c t 1,
    outerBits (n + n) m c t 3, outerBits ((n + n) + (n + n)) m c t 1,
    derivedBits n m c t 3 + 2 * t, derivedBits (n + n) m c t 3 + 2 * t,
    2 * t * n + t]

theorem chooseThree_eval (v : Fin 4 → ℕ) : chooseThree.eval v = (v 3).choose 3 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [chooseThree, div, mul, sub, Term.eval, Op.eval, Nat.descFactorial_succ,
    Nat.descFactorial_zero, Nat.factorial, Nat.mul_comm, Nat.mul_assoc]

theorem branchTerm_eval (n m c t : ℕ) (i : Fin 7) :
    (branchTerm i).eval ![n, m, c, t] = branchBits n m c t i := by
  have h2 : chooseTwo.eval ![n, m, c, t] = t.choose 2 := by
    simp [chooseTwo, div, mul, sub, Term.eval, Op.eval, Nat.choose_two_right]
  have h3 : chooseThree.eval ![n, m, c, t] = t.choose 3 := chooseThree_eval _
  fin_cases i <;>
    simp [branchTerm, branchBits, outer, inner, derived, hadamard, coefficientOne,
      coefficientThree, add, mul, Term.eval, Op.eval, h2, h3, outerBits, innerBits,
      derivedBits, hadamardBits_one, hadamardBits_three, coefficientBits_three] <;> omega

theorem branchBits_sum (n m c t : ℕ) :
    ∑ i, branchBits n m c t i = rawBits n m c t := by
  simp [branchBits, Fin.sum_univ_succ, rawBits, originalBits, outerBits, derivedBits,
    innerBits, hadamardBits_one, hadamardBits_three, coefficientBits_three]
  ring

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}

/-- The exponents refer to the actual production structural codecs. -/
theorem branchCodec_size (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) (i : Fin 7) :
    (branchCodec ρ n m c i).size = 2 ^ branchBits n m c t i := by
  have hdim (r : ℕ) : BooleanCoefficientIndex.dimension t r = coefficientBits t r := rfl
  fin_cases i
  all_goals first
  | change (outerCodec ρ (Codec.fin n) m c 3).size = 2 ^ outerBits n m c t 3
  | change (outerCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c 1).size =
      2 ^ outerBits (n + n) m c t 1
  | change (outerCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c 3).size =
      2 ^ outerBits (n + n) m c t 3
  | change (outerCodec ρ ((Codec.fin (n + n)).sum (Codec.fin (n + n))) m c 1).size =
      2 ^ outerBits ((n + n) + (n + n)) m c t 1
  | change (derivedCodec ρ n m c 3).size = 2 ^ (derivedBits n m c t 3 + 2 * t)
  | change (derivedCodec ρ (n + n) m c 3).size = 2 ^ (derivedBits (n + n) m c t 3 + 2 * t)
  | change (2 ^ t) ^ n * (2 ^ t) ^ n * 2 ^ t = 2 ^ (2 * t * n + t)
  all_goals
    try simp only [outerCodec, derivedCodec, gridCodec, callCodec, innerCodec,
      innerPointCodec, binaryLowDegreeCodec, hadamardCodec, Codec.prod, Codec.function,
      Codec.piFin, Codec.fin, Codec.sum, boolCodec, fieldCodec, bitsCodec, coefficientCodec]
    simp only [hdim, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceSub,
      Nat.reduceAdd, Fin.prod_univ_zero, Nat.mul_one, coefficientBits_one,
      coefficientBits_two, coefficientBits_three, ← pow_mul, ← pow_add]
    try simp only [← Nat.pow_succ', ← pow_add, outerBits, derivedBits, innerBits,
      hadamardBits_one, hadamardBits_three, coefficientBits_three, Nat.succ_eq_add_one]
    congr 1
    ring

end PCP.Lang.SeedArithmetic
