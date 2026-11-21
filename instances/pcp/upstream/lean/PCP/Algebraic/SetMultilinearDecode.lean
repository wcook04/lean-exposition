/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.SetMultilinear
import PCP.Algebraic.PolynomialLine

/-!
# Degree control when decoding an arbitrary inner polynomial

The soundness proof of binary local correction decodes a nearby polynomial that
need not be set-multilinear. Substitution at the power point still produces an
ordinary univariate polynomial of degree at most `totalDegree * m^c`.
The evaluation identity holds for every polynomial, without an encoding premise.
-/

namespace PCP.Algebraic

open Finset

variable {R σ : Type*} [CommSemiring R]

/-- Substituting univariate polynomials multiplies the ordinary degree bound. -/
theorem natDegree_substitution_le (p : MvPolynomial σ R)
    (q : σ → Polynomial R) (d : ℕ) (hq : ∀ i, (q i).natDegree ≤ d) :
    (MvPolynomial.eval₂Hom Polynomial.C q p).natDegree ≤ p.totalDegree * d := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ s.support, (q i ^ s i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ s.support, s i * d := by
      apply sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hq i))
    _ = (s.sum fun _ n => n) * d := by rw [Finsupp.sum, sum_mul]
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hs)

namespace SetMultilinear

variable (m c : ℕ)

/-- Decoding and evaluating equals evaluation at the power point, even off the code. -/
@[simp] theorem eval_decode (P : MvPolynomial (Variables m c) R) (x : R) :
    (decode m c P).eval x = MvPolynomial.eval (evaluationPoint m c x) P := by
  have h : (Polynomial.evalRingHom x).comp (decode m c) =
      MvPolynomial.eval (evaluationPoint m c x) := by
    ext i <;> simp [decode, evaluationPoint]
  exact congrArg (fun f : MvPolynomial (Variables m c) R →+* R => f P) h

/-- A convenient uniform bound on the exponents in the power substitution. -/
theorem evaluationExponent_le [NeZero m] (i : Variables m c) :
    i.2.val * m ^ i.1.val ≤ m ^ c := by
  calc
    i.2.val * m ^ i.1.val ≤ m * m ^ i.1.val := Nat.mul_le_mul_right _ i.2.isLt.le
    _ = m ^ (i.1.val + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ m ^ c := Nat.pow_le_pow_right (NeZero.pos m) i.1.isLt

/-- Arbitrary inner polynomials decode to degree at most `totalDegree * m^c`. -/
theorem natDegree_decode_le [NeZero m] (P : MvPolynomial (Variables m c) R) :
    (decode m c P).natDegree ≤ P.totalDegree * m ^ c := by
  apply natDegree_substitution_le
  intro i
  exact Polynomial.natDegree_pow_le.trans
    ((Nat.mul_le_mul_left _ Polynomial.natDegree_X_le).trans
      (by simpa using evaluationExponent_le m c i))

/-- The degree bound used for the auxiliary lines table in binary correction. -/
theorem natDegree_decode_le_of_totalDegree_le [NeZero m]
    (P : MvPolynomial (Variables m c) R) {d : ℕ} (hP : P.totalDegree ≤ d) :
    (decode m c P).natDegree ≤ d * m ^ c :=
  (natDegree_decode_le m c P).trans (Nat.mul_le_mul_right _ hP)

end SetMultilinear

end PCP.Algebraic
