/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialSelection

/-!
# Materializing the selected modulus as a coefficient list

The bit loop repeatedly takes a remainder and quotient by two, storing each bit
before proceeding. Its output is the exact coefficient-list encoding consumed
by the materialized field arithmetic programs.
-/

namespace PCP.Lang.BinaryPolynomialSelector

open PCP.Algebraic BinaryPolynomialCoefficient

/-- A fixed-width, low-bit-first binary word, including leading zero coefficients. -/
def digits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t + 1, n => n % 2 :: digits t (n / 2)

@[simp] theorem digits_length (t n : ℕ) : (digits t n).length = t := by
  induction t generalizing n <;> simp [digits, *]

theorem digits_bits (t n : ℕ) : BinaryField.Bits (digits t n) := by
  induction t generalizing n with
  | zero => simp [digits, BinaryField.Bits]
  | succ t ih =>
    intro x hx
    simp only [digits, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ hx

theorem digits_ofFn (t n : ℕ) :
    digits t n = List.ofFn (fun i : Fin t => n / 2 ^ i.val % 2) := by
  induction t generalizing n with
  | zero => simp [digits]
  | succ t ih =>
    rw [digits, List.ofFn_succ, ih]
    congr 1
    · simp
    · apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ, Nat.div_div_eq_div_mul]
      rw [pow_succ, Nat.mul_comm (2 ^ i.val) 2]

def extractBody : Stmt 36 2 :=
  .seq (.assign 2 (.mod 34 0)) (.seq (.push 1 2) (.assign 34 (.div 34 0)))

theorem extractBody_step (st : State 36 2) (h0 : st.regs 0 = 2) :
    (extractBody.run st).1.lists 1 = st.regs 34 % 2 :: st.lists 1 ∧
      (extractBody.run st).1.regs 34 = st.regs 34 / 2 ∧
      (extractBody.run st).1.regs 0 = 2 := by
  simp [extractBody, Stmt.run, Expr.eval, Function.update, h0]

theorem extract_iterate (c t : ℕ) (st : State 36 2) (n : ℕ) (out : List ℕ)
    (h0 : st.regs 0 = 2) (hn : st.regs 34 = n) (ho : st.lists 1 = out) :
    (iterate extractBody.run c t st).1.lists 1 = (digits t n).reverse ++ out := by
  induction t generalizing st n out with
  | zero => simp [iterate_zero_fst, digits, ho]
  | succ t ih =>
    obtain ⟨hl, hr, htwo⟩ := extractBody_step st h0
    rw [hn] at hr
    rw [hn, ho] at hl
    have h := ih (extractBody.run st).1 (n / 2) (n % 2 :: out) htwo hr hl
    rw [iterate_succ_fst, h]
    simp [digits, List.reverse_cons, List.append_assoc]

/-- Input width `20`, numeric word `33`, and empty list `0`; output stored word `1`. -/
def materialize : Stmt 36 2 :=
  .seq (.copy 0 1) (.seq (.assign 34 (.var 33)) (.seq (.assign 0 (.const 2))
    (.seq (.loop 20 extractBody) (.rev 1))))

theorem materialize_run (st : State 36 2) (h0 : st.lists 0 = []) :
    (materialize.run st).1.lists 1 = digits (st.regs 20) (st.regs 33) := by
  let s := setReg (setReg (setList st 1 []) 34 (st.regs 33)) 0 2
  have hs : (iterate extractBody.run (Nat.size (st.regs 20) + 1) (st.regs 20) s).1.lists 1 =
      (digits (st.regs 20) (st.regs 33)).reverse := by
    simpa using extract_iterate (Nat.size (st.regs 20) + 1) (st.regs 20) s
      (st.regs 33) [] (by simp [s]) (by simp [s, Function.update]) (by simp [s])
  simp only [materialize, Stmt.run, Expr.eval, h0,
    setReg_regs, setList_regs, Function.update, Fin.reduceEq, dite_false]
  change ((iterate extractBody.run (Nat.size (st.regs 20) + 1)
    (st.regs 20) s).1.lists 1).reverse = _
  rw [hs, List.reverse_reverse]

theorem digits_modulus (t : ℕ) [NeZero t] :
    digits t (BinaryIrreduciblePolynomial.selectedCode t
      (Nat.pos_of_ne_zero (NeZero.ne t))).val =
        BinaryField.encode (BinaryWordMaterialization.modulus t) := by
  rw [digits_ofFn, BinaryField.encode, BinaryWordMaterialization.modulus]
  simp only [BinaryWordMaterialization.toWord_ofWord]
  apply congrArg List.ofFn
  funext i
  rw [BinaryQuotientModel.lowerCoefficients_apply, BinaryIrreduciblePolynomial.polynomial_coeff]
  rw [coefficient_value]
  simp [value, i.isLt]

/-- Select and materialize the actual production modulus. -/
def fieldModulus : Stmt 36 2 := .seq selectPolynomial materialize

theorem fieldModulus_run (t : ℕ) [NeZero t] (st : State 36 2)
    (h20 : st.regs 20 = t) (h0 : st.lists 0 = []) :
    (fieldModulus.run st).1.lists 1 =
      BinaryField.encode (BinaryWordMaterialization.modulus t) := by
  have hs33 := selectPolynomial_run t (Nat.pos_of_ne_zero (NeZero.ne t)) st h20
  have hs20 := run_regs_frame selectPolynomial 20 (by decide) st
  have hs0 := run_lists_frame selectPolynomial 0 (by decide) st
  simp only [fieldModulus, run_seq_fst]
  rw [materialize_run _ (hs0.trans h0), hs20, h20, hs33, digits_modulus]

end PCP.Lang.BinaryPolynomialSelector
