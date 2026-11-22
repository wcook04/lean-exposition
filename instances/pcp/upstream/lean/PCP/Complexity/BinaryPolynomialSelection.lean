/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialSelectorCost

/-!
# Uniform language program selecting the binary field modulus

The sole numeric input is the positive extension degree in register `20`.
The program computes `2^t` by counted doubling, then runs the complete least-mask
search. Both parts have charged polynomial cost in the resulting field size.
-/

namespace PCP.Lang.BinaryPolynomialSelector

open PCP.Algebraic

def doubleBody : Stmt 36 2 := .assign 28 (.mul 28 0)

def cardinality : Stmt 36 2 :=
  .seq (.assign 28 (.const 1)) (.seq (.assign 0 (.const 2)) (.loop 20 doubleBody))

theorem doubleBody_step (st : State 36 2) (h0 : st.regs 0 = 2) :
    (doubleBody.run st).1.regs 28 = st.regs 28 * 2 ∧
      (doubleBody.run st).1.regs 0 = 2 := by
  simp [doubleBody, run_assign_fst, Expr.eval, Function.update, h0]

theorem double_iterate (c n : ℕ) (st : State 36 2) (h0 : st.regs 0 = 2) :
    (iterate doubleBody.run c n st).1.regs 28 = st.regs 28 * 2 ^ n := by
  have h := iterate_inv doubleBody.run c n
    (fun j u => u.regs 0 = 2 ∧ u.regs 28 = st.regs 28 * 2 ^ j)
    (by
      intro j u _ hu
      obtain ⟨h28, h0⟩ := doubleBody_step u hu.1
      refine ⟨h0, ?_⟩
      rw [h28, hu.2, pow_succ, Nat.mul_assoc]) st (by simp [h0])
  exact h.2

theorem cardinality_run (st : State 36 2) :
    (cardinality.run st).1.regs 28 = 2 ^ st.regs 20 := by
  simp only [cardinality, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  rw [double_iterate _ _ _ (by simp)]
  simp [Function.update]

theorem cardinality_cost (st : State 36 2) (t : ℕ) (h20 : st.regs 20 = t) :
    (cardinality.run st).2 ≤ 20 * (2 ^ t + 1) ^ 2 := by
  let q := 2 ^ t
  let s := setReg (setReg st 28 1) 0 2
  have hit := iterate_cost_idx doubleBody.run (Nat.size t + 1) (2 * q + 3) t
    (fun j u => u.regs 0 = 2 ∧ u.regs 28 = 2 ^ j)
    (by
      intro j u hj hu
      obtain ⟨h28, h0⟩ := doubleBody_step u hu.1
      refine ⟨⟨h0, by rw [h28, hu.2, pow_succ]⟩, ?_⟩
      have hsz : Nat.size (2 ^ j) ≤ q := (size_le_self _).trans
        (Nat.pow_le_pow_right (by decide) hj.le)
      have hsz' : Nat.size (2 ^ j * 2) ≤ q := (size_le_self _).trans (by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right (by decide) hj)
      simp only [doubleBody, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hu.1, hu.2,
        show Nat.size 2 = 2 from rfl]
      omega) s (by simp [s, Function.update])
  have htq : t ≤ q := (Nat.lt_two_pow_self (n := t)).le
  have hsz : Nat.size t ≤ q := (size_le_self _).trans htq
  have hb : t * (Nat.size t + 1 + (2 * q + 3)) ≤ q * (q + 1 + (2 * q + 3)) :=
    Nat.mul_le_mul htq (by omega)
  have hb' := hit.trans hb
  simp only [cardinality, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, h20]
  change (Expr.const 1).cost st.regs + ((Expr.const 2).cost _ +
    ((iterate doubleBody.run (Nat.size t + 1) t s).2 + Nat.size t + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, show Nat.size 1 = 1 from rfl,
    show Nat.size 2 = 2 from rfl]
  change _ ≤ 20 * (q + 1) ^ 2
  nlinarith

/-- Compute the full modulus address from the degree, with no precomputed field data. -/
def selectPolynomial : Stmt 36 2 := .seq cardinality selectMask

theorem selectPolynomial_run (t : ℕ) (ht : 0 < t) (st : State 36 2)
    (h20 : st.regs 20 = t) :
    (selectPolynomial.run st).1.regs 33 =
      (BinaryIrreduciblePolynomial.selectedCode t ht).val := by
  have h := cardinality_run st
  rw [h20] at h
  exact selectMask_run t ht (cardinality.run st).1
    ((run_regs_frame cardinality 20 (by decide) st).trans h20) h

/-- This is a bound for the actual complete program, including field-size construction. -/
theorem selectPolynomial_cost (t : ℕ) (st : State 36 2) (h20 : st.regs 20 = t) :
    (selectPolynomial.run st).2 ≤ 6000000 * (2 ^ t + 1) ^ 7 := by
  have hcard := cardinality_cost st t h20
  have hs20 := run_regs_frame cardinality 20 (by decide) st
  have hs28 := cardinality_run st
  rw [h20] at hs28
  simp only [selectPolynomial, run_seq_snd]
  generalize hs : (cardinality.run st).1 = s at *
  have hselect := selectMask_cost t s (hs20.trans h20) hs28
  nlinarith [Nat.zero_le ((2 ^ t) ^ 7), Nat.zero_le ((2 ^ t) ^ 6),
    Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
    Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

end PCP.Lang.BinaryPolynomialSelector
