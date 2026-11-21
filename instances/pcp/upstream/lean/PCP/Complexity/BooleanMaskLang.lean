/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialMaterializationCost
import PCP.Algebraic.BooleanCoefficientIndex

/-!
# Numeric Boolean coefficient masks in the counted-loop language

The degree of a squarefree monomial is computed by summing the low fixed-width
binary digits of its numeric mask. This is exactly the support-cardinality
condition in the production coefficient index.
-/

namespace PCP.Lang.BooleanMask

open PCP.Algebraic BinaryPolynomialSelector

/-- One low-bit extraction updates a stored population counter. -/
def body : Stmt 6 1 :=
  .seq (.assign 4 (.mod 3 5)) (.seq (.assign 2 (.add 2 4)) (.assign 3 (.div 3 5)))

theorem body_step (st : State 6 1) (h5 : st.regs 5 = 2) :
    (body.run st).1.regs 2 = st.regs 2 + st.regs 3 % 2 ∧
      (body.run st).1.regs 3 = st.regs 3 / 2 ∧ (body.run st).1.regs 5 = 2 := by
  simp [body, Stmt.run, Expr.eval, Function.update, h5]

theorem iterate_result (c n : ℕ) (st : State 6 1) (h5 : st.regs 5 = 2) :
    (iterate body.run c n st).1.regs 2 = st.regs 2 + (digits n (st.regs 3)).sum := by
  induction n generalizing st with
  | zero => simp [iterate, digits]
  | succ n ih =>
    obtain ⟨h2, h3, htwo⟩ := body_step st h5
    rw [iterate_succ_fst, ih _ htwo, h2, h3, digits, List.sum_cons, Nat.add_assoc]

/-- Width `0` and numeric word `1` are preserved; the population count is in `2`. -/
def popcount : Stmt 6 1 :=
  .seq (.assign 3 (.var 1)) (.seq (.assign 2 (.const 0))
    (.seq (.assign 5 (.const 2)) (.loop 0 body)))

theorem popcount_run (st : State 6 1) :
    (popcount.run st).1.regs 2 = (digits (st.regs 0) (st.regs 1)).sum := by
  simp only [popcount, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  rw [iterate_result _ _ _ (by simp)]
  simp [Function.update]

theorem body_cost (st : State 6 1) (t b : ℕ)
    (h5 : st.regs 5 = 2) (h2 : st.regs 2 ≤ t) (h3 : Nat.size (st.regs 3) ≤ b) :
    (body.run st).2 ≤ 20 * (t + b + 1) := by
  have hm : st.regs 3 % 2 ≤ 1 := by have := Nat.mod_lt (st.regs 3) (by decide : 0 < 2); omega
  have hsm : Nat.size (st.regs 3 % 2) ≤ 1 := size_le_one_of_le_one hm
  have hsa : Nat.size (st.regs 2) ≤ t := (size_le_self _).trans h2
  have hsb : Nat.size (st.regs 2 + st.regs 3 % 2) ≤ t + 1 :=
    (size_le_self _).trans (by omega)
  have hsd : Nat.size (st.regs 3 / 2) ≤ b :=
    (Nat.size_le_size (Nat.div_le_self _ _)).trans h3
  simp only [body, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, h5, show Nat.size 2 = 2 from rfl]
  omega

/-- Population count is polynomial in width and the binary input size. -/
theorem popcount_cost (st : State 6 1) :
    (popcount.run st).2 ≤ 100 * (st.regs 0 + Nat.size (st.regs 1) + 1) ^ 2 := by
  let t := st.regs 0
  let b := Nat.size (st.regs 1)
  let s := setReg (setReg (setReg st 3 (st.regs 1)) 2 0) 5 2
  have hit := iterate_cost_idx body.run (Nat.size t + 1) (20 * (t + b + 1)) t
    (fun j u => u.regs 5 = 2 ∧ u.regs 2 ≤ j ∧ Nat.size (u.regs 3) ≤ b)
    (by
      intro j u hj hu
      obtain ⟨h2, h3, htwo⟩ := body_step u hu.1
      refine ⟨⟨htwo, ?_, ?_⟩, body_cost u t b hu.1 (hu.2.1.trans hj.le) hu.2.2⟩
      · rw [h2]
        have hm : u.regs 3 % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      · rw [h3]
        exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hu.2.2) s
    (by simp [s, b, Function.update])
  have hsize : Nat.size t ≤ t := size_le_self _
  have hb : t * (Nat.size t + 1 + 20 * (t + b + 1)) ≤
      t * (t + 1 + 20 * (t + b + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hb' := hit.trans hb
  simp only [popcount, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  change (Expr.var 1).cost st.regs + ((Expr.const 0).cost _ + ((Expr.const 2).cost _ +
    ((iterate body.run (Nat.size t + 1) t s).2 + Nat.size t + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero, show Nat.size 2 = 2 from rfl]
  change _ ≤ 100 * (t + b + 1) ^ 2
  have hbdef : Nat.size (st.regs 1) = b := rfl
  nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le (b ^ 2)]

/-- Population count is precisely the degree restriction of the semantic monomial codec. -/
theorem digits_sum_card (t : ℕ) (i : Fin (2 ^ t)) :
    (digits t i.val).sum = ((BooleanCoefficientIndex.subsetCodeEquiv t).symm i).card := by
  rw [digits_ofFn, List.sum_ofFn]
  change (∑ j : Fin t, i.val / 2 ^ j.val % 2) =
    (Finset.univ.filter (fun j : Fin t => (@finFunctionFinEquiv 2 t).symm i j = 1)).card
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  change (((@finFunctionFinEquiv 2 t).symm i j).val : ℕ) =
    if (@finFunctionFinEquiv 2 t).symm i j = 1 then 1 else 0
  generalize (@finFunctionFinEquiv 2 t).symm i j = bit
  fin_cases bit <;> rfl

end PCP.Lang.BooleanMask
