import PCP.Complexity.GridFactorLang

/-!
# Polynomial charged cost of the variable-size grid factor
-/

namespace PCP.Lang.GridFactor

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

theorem body_cost (z : BinaryMaterializedField.Element t) (n j : ℕ) (st : State 39 12)
    (h : Inv z n j st) (hj : j < 2 ^ t) :
    (body.run st).2 ≤ 50000000 * (t + 1) ^ 4 := by
  have hv := inv_view z n j st h hj
  have hc := scalar_cost factorTerm st (env z j) hv
  obtain ⟨ho, _, he⟩ := scalar_spec factorTerm st (env z j) hv
  rw [factorTerm_eval] at ho
  have hsize : Nat.size (fieldEquiv t (value z (j + 1))).val ≤ t :=
    Nat.size_le.mpr (fieldEquiv t (value z (j + 1))).isLt
  have hindex : Nat.size j ≤ t := Nat.size_le.mpr hj
  have hnext : Nat.size (j + 1) ≤ t + 1 := by
    have := Nat.size_le_size (Nat.succ_le_of_lt hj)
    simpa only [Nat.size_pow] using this
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [body, run_seq_snd]
  generalize hu : (scalar factorTerm).run st = u at *
  have h1 : u.1.regs 1 = j := by simpa [env, code_node j hj] using he.1 1
  change u.1.regs 29 = _ at ho
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, dite_true, Nat.size_one, ho, h1]
  norm_num only [factorTerm, Term.weight] at hc
  omega

/-- The node count is supplied at runtime; every visit and field operation is charged. -/
theorem program_cost (z : BinaryMaterializedField.Element t) (n : ℕ) (hn : n ≤ 2 ^ t)
    (st : State 39 12) (h0 : st.regs 0 = (fieldEquiv t z).val)
    (ht : st.regs 23 = t) (hc : st.regs 31 = n)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).2 ≤ 60000000 * (n + t + 1) ^ 5 := by
  let s := setReg (setReg st 1 0) 2 1
  have hi : Inv z n 0 s := by
    refine ⟨by simpa [s, Function.update] using h0, by simp [s, Function.update],
      ?_, by simpa [s, Function.update] using ht,
      by simpa [s, Function.update] using hc, hm, he⟩
    change 1 = (fieldEquiv t (value z 0)).val
    rw [value_zero, code_one]
  have hit := iterate_cost_idx body.run (Nat.size n + 1) (50000000 * (t + 1) ^ 4)
    n (Inv z n) (fun j u hj hu => ⟨body_inv z n j u hu (lt_of_lt_of_le hj hn),
      body_cost z n j u hu (lt_of_lt_of_le hj hn)⟩) s hi
  have hsize := size_le_self n
  have hpow : (t + 1) ^ 4 ≤ (n + t + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hiter := hit.trans (Nat.mul_le_mul_left n
    (show Nat.size n + 1 + 50000000 * (t + 1) ^ 4 ≤
      n + 1 + 50000000 * (n + t + 1) ^ 4 by omega))
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update_of_ne (by decide : (31 : Fin 39) ≠ 2),
    Function.update_of_ne (by decide : (31 : Fin 39) ≠ 1), hc]
  change ((Stmt.assign 1 (.const 0)).run st).2 +
    (((Stmt.assign 2 (.const 1)).run (setReg st 1 0)).2 +
      ((iterate body.run (Nat.size n + 1) n s).2 + Nat.size n + 1) + 1) + 1 ≤ _
  have ha : ((Stmt.assign 1 (.const 0)).run st).2 = 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  have hb : ((Stmt.assign 2 (.const 1)).run (setReg st 1 0)).2 = 3 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  rw [ha, hb]
  have hbase : 1 ≤ n + t + 1 := by omega
  have hlin : n + t + 1 ≤ (n + t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right hbase (by decide : 1 ≤ 4)
  have hnbase : n ≤ n + t + 1 := by omega
  have hmul := Nat.mul_le_mul_right (n + 1 + 50000000 * (n + t + 1) ^ 4) hnbase
  rw [pow_succ]
  nlinarith

end PCP.Lang.GridFactor
