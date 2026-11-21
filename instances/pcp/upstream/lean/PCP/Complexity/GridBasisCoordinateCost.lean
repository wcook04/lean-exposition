import PCP.Complexity.GridBasisCoordinateLang

/-!
# Polynomial charged cost of a coordinate interpolation basis
-/

namespace PCP.Lang.GridBasisCoordinate

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

theorem update_cost (z : BinaryMaterializedField.Element t) (k n j : ℕ)
    (st : State 40 12) (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    (update.run st).2 ≤ 110000000 * (t + 1) ^ 4 := by
  have hv := inv_view z k n j st h hj hk
  have hc := scalar_cost factorTerm st (env z k j) hv
  obtain ⟨ho, _, _⟩ := scalar_spec factorTerm st (env z k j) hv
  have hs : Nat.size (fieldEquiv t (factorTerm.eval (env z k j))).val ≤ t :=
    Nat.size_le.mpr (fieldEquiv t (factorTerm.eval (env z k j))).isLt
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [update, run_seq_snd]
  generalize hu : (scalar factorTerm).run st = u at *
  change u.1.regs 30 = _ at ho
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ho]
  norm_num only [factorTerm, Term.weight] at hc
  omega

theorem advance_cost (z : BinaryMaterializedField.Element t) (k n j : ℕ)
    (st : State 40 12) (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    (advance.run st).2 ≤ 111000000 * (t + 1) ^ 4 := by
  have hjb : Nat.size j ≤ t := Nat.size_le.mpr hj
  have hkb : Nat.size k ≤ t := Nat.size_le.mpr hk
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  by_cases heq : j = k
  · simp only [advance, run_seq_snd, run_assign_fst, run_ite_snd, Expr.eval,
      h.2.1, h.2.2.2.1, heq, ↓reduceIte, setReg_regs, Function.update_self,
      Nat.size_one]
    change (Expr.eq 1 3).cost st.regs + (1 + 1 + 1) + 1 ≤ _
    simp only [Expr.cost, Expr.readSize, Expr.eval, h.2.1, h.2.2.2.1, heq,
      ↓reduceIte, Nat.size_one]
    omega
  · let s := setReg st 4 0
    have hs : Inv z k n j s := by simpa [Inv, s, Function.update] using h
    have hc := update_cost z k n j s hs hj hk
    simp only [advance, run_seq_snd, run_assign_fst, run_ite_snd, Expr.eval,
      h.2.1, h.2.2.2.1, ite_eq_right heq, setReg_regs, Function.update_self, ne_eq,
      not_true_eq_false, ↓reduceIte, Nat.size_zero]
    change (Expr.eq 1 3).cost st.regs + ((update.run s).2 + 0 + 1) + 1 ≤ _
    simp only [Expr.cost, Expr.readSize, Expr.eval, h.2.1, h.2.2.2.1, ite_eq_right heq,
      Nat.size_zero]
    omega

theorem body_cost (z : BinaryMaterializedField.Element t) (k n j : ℕ) (st : State 40 12)
    (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    (body.run st).2 ≤ 120000000 * (t + 1) ^ 4 := by
  have hc := advance_cost z k n j st h hj hk
  have ha := advance_spec z k n j st h hj hk
  have hjb : Nat.size j ≤ t := Nat.size_le.mpr hj
  have hnext : Nat.size (j + 1) ≤ t + 1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size (Nat.succ_le_of_lt hj)
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [body, run_seq_snd]
  generalize hu : advance.run st = u at *
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, dite_true, Nat.size_one, ha.2.1]
  omega

/-- Uniform polynomial cost in the supplied grid size and field bit width. -/
theorem program_cost (z : BinaryMaterializedField.Element t) (k n : ℕ)
    (hn : n ≤ 2 ^ t) (hk : k < 2 ^ t) (st : State 40 12)
    (h0 : st.regs 0 = (fieldEquiv t z).val) (h3 : st.regs 3 = k)
    (ht : st.regs 24 = t) (hc : st.regs 32 = n)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).2 ≤ 130000000 * (n + t + 1) ^ 5 := by
  let s := setReg (setReg st 1 0) 2 1
  have hi : Inv z k n 0 s := by
    refine ⟨by simpa [s, Function.update] using h0, by simp [s, Function.update], ?_,
      by simpa [s, Function.update] using h3, by simpa [s, Function.update] using ht,
      by simpa [s, Function.update] using hc, hm, he⟩
    change 1 = (fieldEquiv t (value z k 0)).val
    rw [value_zero, code_one]
  have hit := iterate_cost_idx body.run (Nat.size n + 1) (120000000 * (t + 1) ^ 4)
    n (Inv z k n) (fun j u hj hu => ⟨body_inv z k n j u hu (lt_of_lt_of_le hj hn) hk,
      body_cost z k n j u hu (lt_of_lt_of_le hj hn) hk⟩) s hi
  have hsize := size_le_self n
  have hpow : (t + 1) ^ 4 ≤ (n + t + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hiter := hit.trans (Nat.mul_le_mul_left n
    (show Nat.size n + 1 + 120000000 * (t + 1) ^ 4 ≤
      n + 1 + 120000000 * (n + t + 1) ^ 4 by omega))
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update_of_ne (by decide : (32 : Fin 40) ≠ 2),
    Function.update_of_ne (by decide : (32 : Fin 40) ≠ 1), hc]
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
  have hmul := Nat.mul_le_mul_right (n + 1 + 120000000 * (n + t + 1) ^ 4) hnbase
  rw [pow_succ]
  nlinarith

end PCP.Lang.GridBasisCoordinate
