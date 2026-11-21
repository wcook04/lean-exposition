import PCP.Complexity.BinaryPolynomialCoefficientLang

/-!
# Constructing powers of two at their actual bit cost

The exponent is a counted-loop bound. Each iteration doubles the stored result;
the quadratic charged bound uses its bit length, not its numeric magnitude.
-/

namespace PCP.Lang.PowerTwo

open BinaryPolynomialCoefficient

/-- Exponent register 2 is retained; register 5 receives `2^exponent`. -/
def program : Stmt 8 2 := .seq (.assign 5 (.const 1))
  (.seq (.assign 6 (.const 2)) (.loop 2 powerBody))

theorem program_run (st : State 8 2) :
    (program.run st).1.regs 5 = 2 ^ st.regs 2 := by
  let s := setReg (setReg st 5 1) 6 2
  have h := power_iterate (st.regs 2) (Nat.size (st.regs 2) + 1) s (by simp [s])
  simp only [program, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst]
  simpa [s, Function.update] using h

theorem program_reg (i : Fin 8) (hi : i ≠ 5) (hi' : i ≠ 6) (st : State 8 2) :
    (program.run st).1.regs i = st.regs i := by
  exact run_regs_frame program i
    (by simp [program, powerBody, Stmt.regWrites, hi, hi']) st

theorem program_lists (L : Fin 2) (st : State 8 2) :
    (program.run st).1.lists L = st.lists L :=
  run_lists_frame program L (by simp [program, powerBody, Stmt.listWrites]) st

theorem body_cost (j : ℕ) (st : State 8 2) (h5 : st.regs 5 = 2 ^ j)
    (h6 : st.regs 6 = 2) : (powerBody.run st).2 = 2 * j + 6 := by
  simp [powerBody, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h5, h6,
    ← pow_succ, Nat.size_pow, show Nat.size 2 = 2 from rfl]
  omega

/-- All intermediate powers and every loop overhead are charged. -/
theorem program_cost (st : State 8 2) :
    (program.run st).2 ≤ 20 * (st.regs 2 + 1) ^ 2 := by
  let n := st.regs 2
  let s := setReg (setReg st 5 1) 6 2
  have hloop := iterate_cost_idx powerBody.run (Nat.size n + 1) (2 * n + 6) n
    (fun j u => u.regs 5 = 2 ^ j ∧ u.regs 6 = 2)
    (by
      intro j u hj hu
      constructor
      · simp [powerBody, Stmt.run, Expr.eval, Function.update, hu.1, hu.2, pow_succ]
      · rw [body_cost j u hu.1 hu.2]
        omega) s (by simp [s, Function.update])
  have hn : s.regs 2 = n := by simp [s, n, Function.update]
  have hsize := size_le_self n
  have h1 : ((Stmt.assign 5 (.const 1) : Stmt 8 2).run st).2 = 3 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  have h2 : ((Stmt.assign 6 (.const 2) : Stmt 8 2).run (setReg st 5 1)).2 = 5 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, show Nat.size 2 = 2 from rfl]
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval, h1, h2]
  change 3 + (5 + ((Stmt.loop 2 powerBody).run s).2 + 1) + 1 ≤ _
  rw [run_loop_snd, hn]
  change 3 + (5 + ((iterate powerBody.run (Nat.size n + 1) n s).2 + Nat.size n + 1) + 1) +
    1 ≤ 20 * (n + 1) ^ 2
  nlinarith

end PCP.Lang.PowerTwo
