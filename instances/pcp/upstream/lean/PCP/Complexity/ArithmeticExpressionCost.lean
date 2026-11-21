/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticExpressionLang

/-!
# Caller-state bounds for compiled arithmetic

The expression compiler reads only its source registers and scratch-list content;
initial scratch-register values have no effect on its charged-cost bound.
-/

namespace PCP.Lang.ArithmeticExpression

variable {n : ℕ}

@[simp] theorem binaryStep_uses (o : Op) : (binaryStep (n := n) o).uses = [] := by
  cases o <;> simp [binaryStep, Stmt.uses, Stmt.mustW, Expr.uses, Op.expr]

theorem compile_uses (t : Term n) (r : Fin (n + 3)) (hr : r ∈ (compile t).uses) :
    ∃ i : Fin n, r = i.castAdd 3 := by
  induction t with
  | const a => simp [compile, Stmt.uses, Stmt.mustW, Expr.uses] at hr
  | input i =>
      simp only [compile, Stmt.uses, List.mem_singleton] at hr
      exact ⟨i, hr⟩
  | bin o a b iha ihb =>
      simp only [compile, Stmt.uses, binaryStep_uses, List.filter_nil, List.append_nil,
        List.mem_append, List.mem_filter] at hr
      rcases hr with hr | ⟨hr, _⟩
      · exact iha hr
      · exact ihb hr
  | cond c a b ihc iha ihb =>
      simp only [compile, Stmt.uses, Stmt.mustW, List.nil_append, List.mem_append,
        List.mem_filter, List.mem_cons, decide_eq_true_eq] at hr
      rcases hr with hr | ⟨⟨hr, hpop⟩, _⟩
      · exact ihc hr
      · rcases hr with hr | hr | hr
        · subst r
          simp at hpop
        · exact iha hr
        · exact ihb hr

theorem scalar_uses (t : Term n) (r : Fin (n + 3)) (hr : r ∈ (scalar t).uses) :
    ∃ i : Fin n, r = i.castAdd 3 := by
  apply compile_uses t r
  simpa [scalar, Stmt.uses] using hr

theorem compile_lUses (t : Term n) (L : Fin 2) (hL : L ∈ (compile t).lUses) : L = 1 := by
  induction t with
  | const a => simp [compile, Stmt.lUses] at hL
  | input i => simp [compile, Stmt.lUses] at hL
  | bin o a b iha ihb =>
      simp only [compile, Stmt.lUses, List.mem_append] at hL
      rcases hL with hL | hL | hL
      · exact iha hL
      · exact ihb hL
      · simpa [binaryStep, Stmt.lUses] using hL
  | cond c a b ihc iha ihb =>
      simp only [compile, Stmt.lUses, List.mem_append, List.mem_singleton] at hL
      rcases hL with hL | hL | hL | hL
      · exact ihc hL
      · exact hL
      · exact iha hL
      · exact ihb hL

theorem scalar_lUses (t : Term n) (L : Fin 2) (hL : L ∈ (scalar t).lUses) : L = 1 := by
  simp only [scalar, Stmt.lUses, List.mem_append, List.mem_singleton] at hL
  exact hL.elim (compile_lUses t L) id

/-- Bounds from only the caller-owned input registers and expression stack. -/
theorem scalar_cost_state (t : Term n) (st : State (n + 3) 2) (W : ℕ)
    (hr : ∀ i : Fin n, Nat.size (st.regs (i.castAdd 3)) ≤ W)
    (hl : listSize (st.lists 1) ≤ W) :
    ((scalar t).run st).2 ≤
      (scalar t).C * ((scalar t).width + (scalar t).csize + 1) * (W + 1) := by
  apply loopFree_cost_le (scalar t) (scalar_loopFree t) st W
  · intro r hmem
    obtain ⟨i, rfl⟩ := scalar_uses t r hmem
    exact hr i
  · intro L hmem
    rw [scalar_lUses t L hmem]
    exact hl

private theorem register_distinct : leftReg n ≠ rightReg n ∧ leftReg n ≠ flagReg n ∧
    rightReg n ≠ flagReg n := by
  simp only [leftReg, rightReg, flagReg, ne_eq, Fin.mk.injEq]
  omega

private theorem input_distinct (i : Fin n) :
    i.castAdd 3 ≠ rightReg n ∧ i.castAdd 3 ≠ flagReg n := by
  simp only [rightReg, flagReg, ne_eq, Fin.ext_iff, Fin.val_castAdd]
  omega

def Term.cost (r : Fin n → ℕ) : Term n → ℕ
  | .const a => 3 * Nat.size a + 3
  | .input i => Nat.size (r i) + 1
  | .bin o a b => a.cost r + b.cost r + 2 * Nat.size (a.eval r) +
      2 * Nat.size (b.eval r) + 2 * Nat.size (o.eval (a.eval r) (b.eval r)) + 9
  | .cond c a b => c.cost r + (if c.eval r ≠ 0 then a.cost r else b.cost r) +
      2 * Nat.size (c.eval r) + 4

theorem binaryStep_cost (o : Op) (st : State (n + 3) 2) (a b : ℕ) (tail : List ℕ)
    (hs : st.lists 1 = b :: a :: tail) :
    ((binaryStep o).run st).2 =
      2 * Nat.size a + 2 * Nat.size b + 2 * Nat.size (o.eval a b) + 7 := by
  obtain ⟨hLR, hLF, hRF⟩ := register_distinct (n := n)
  cases o <;> simp [binaryStep, Stmt.run, hs, Function.update, Op.expr, Op.eval,
    Expr.eval, Expr.cost, Expr.readSize, hLF, hRF, Ne.symm hLR] <;> omega

/-- The exact charged cost is independent of initial scratch values and stack tail. -/
theorem compile_cost_exact (t : Term n) (st : State (n + 3) 2) :
    ((compile t).run st).2 = t.cost (fun i => st.regs (i.castAdd 3)) := by
  induction t generalizing st with
  | const a => simp [compile, Stmt.run, Term.cost, Expr.eval, Expr.cost, Expr.readSize]; omega
  | input i => rfl
  | bin o a b iha ihb =>
      have hstack : ((compile b).run ((compile a).run st).1).1.lists 1 =
          b.eval (fun i => st.regs (i.castAdd 3)) ::
            a.eval (fun i => st.regs (i.castAdd 3)) :: st.lists 1 := by
        rw [compile_spec, compile_inputs, compile_spec]
      simp only [compile, run_seq_snd, iha, ihb, compile_inputs,
        binaryStep_cost o _ _ _ _ hstack, Term.cost]
      omega
  | cond c a b ihc iha ihb =>
      let sc := ((compile c).run st).1
      let sp := ((Stmt.pop 1 (flagReg n) (rightReg n)).run sc).1
      have hc : sc.lists 1 = c.eval (fun i => st.regs (i.castAdd 3)) :: st.lists 1 :=
        compile_spec c st
      have hf : sp.regs (flagReg n) = c.eval (fun i => st.regs (i.castAdd 3)) := by
        simp [sp, Stmt.run, hc, setReg, setList, Ne.symm (register_distinct (n := n)).2.2]
      have hi : (fun i : Fin n => sp.regs (i.castAdd 3)) =
          fun i => st.regs (i.castAdd 3) := by
        funext i
        simp [sp, Stmt.run, hc, setReg, setList, (input_distinct i).1,
          (input_distinct i).2, sc, compile_preserves_input]
      have hp : ((Stmt.pop 1 (flagReg n) (rightReg n)).run sc).2 =
          Nat.size (c.eval (fun i => st.regs (i.castAdd 3))) + 1 := by
        simp [Stmt.run, hc]
      change ((compile c).run st).2 +
        (((Stmt.pop 1 (flagReg n) (rightReg n)).run sc).2 +
          ((Stmt.ite (flagReg n) (compile a) (compile b)).run sp).2 + 1) + 1 = _
      rw [ihc, hp, run_ite_snd, hf]
      simp only [iha, ihb, hi, Term.cost]
      omega

/-- Exact scalar cost, including the final pop into the result register. -/
theorem scalar_cost_exact (t : Term n) (st : State (n + 3) 2) :
    ((scalar t).run st).2 = t.cost (fun i => st.regs (i.castAdd 3)) +
      Nat.size (t.eval (fun i => st.regs (i.castAdd 3))) + 2 := by
  simp [scalar, compile_cost_exact, Stmt.run, compile_spec]
  omega

/-- Existing caller stack content is excluded entirely from the arithmetic cost bound. -/
theorem scalar_cost_inputs (t : Term n) (st : State (n + 3) 2) (W : ℕ)
    (hr : ∀ i : Fin n, Nat.size (st.regs (i.castAdd 3)) ≤ W) :
    ((scalar t).run st).2 ≤
      (scalar t).C * ((scalar t).width + (scalar t).csize + 1) * (W + 1) := by
  have he : ((scalar t).run st).2 =
      ((scalar t).run (inputState (fun i => st.regs (i.castAdd 3)))).2 := by
    simp only [scalar_cost_exact, inputState_input]
  rw [he]
  exact scalar_cost t _ W hr

/-- Every resulting arithmetic value has bit length bounded by the same fixed constant. -/
theorem eval_size_le (t : Term n) (r : Fin n → ℕ) (W : ℕ)
    (hr : ∀ i, Nat.size (r i) ≤ W) :
    Nat.size (t.eval r) ≤
      (scalar t).C * ((scalar t).width + (scalar t).csize + 1) * (W + 1) := by
  have h := scalar_cost t r W hr
  rw [scalar_cost_exact] at h
  simp only [inputState_input] at h
  change t.cost r + Nat.size (t.eval r) + 2 ≤ _ at h
  omega

end PCP.Lang.ArithmeticExpression
