/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Compiling nested arithmetic expressions to the counted-loop language

The compiler preserves source registers and evaluates through a scratch stack.
Its output is actual loop-free `Lang` code over addition, subtraction, product,
quotient, remainder, comparisons, and conditional branches. This is used for
numeric graph adjacency and arithmetic constraint codecs.
-/

namespace PCP.Lang.ArithmeticExpression

inductive Op
  | add | sub | mul | div | mod | eq | lt
  deriving DecidableEq, Repr

def Op.eval : Op → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .eq, a, b => if a = b then 1 else 0
  | .lt, a, b => if a < b then 1 else 0

def Op.expr {R : ℕ} (x y : Fin R) : Op → Expr R
  | .add => .add x y
  | .sub => .sub x y
  | .mul => .mul x y
  | .div => .div x y
  | .mod => .mod x y
  | .eq => .eq x y
  | .lt => .lt x y

@[simp] theorem Op.eval_expr {R : ℕ} (o : Op) (x y : Fin R) (r : Fin R → ℕ) :
    (o.expr x y).eval r = o.eval (r x) (r y) := by cases o <;> rfl

inductive Term (n : ℕ)
  | const : ℕ → Term n
  | input : Fin n → Term n
  | bin : Op → Term n → Term n → Term n
  | cond : Term n → Term n → Term n → Term n
  deriving Repr

def Term.eval {n : ℕ} (r : Fin n → ℕ) : Term n → ℕ
  | .const a => a
  | .input i => r i
  | .bin o a b => o.eval (a.eval r) (b.eval r)
  | .cond c a b => if c.eval r ≠ 0 then a.eval r else b.eval r

variable {n : ℕ}

def leftReg (n : ℕ) : Fin (n + 3) := ⟨n, by omega⟩
def rightReg (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩
def flagReg (n : ℕ) : Fin (n + 3) := ⟨n + 2, by omega⟩

private theorem scratch_ne : leftReg n ≠ rightReg n ∧ leftReg n ≠ flagReg n ∧
    rightReg n ≠ flagReg n := by
  simp only [leftReg, rightReg, flagReg, ne_eq, Fin.mk.injEq]
  omega

private theorem input_ne (i : Fin n) :
    i.castAdd 3 ≠ leftReg n ∧ i.castAdd 3 ≠ rightReg n ∧ i.castAdd 3 ≠ flagReg n := by
  simp only [leftReg, rightReg, flagReg, ne_eq, Fin.ext_iff, Fin.val_castAdd]
  omega

/-- Consume the two top stack values and push their binary result. -/
def binaryStep (o : Op) : Stmt (n + 3) 2 :=
  .seq (.pop 1 (rightReg n) (flagReg n))
    (.seq (.pop 1 (leftReg n) (flagReg n))
      (.seq (.assign (leftReg n) (o.expr (leftReg n) (rightReg n))) (.push 1 (leftReg n))))

/-- Source registers are embedded first; the final three registers are compiler scratch. -/
def compile : Term n → Stmt (n + 3) 2
  | .const a => .seq (.assign (leftReg n) (.const a)) (.push 1 (leftReg n))
  | .input i => .push 1 (i.castAdd 3)
  | .bin o a b => .seq (compile a) (.seq (compile b) (binaryStep o))
  | .cond c a b => .seq (compile c)
      (.seq (.pop 1 (flagReg n) (rightReg n)) (.ite (flagReg n) (compile a) (compile b)))

theorem compile_regWrites (t : Term n) (r : Fin (n + 3)) (hr : r ∈ (compile t).regWrites) :
    r = leftReg n ∨ r = rightReg n ∨ r = flagReg n := by
  induction t with
  | const a => exact Or.inl (by simpa [compile, Stmt.regWrites] using hr)
  | input i => simp [compile, Stmt.regWrites] at hr
  | bin o a b iha ihb =>
      simp only [compile, Stmt.regWrites, List.mem_append] at hr
      rcases hr with hr | hr | hr
      · exact iha hr
      · exact ihb hr
      · simpa [binaryStep, Stmt.regWrites, or_assoc, or_left_comm, or_comm] using hr
  | cond c a b ihc iha ihb =>
      simp only [compile, Stmt.regWrites, List.mem_append] at hr
      rcases hr with hr | hr | hr | hr
      · exact ihc hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        exact hr.elim (fun h => Or.inr (Or.inr h)) (fun h => Or.inr (Or.inl h))
      · exact iha hr
      · exact ihb hr

theorem compile_preserves_input (t : Term n) (i : Fin n) (st : State (n + 3) 2) :
    ((compile t).run st).1.regs (i.castAdd 3) = st.regs (i.castAdd 3) := by
  apply run_regs_frame
  intro hr
  rcases compile_regWrites t _ hr with h | h | h
  · exact (input_ne i).1 h
  · exact (input_ne i).2.1 h
  · exact (input_ne i).2.2 h

theorem compile_listWrites (t : Term n) : ∀ L ∈ (compile t).listWrites, L = 1 := by
  induction t with
  | const a => simp [compile, Stmt.listWrites]
  | input i => simp [compile, Stmt.listWrites]
  | bin o a b iha ihb =>
      simp only [compile, Stmt.listWrites, List.mem_append]
      intro L hL
      rcases hL with hL | hL | hL
      · exact iha L hL
      · exact ihb L hL
      · simpa [binaryStep, Stmt.listWrites] using hL
  | cond c a b ihc iha ihb =>
      simp only [compile, Stmt.listWrites, List.mem_append]
      intro L hL
      rcases hL with hL | hL | hL | hL
      · exact ihc L hL
      · simpa using hL
      · exact iha L hL
      · exact ihb L hL

theorem compile_preserves_source (t : Term n) (st : State (n + 3) 2) :
    ((compile t).run st).1.lists 0 = st.lists 0 := by
  apply run_lists_frame
  intro h
  have := compile_listWrites t 0 h
  contradiction

theorem binaryStep_spec (o : Op) (st : State (n + 3) 2) (a b : ℕ) (tail : List ℕ)
    (hs : st.lists 1 = b :: a :: tail) :
    ((binaryStep o).run st).1.lists 1 = o.eval a b :: tail := by
  obtain ⟨hLR, hLF, hRF⟩ := scratch_ne (n := n)
  simp [binaryStep, Stmt.run, hs, Function.update, Op.eval_expr,
    hLF, hRF, Ne.symm hLR]

theorem compile_inputs (t : Term n) (st : State (n + 3) 2) :
    (fun i : Fin n => ((compile t).run st).1.regs (i.castAdd 3)) =
      (fun i => st.regs (i.castAdd 3)) := funext fun i => compile_preserves_input t i st

theorem compile_spec (t : Term n) (st : State (n + 3) 2) :
    ((compile t).run st).1.lists 1 =
      t.eval (fun i => st.regs (i.castAdd 3)) :: st.lists 1 := by
  induction t generalizing st with
  | const a => simp [compile, Stmt.run, Term.eval, Expr.eval, setReg, setList]
  | input i => simp [compile, Stmt.run, Term.eval, setList]
  | bin o a b iha ihb =>
      simp only [compile, run_seq_fst]
      apply (binaryStep_spec o _ _ _ _ ?_).trans (by rfl)
      rw [ihb, compile_inputs, iha]
  | cond c a b ihc iha ihb =>
      let sc := ((compile c).run st).1
      let sp := ((Stmt.pop 1 (flagReg n) (rightReg n)).run sc).1
      have hc : sc.lists 1 = c.eval (fun i => st.regs (i.castAdd 3)) :: st.lists 1 := ihc st
      have hp : sp.lists 1 = st.lists 1 := by
        simp [sp, Stmt.run, hc, setReg, setList]
      have hf : sp.regs (flagReg n) = c.eval (fun i => st.regs (i.castAdd 3)) := by
        simp [sp, Stmt.run, hc, setReg, setList, Ne.symm (scratch_ne (n := n)).2.2]
      have hi : (fun i : Fin n => sp.regs (i.castAdd 3)) =
          fun i => st.regs (i.castAdd 3) := by
        funext i
        simp [sp, Stmt.run, hc, setReg, setList, (input_ne i).2.1, (input_ne i).2.2,
          sc, compile_preserves_input]
      change ((Stmt.ite (flagReg n) (compile a) (compile b)).run sp).1.lists 1 = _
      simp only [Stmt.run, hf, Term.eval]
      split_ifs <;> simp only [iha, ihb, hi, hp]

@[simp] theorem compile_loopFree (t : Term n) : (compile t).loopFree = true := by
  induction t <;> simp_all [compile, binaryStep, Stmt.loopFree]

/-- Evaluate into the left scratch register, restoring the scratch stack exactly. -/
def scalar (t : Term n) : Stmt (n + 3) 2 :=
  .seq (compile t) (.pop 1 (leftReg n) (flagReg n))

theorem scalar_spec (t : Term n) (st : State (n + 3) 2) :
    ((scalar t).run st).1.regs (leftReg n) = t.eval (fun i => st.regs (i.castAdd 3)) ∧
    ((scalar t).run st).1.lists 1 = st.lists 1 := by
  simp [scalar, Stmt.run, compile_spec, setReg, setList, (scratch_ne (n := n)).2.1]

theorem scalar_preserves_input (t : Term n) (i : Fin n) (st : State (n + 3) 2) :
    ((scalar t).run st).1.regs (i.castAdd 3) = st.regs (i.castAdd 3) := by
  simp [scalar, Stmt.run, compile_spec, setReg, setList,
    (input_ne i).1, (input_ne i).2.2, compile_preserves_input]

theorem scalar_preserves_source (t : Term n) (st : State (n + 3) 2) :
    ((scalar t).run st).1.lists 0 = st.lists 0 := by
  simp [scalar, Stmt.run, compile_spec, setReg, setList, compile_preserves_source]

@[simp] theorem scalar_loopFree (t : Term n) : (scalar t).loopFree = true := by
  simp [scalar, Stmt.loopFree]

/-- Store a nested arithmetic expression in one source-register slot. -/
def assign (dest : Fin n) (t : Term n) : Stmt (n + 3) 2 :=
  .seq (scalar t) (.assign (dest.castAdd 3) (.var (leftReg n)))

theorem assign_spec (dest : Fin n) (t : Term n) (st : State (n + 3) 2) :
    ((assign dest t).run st).1.regs (dest.castAdd 3) =
      t.eval (fun i => st.regs (i.castAdd 3)) := by
  simp [assign, run_seq_fst, run_assign_fst, Expr.eval, (scalar_spec t st).1]

theorem assign_frame (dest i : Fin n) (t : Term n) (hi : i ≠ dest)
    (st : State (n + 3) 2) :
    ((assign dest t).run st).1.regs (i.castAdd 3) = st.regs (i.castAdd 3) := by
  have hc : i.castAdd 3 ≠ dest.castAdd 3 := by
    simpa only [ne_eq, Fin.ext_iff, Fin.val_castAdd] using hi
  simp [assign, run_seq_fst, run_assign_fst, Expr.eval, hc, scalar_preserves_input]

theorem assign_lists (dest : Fin n) (t : Term n) (st : State (n + 3) 2) :
    ((assign dest t).run st).1.lists = st.lists := by
  funext L
  fin_cases L
  · simpa [assign, run_seq_fst, run_assign_fst] using scalar_preserves_source t st
  · simpa [assign, run_seq_fst, run_assign_fst] using (scalar_spec t st).2

@[simp] theorem assign_loopFree (dest : Fin n) (t : Term n) :
    (assign dest t).loopFree = true := by simp [assign, Stmt.loopFree]

def inputState (r : Fin n → ℕ) : State (n + 3) 2 where
  regs j := if hj : j.val < n then r ⟨j.val, hj⟩ else 0
  lists _ := []

@[simp] theorem inputState_input (r : Fin n → ℕ) (i : Fin n) :
    (inputState r).regs (i.castAdd 3) = r i := by simp [inputState, i.isLt]

theorem scalar_inputState (t : Term n) (r : Fin n → ℕ) :
    ((scalar t).run (inputState r)).1.regs (leftReg n) = t.eval r := by
  simpa using (scalar_spec t (inputState r)).1

/-- The compiler supplies a fixed bit-linear operational cost bound. -/
theorem scalar_cost (t : Term n) (r : Fin n → ℕ) (W : ℕ)
    (hr : ∀ i, Nat.size (r i) ≤ W) :
    ((scalar t).run (inputState r)).2 ≤
      (scalar t).C * ((scalar t).width + (scalar t).csize + 1) * (W + 1) := by
  apply loopFree_cost_le (scalar t) (scalar_loopFree t) (inputState r) W
  · intro j _
    dsimp only [inputState]
    split_ifs with hj
    · exact hr _
    · simp
  · intro L _
    simp [inputState, listSize]

end PCP.Lang.ArithmeticExpression
