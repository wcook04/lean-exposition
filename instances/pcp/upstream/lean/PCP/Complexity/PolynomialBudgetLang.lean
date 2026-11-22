/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Operational evaluation of the fixed polynomial tableau budgets

A coefficient list is compiled to a loop-free Horner statement using three natural
registers. Its output agrees exactly with polynomial evaluation, and its charged
cost is linear in the input bit size, with a constant depending on the fixed
coefficient list. Every natural polynomial has such a fixed presentation.
This is a `Lang` program/cost result; the proved machine compiler can be applied separately.
-/

namespace PCP.Lang.PolynomialBudget

/-- Low-degree coefficients, evaluated by Horner's rule. -/
def value : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: cs, n => value cs n * n + a

/-- Add a constant to the coefficient list, including the zero-polynomial case. -/
def addConstant (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: cs => (b + a) :: cs

@[simp] theorem value_addConstant (a : ℕ) (cs : List ℕ) (n : ℕ) :
    value (addConstant a cs) n = value cs n + a := by
  cases cs <;> simp [addConstant, value, Nat.add_assoc]

/-- Coefficients are selected once for each fixed budget polynomial, never from the input. -/
theorem exists_coefficients (p : Polynomial ℕ) :
    ∃ cs : List ℕ, ∀ n, value cs n = p.eval n := by
  induction p using Polynomial.recOnHorner with
  | M0 => exact ⟨[], fun n => by simp [value]⟩
  | MC p a _ _ ih =>
      obtain ⟨cs, hc⟩ := ih
      refine ⟨addConstant a cs, fun n => ?_⟩
      simp [hc]
  | MX p _ ih =>
      obtain ⟨cs, hc⟩ := ih
      refine ⟨0 :: cs, fun n => ?_⟩
      simp [value, hc]

/-- Register 0 is the input; 1 is the accumulator; 2 holds the current fixed coefficient. -/
def hornerStep (a : ℕ) : Stmt 3 2 :=
  .seq (.assign 1 (.mul 1 0))
    (.seq (.assign 2 (.const a)) (.assign 1 (.add 1 2)))

/-- Each coefficient becomes fixed straight-line code. Lists are preserved. -/
def code : List ℕ → Stmt 3 2
  | [] => .assign 1 (.const 0)
  | a :: cs => .seq (code cs) (hornerStep a)

theorem hornerStep_spec (a : ℕ) (st : State 3 2) :
    (hornerStep a |>.run st).1.regs 0 = st.regs 0 ∧
      (hornerStep a |>.run st).1.regs 1 = st.regs 1 * st.regs 0 + a := by
  simp [hornerStep, Stmt.run, Expr.eval, Function.update]

theorem code_spec (cs : List ℕ) (st : State 3 2) :
    ((code cs).run st).1.regs 0 = st.regs 0 ∧
      ((code cs).run st).1.regs 1 = value cs (st.regs 0) := by
  induction cs with
  | nil => simp [code, value, Stmt.run, Expr.eval, Function.update]
  | cons a cs ih =>
      rw [code, run_seq_fst]
      have hh := hornerStep_spec a ((code cs).run st).1
      rw [ih.1, ih.2] at hh
      exact hh

@[simp] theorem code_listWrites (cs : List ℕ) : (code cs).listWrites = [] := by
  induction cs <;> simp [code, hornerStep, Stmt.listWrites, *]

theorem code_lists (cs : List ℕ) (st : State 3 2) : ((code cs).run st).1.lists = st.lists := by
  funext L
  exact run_lists_frame (code cs) L (by simp) st

@[simp] theorem code_loopFree (cs : List ℕ) : (code cs).loopFree = true := by
  induction cs <;> simp [code, hornerStep, Stmt.loopFree, *]

@[simp] theorem code_lUses (cs : List ℕ) : (code cs).lUses = [] := by
  induction cs <;> simp [code, hornerStep, Stmt.lUses, *]

/-- This explicit constant depends only on the compiled coefficient list. -/
def costConstant (cs : List ℕ) : ℕ :=
  (code cs).C * ((code cs).width + (code cs).csize + 1)

/-- The precise operational cost is bounded in the sizes of the three initial registers. -/
theorem code_cost_le (cs : List ℕ) (st : State 3 2) :
    ((code cs).run st).2 ≤ costConstant cs *
      (Nat.size (st.regs 0) + Nat.size (st.regs 1) + Nat.size (st.regs 2) + 1) := by
  apply loopFree_cost_le (code cs) (code_loopFree cs) st
  · intro r _
    fin_cases r <;> simp <;> omega
  · intro L hL
    simp at hL

/-- A standard evaluation state, independent of any other machine data. -/
def inputState (n : ℕ) : State 3 2 :=
  ⟨fun r => if r = 0 then n else 0, fun _ => []⟩

@[simp] theorem code_input_result (cs : List ℕ) (n : ℕ) :
    ((code cs).run (inputState n)).1.regs 1 = value cs n := by
  simpa [inputState] using (code_spec cs (inputState n)).2

/-- A fixed polynomial is evaluated in charged cost linear in the binary input length. -/
theorem code_input_cost_le (cs : List ℕ) (n : ℕ) :
    ((code cs).run (inputState n)).2 ≤ costConstant cs * (Nat.size n + 1) := by
  simpa [inputState] using code_cost_le cs (inputState n)

/-- Actual straight-line code exists for every polynomial used as a fixed resource budget. -/
theorem exists_code (p : Polynomial ℕ) :
    ∃ (s : Stmt 3 2) (C : ℕ), ∀ n,
      (s.run (inputState n)).1.regs 1 = p.eval n ∧
      (s.run (inputState n)).2 ≤ C * (Nat.size n + 1) := by
  obtain ⟨cs, hc⟩ := exists_coefficients p
  refine ⟨code cs, costConstant cs, fun n => ?_⟩
  exact ⟨(code_input_result cs n).trans (hc n), code_input_cost_le cs n⟩


/-- Read the input length, evaluate the fixed polynomial, and emit its natural-number value. -/
def program (cs : List ℕ) : Prog where
  R := 3
  Q := 2
  hQ := by decide
  body := .seq (.len 0 0) (.seq (code cs) (.push 1 1))

@[simp] theorem program_run (cs : List ℕ) (l : List ℕ) :
    (program cs).run l = [value cs l.length] := by
  dsimp only [program, Prog.run, Prog.init, Prog.inL, Prog.outL]
  rw [run_seq_fst, run_len_fst]
  rw [run_seq_fst, run_push_fst]
  simp only [setList_lists]
  rw [(code_spec cs _).2, code_lists]
  simp [Function.update]

@[simp] theorem program_loopFree (cs : List ℕ) : (program cs).body.loopFree = true := by
  simp [program, Stmt.loopFree]

/-- An explicit cost constant for the complete length-to-budget program. -/
def programCostConstant (cs : List ℕ) : ℕ :=
  (program cs).body.C * ((program cs).body.width + (program cs).body.csize + 1)

/-- Its charged work is linear in the actual stored input size. -/
theorem program_cost_le (cs : List ℕ) (l : List ℕ) :
    (program cs).cost l ≤ programCostConstant cs * (listSize l + 1) := by
  apply loopFree_cost_le (program cs).body (program_loopFree cs) ((program cs).init l)
  · intro r _
    simp [Prog.init]
  · intro L _
    simp only [Prog.init]
    split <;> simp [listSize]

/-- Every fixed polynomial budget has an actual `Lang.Prog` with certified semantics and cost. -/
theorem exists_program (p : Polynomial ℕ) :
    ∃ (P : Prog) (C : ℕ), ∀ l : List ℕ,
      P.run l = [p.eval l.length] ∧ P.cost l ≤ C * (listSize l + 1) := by
  obtain ⟨cs, hc⟩ := exists_coefficients p
  refine ⟨program cs, programCostConstant cs, fun l => ?_⟩
  exact ⟨(program_run cs l).trans (congrArg (fun n => [n]) (hc l.length)), program_cost_le cs l⟩

end PCP.Lang.PolynomialBudget
