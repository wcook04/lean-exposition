/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost
import Mathlib.Data.List.OfFn

/-!
# Straight-line programs for fixed finite lookup tables

A fixed table compiles to a finite chain of comparisons and constant assignments.
The generated `Lang` statement handles every natural input index, returning zero
outside the table, preserves its input and all lists, and has charged cost linear
in the binary input length. Table size affects only the fixed program constant.
No abstract lookup operation or machine compiler hypothesis appears in the proofs.
-/

namespace PCP.Lang.FiniteLookup

/-- The semantic lookup at a fixed base address. -/
def value (base : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, n => if n = base then a else value (base + 1) as n

/-- Input is register zero, output is one, and registers two and three are scratch. -/
def code (base : ℕ) : List ℕ → Stmt 4 2
  | [] => .assign 1 (.const 0)
  | a :: as => .seq (.assign 2 (.const base))
      (.seq (.assign 3 (.eq 0 2)) (.ite 3 (.assign 1 (.const a)) (code (base + 1) as)))

theorem code_spec (base : ℕ) (cs : List ℕ) (st : State 4 2) :
    ((code base cs).run st).1.regs 0 = st.regs 0 ∧
      ((code base cs).run st).1.regs 1 = value base cs (st.regs 0) := by
  induction cs generalizing base st with
  | nil => simp [code, value, Stmt.run, Expr.eval, Function.update]
  | cons a as ih =>
      let next := setReg (setReg st 2 base) 3 (if st.regs 0 = base then 1 else 0)
      have hnext : next.regs 0 = st.regs 0 := by simp [next, Function.update]
      have ht := ih (base + 1) next
      rw [hnext] at ht
      by_cases hn : st.regs 0 = base
      · simp [code, value, Stmt.run, Expr.eval, Function.update, hn]
      · simpa [code, Stmt.run, Expr.eval, Function.update, value, hn, next] using ht

@[simp] theorem code_listWrites (base : ℕ) (cs : List ℕ) : (code base cs).listWrites = [] := by
  induction cs generalizing base <;> simp [code, Stmt.listWrites, *]

theorem code_lists (base : ℕ) (cs : List ℕ) (st : State 4 2) :
    ((code base cs).run st).1.lists = st.lists := by
  funext L
  exact run_lists_frame (code base cs) L (by simp) st

@[simp] theorem code_loopFree (base : ℕ) (cs : List ℕ) : (code base cs).loopFree = true := by
  induction cs generalizing base <;> simp [code, Stmt.loopFree, *]

@[simp] theorem code_lUses (base : ℕ) (cs : List ℕ) : (code base cs).lUses = [] := by
  induction cs generalizing base <;> simp [code, Stmt.lUses, *]

theorem value_below {base n : ℕ} (cs : List ℕ) (hn : n < base) : value base cs n = 0 := by
  induction cs generalizing base with
  | nil => rfl
  | cons a as ih =>
      rw [value, ite_eq_right (by omega)]
      exact ih (by omega)

/-- The comparison chain agrees with ordinary zero-padded list lookup. -/
theorem value_eq_getD (base : ℕ) (cs : List ℕ) (n : ℕ) :
    value base cs n = if base ≤ n then cs.getD (n - base) 0 else 0 := by
  by_cases hn : base ≤ n
  · rw [ite_eq_left hn]
    induction cs generalizing base with
    | nil => simp [value]
    | cons a as ih =>
      by_cases he : n = base
      · simp [value, he]
      · rw [value, ite_eq_right he]
        have hb : base + 1 ≤ n := by omega
        rw [ih (base + 1) hb]
        have hd : n - base = n - (base + 1) + 1 := by omega
        rw [hd]
        simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right hn]
    exact value_below cs (by omega)

/-- The generated zero-based program implements an ordinary finite stored table. -/
theorem lookup_spec (cs : List ℕ) (st : State 4 2) :
    ((code 0 cs).run st).1.regs 1 = cs.getD (st.regs 0) 0 := by
  rw [(code_spec 0 cs st).2, value_eq_getD]
  simp

/-- Every genuinely finite function can be compiled by listing its values once. -/
theorem finite_spec {n : ℕ} (f : Fin n → ℕ) (st : State 4 2) (i : Fin n)
    (hi : st.regs 0 = i.val) :
    ((code 0 (List.ofFn f)).run st).1.regs 1 = f i := by
  rw [lookup_spec, hi]
  simp [List.getD_eq_getElem?_getD]

/-- The fixed table determines this explicit operational constant. -/
def costConstant (cs : List ℕ) : ℕ :=
  (code 0 cs).C * ((code 0 cs).width + (code 0 cs).csize + 1)

def inputState (n : ℕ) : State 4 2 :=
  ⟨fun r => if r = 0 then n else 0, fun _ => []⟩

/-- Charged cost is linear in the input bit length even on an out-of-range index. -/
theorem lookup_cost (cs : List ℕ) (n : ℕ) :
    ((code 0 cs).run (inputState n)).2 ≤ costConstant cs * (Nat.size n + 1) := by
  apply loopFree_cost_le (code 0 cs) (code_loopFree 0 cs) (inputState n)
  · intro r _
    simp only [inputState]
    split <;> simp
  · intro L hL
    simp at hL

end PCP.Lang.FiniteLookup
