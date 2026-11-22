/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.Lang

/-! # Fixed-list output programs with exact charged cost -/

namespace PCP.Lang.Constant

def write : List ℕ → Stmt 1 2
  | [] => .skip
  | a :: xs => .seq (write xs) (.seq (.assign 0 (.const a)) (.push 1 0))

theorem write_output (xs : List ℕ) (st : State 1 2) :
    ((write xs).run st).1.lists 1 = xs ++ st.lists 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [write, Stmt.run, Expr.eval, ih]

theorem write_cost (xs : List ℕ) (st : State 1 2) :
    ((write xs).run st).2 = 3 * listSize xs + xs.length + 1 := by
  induction xs with
  | nil => simp [write, Stmt.run, listSize]
  | cons a xs ih =>
      simp only [write, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ih,
        setReg, Function.update_self, listSize, List.map_cons, List.sum_cons, List.length_cons]
      omega

def program (xs : List ℕ) : Prog where
  R := 1
  Q := 2
  hQ := by decide
  body := write xs

theorem program_run (xs input : List ℕ) : (program xs).run input = xs := by
  exact (write_output xs ((program xs).init input)).trans (List.append_nil xs)

theorem program_cost (xs input : List ℕ) :
    (program xs).cost input = 3 * listSize xs + xs.length + 1 := write_cost xs _

end PCP.Lang.Constant
