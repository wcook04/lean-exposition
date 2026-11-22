/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticLookupCost
import PCP.Complexity.FiniteLookupLang

/-!
# Fixed finite tables inside arithmetic expressions

A table fixed by the source machine is compiled to ordinary comparisons and
constants. The resulting term can be freely combined with arithmetic, source
reads, and conditional code, using the existing uniform operational bounds.
-/

namespace PCP.Lang.ArithmeticExpression

variable {n : ℕ}

def Term.tableFrom (base : ℕ) : List ℕ → Term n → Term n
  | [], _ => .const 0
  | a :: as, key => .cond (.bin .eq key (.const base)) (.const a)
      (tableFrom (base + 1) as key)

def Term.table (cs : List ℕ) (key : Term n) : Term n := tableFrom 0 cs key

theorem Term.eval_tableFrom (base : ℕ) (cs : List ℕ) (key : Term n) (r : Fin n → ℕ) :
    (tableFrom base cs key).eval r = FiniteLookup.value base cs (key.eval r) := by
  induction cs generalizing base with
  | nil => rfl
  | cons a as ih =>
      by_cases h : key.eval r = base
      · simp [tableFrom, Term.eval, Op.eval, FiniteLookup.value, h]
      · simp [tableFrom, Term.eval, Op.eval, FiniteLookup.value, h, ih]

@[simp] theorem Term.eval_table (cs : List ℕ) (key : Term n) (r : Fin n → ℕ) :
    (table cs key).eval r = cs.getD (key.eval r) 0 := by
  rw [table, eval_tableFrom, FiniteLookup.value_eq_getD]
  simp

/-- Each finite semantic lookup compiles to a fixed arithmetic term. -/
theorem Term.eval_finiteTable {m : ℕ} (f : Fin m → ℕ) (key : Term n) (r : Fin n → ℕ)
    (i : Fin m) (hi : key.eval r = i.val) :
    (table (List.ofFn f) key).eval r = f i := by
  rw [eval_table, hi]
  simp [List.getD_eq_getElem?_getD]

end PCP.Lang.ArithmeticExpression
