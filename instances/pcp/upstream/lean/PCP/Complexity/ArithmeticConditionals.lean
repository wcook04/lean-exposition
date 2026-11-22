/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticExpressionLang

/-! # Arithmetic expression helpers with direct conditional semantics -/

namespace PCP.Lang.ArithmeticExpression.Term

variable {n : ℕ}

def iteEq (a b yes no : Term n) : Term n := .cond (.bin .eq a b) yes no

def iteLt (a b yes no : Term n) : Term n := .cond (.bin .lt a b) yes no

def minimum (a b : Term n) : Term n := iteLt a b a b

private theorem bit_test (p : Prop) [Decidable p] :
    ((if p then 1 else 0) : ℕ) ≠ 0 ↔ p := by by_cases h : p <;> simp [h]

theorem eval_iteEq (a b yes no : Term n) (r : Fin n → ℕ) :
    (iteEq a b yes no).eval r = if a.eval r = b.eval r then yes.eval r else no.eval r := by
  change (if (if a.eval r = b.eval r then 1 else 0) ≠ 0 then yes.eval r else no.eval r) = _
  simp only [bit_test]

theorem eval_iteLt (a b yes no : Term n) (r : Fin n → ℕ) :
    (iteLt a b yes no).eval r = if a.eval r < b.eval r then yes.eval r else no.eval r := by
  change (if (if a.eval r < b.eval r then 1 else 0) ≠ 0 then yes.eval r else no.eval r) = _
  simp only [bit_test]

theorem eval_minimum (a b : Term n) (r : Fin n → ℕ) :
    (minimum a b).eval r = min (a.eval r) (b.eval r) := by
  rw [minimum, eval_iteLt]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (by omega)).symm

end PCP.Lang.ArithmeticExpression.Term
