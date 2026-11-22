/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticLookupLang
import PCP.Complexity.ArithmeticExpressionCost

/-!
# Polynomial cost of finite arithmetic and stored-read computations

The source list is fixed through every computation. The caller's output buffer
and initial scratch-register contents are excluded from the bound.
-/

namespace PCP.Lang.ArithmeticLookup

open ArithmeticExpression

variable {n : ℕ}

def exprConstant (t : Term n) : ℕ :=
  (scalar t).C * ((scalar t).width + (scalar t).csize + 1)

theorem expr_cost (t : Term n) (st : State (n + 4) 3) (W : ℕ)
    (hr : ∀ i, Nat.size (inputs st i) ≤ W) :
    ((expr t).run st).2 ≤ exprConstant t * (W + 1) := by
  rw [expr, Stmt.run_rename_cost _ _ _ (Fin.castSucc_injective _) (Fin.castSucc_injective _)]
  exact scalar_cost_inputs t _ W hr

theorem term_size (t : Term n) (r : Fin n → ℕ) (W : ℕ)
    (hr : ∀ i, Nat.size (r i) ≤ W) :
    Nat.size (t.eval r) ≤ exprConstant t * (W + 1) := eval_size_le t r W hr

theorem assign_cost (dest : Fin n) (t : Term n) (st : State (n + 4) 3) (W : ℕ)
    (hr : ∀ i, Nat.size (inputs st i) ≤ W) :
    ((assign dest t).run st).2 ≤ (3 * exprConstant t + 2) * (W + 1) := by
  have he := (expr_spec t st).1
  have hc := expr_cost t st W hr
  have hv := term_size t (inputs st) W hr
  simp only [assign, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, he]
  nlinarith

theorem size_getD (l : List ℕ) (i : ℕ) : Nat.size (l.getD i 0) ≤ listSize l := by
  by_cases hi : i < l.length
  · simpa [List.getD_eq_getElem?_getD, hi] using
      (size_le_listSize (List.getElem_mem hi))
  · simp [List.getD_eq_getElem?_getD, hi]

theorem lookup_cost (dest : Fin n) (t : Term n) (st : State (n + 4) 3) (W : ℕ)
    (hr : ∀ i, Nat.size (inputs st i) ≤ W) (hl : listSize (st.lists 0) ≤ W) :
    ((lookup dest t).run st).2 ≤ (22 * (exprConstant t + 1) ^ 2) * (W + 1) ^ 2 := by
  let E := exprConstant t
  let se := ((expr t).run st).1
  have hc := expr_cost t st W hr
  have hv := term_size t (inputs st) W hr
  have he := (expr_spec t st).1
  have hs := (expr_spec t st).2.2.1
  have hb := Lookup.lookup_cost (se.restrict (lookupRegs dest) lookupLists)
  have hx : Nat.size ((se.restrict (lookupRegs dest) lookupLists).regs 0) ≤ E * (W + 1) := by
    simpa [State.restrict_regs, lookupRegs, se, leftReg] using he ▸ hv
  have hls : listSize ((se.restrict (lookupRegs dest) lookupLists).lists 0) ≤ W := by
    simpa [State.restrict_lists, lookupLists, se, hs] using hl
  have harg : listSize ((se.restrict (lookupRegs dest) lookupLists).lists 0) +
      Nat.size ((se.restrict (lookupRegs dest) lookupLists).regs 0) + 1 ≤
        (E + 1) * (W + 1) := by nlinarith
  have hpow := Nat.pow_le_pow_left harg 2
  rw [lookup, run_seq_snd, Stmt.run_rename_cost _ _ _ (lookupRegs_injective dest)
    lookupLists_injective]
  change ((expr t).run st).2 +
    (Lookup.lookup.run (se.restrict (lookupRegs dest) lookupLists)).2 + 1 ≤ _
  have hE : E ≤ (E + 1) ^ 2 := by nlinarith
  have hW : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul hE hW
  change ((expr t).run st).2 ≤ E * (W + 1) at hc
  change _ ≤ 22 * (E + 1) ^ 2 * (W + 1) ^ 2
  nlinarith [show ((E + 1) * (W + 1)) ^ 2 = (E + 1) ^ 2 * (W + 1) ^ 2 by ring]

set_option maxHeartbeats 1000000 in
-- Composition bounds contain products of symbolic program-dependent constants.
/-- Every fixed finite arithmetic/read program has a uniform quadratic charged-cost bound. -/
theorem Code.cost_bound (p : Code n) : ∃ K : ℕ, 1 ≤ K ∧
    ∀ (st : State (n + 4) 3) (W : ℕ),
      (∀ i, Nat.size (inputs st i) ≤ W) → listSize (st.lists 0) ≤ W →
      (p.compile.run st).2 ≤ K * (W + 1) ^ 2 ∧
      ∀ i, Nat.size (inputs (p.compile.run st).1 i) ≤ K * (W + 1) := by
  induction p with
  | assign dest t =>
      refine ⟨3 * exprConstant t + 3, by omega, fun st W hr _ => ?_⟩
      have hc := assign_cost dest t st W hr
      have hv := term_size t (inputs st) W hr
      have he := (assign_spec dest t st).1
      simp only [Code.compile]
      refine ⟨?_, ?_⟩
      · have hw : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
        nlinarith
      · intro i
        rw [he]
        by_cases hi : i = dest
        · subst i
          simp only [Function.update_self]
          nlinarith
        · simp only [Function.update_of_ne hi]
          have := hr i
          nlinarith
  | lookup dest t =>
      refine ⟨22 * (exprConstant t + 1) ^ 2 + 1, by omega, fun st W hr hl => ?_⟩
      have hc := lookup_cost dest t st W hr hl
      have he := (lookup_spec dest t st).1
      simp only [Code.compile]
      refine ⟨by nlinarith, ?_⟩
      intro i
      rw [he]
      by_cases hi : i = dest
      · subst i
        simp only [Function.update_self]
        have hv := (size_getD (st.lists 0) (t.eval (inputs st))).trans hl
        nlinarith
      · simp only [Function.update_of_ne hi]
        have := hr i
        nlinarith
  | seq a b iha ihb =>
      obtain ⟨A, hA, ha⟩ := iha
      obtain ⟨B, hB, hb⟩ := ihb
      refine ⟨A + B * (A + 1) ^ 2 + 1, by omega, fun st W hr hl => ?_⟩
      obtain ⟨hca, hra⟩ := ha st W hr hl
      have hWa : W ≤ A * (W + 1) := by nlinarith
      have hla : listSize ((a.compile.run st).1.lists 0) ≤ A * (W + 1) := by
        rw [(a.spec st).2.1]
        exact hl.trans hWa
      obtain ⟨hcb, hrb⟩ := hb (a.compile.run st).1 (A * (W + 1)) hra hla
      have harg : A * (W + 1) + 1 ≤ (A + 1) * (W + 1) := by nlinarith
      have hpow := Nat.pow_le_pow_left harg 2
      have heq : ((A + 1) * (W + 1)) ^ 2 = (A + 1) ^ 2 * (W + 1) ^ 2 := by ring
      have hbCost := Nat.mul_le_mul_left B hpow
      refine ⟨?_, fun i => ?_⟩
      · simp only [Code.compile, run_seq_snd]
        nlinarith
      · simp only [Code.compile, run_seq_fst]
        have hi := hrb i
        have hsmall : B * (A * (W + 1) + 1) ≤ B * (A + 1) * (W + 1) := by nlinarith
        have hAB : B * (A + 1) ≤ A + B * (A + 1) ^ 2 + 1 := by nlinarith
        exact hi.trans (hsmall.trans (Nat.mul_le_mul_right (W + 1) hAB))

end PCP.Lang.ArithmeticLookup
