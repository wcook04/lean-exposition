/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.AmplifiedProtocolBudget
import PCP.Complexity.AmplifiedProtocolParseCost

/-! # Concrete quadratic cost certificate for public protocol setup -/

namespace PCP.Lang.AmplifiedProtocolSetup

open PCP.Machine PCP.Machine.LangSymbolBridge

attribute [local irreducible] clog parse budget

def fixedConstant (p : Stmt 420 140) : ℕ := p.C * (p.width + p.csize + 1)

def budgetConstant : ℕ := fixedConstant prepareBudget +
  (Clog.setup.C * 4 + Clog.body.C * 10 + 5) + fixedConstant finishBudget + 2

theorem prepareBudget_cost (st : State 420 140) :
    (prepareBudget.run st).2 ≤ fixedConstant prepareBudget * (listSize (st.lists 130) + 1) := by
  apply loopFree_cost_le prepareBudget (by decide)
  · intro i hi
    have he : prepareBudget.uses = [] := by decide
    simp [he] at hi
  · intro L hL
    have he : prepareBudget.lUses = [130] := by decide
    simp only [he, List.mem_singleton] at hL
    subst L
    rfl

theorem finishBudget_cost (W : ℕ) (st : State 420 140) (h2 : Nat.size (st.regs 2) ≤ W) :
    (finishBudget.run st).2 ≤ fixedConstant finishBudget * (W + 1) := by
  apply loopFree_cost_le finishBudget (by decide)
  · intro i hi
    have he : finishBudget.uses = [2] := by decide
    simp only [he, List.mem_singleton] at hi
    subst i
    exact h2
  · intro L hL
    have he : finishBudget.lUses = [] := by decide
    simp [he] at hL

theorem budget_cost (st : State 420 140) :
    (budget.run st).2 ≤ budgetConstant * (listSize (st.lists 130) + 3) ^ 2 := by
  let B := listSize (st.lists 130)
  have hlen := length_le_listSize (st.lists 130)
  have hp := prepareBudget_cost st
  have h0 : (prepareBudget.run st).1.regs 0 = (st.lists 130).length + 2 := by
    simp [prepareBudget, Stmt.run, Expr.eval, Function.update]
  have hc := Clog.program_cost ((prepareBudget.run st).1.restrict
    (Fin.castLE (by decide)) Fin.elim0)
  rw [← clog_result] at hc
  change (clog.run (prepareBudget.run st).1).2 ≤
    (Clog.setup.C * 4 + Clog.body.C * 10 + 5) * ((prepareBudget.run st).1.regs 0 + 1) ^ 2 at hc
  rw [h0] at hc
  have hval := clog_run (prepareBudget.run st).1
  rw [h0] at hval
  unfold budget
  simp only [run_seq_snd]
  generalize hu : (clog.run (prepareBudget.run st).1).1 = u at *
  have hsize : Nat.size (u.regs 2) ≤ (st.lists 130).length + 2 := by
    rw [hval]
    exact (size_le_self _).trans (clog_le_self _)
  have hf := finishBudget_cost _ u hsize
  have harg : (st.lists 130).length + 2 + 1 ≤ B + 3 := by dsimp [B]; omega
  have hc' := hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hpoly : B + 3 ≤ (B + 3) ^ 2 := Nat.le_pow (by decide)
  have hf' := hf.trans (Nat.mul_le_mul_left _ (harg.trans hpoly))
  have hp' := hp.trans (Nat.mul_le_mul_left _
    ((show listSize (st.lists 130) + 1 ≤ B + 3 by dsimp [B]; omega).trans hpoly))
  have h1 : 1 ≤ (B + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  change _ ≤ budgetConstant * (B + 3) ^ 2
  unfold budgetConstant
  nlinarith only [hp', hc', hf', h1]

def costConstant : ℕ := 2001 + 9 * budgetConstant

theorem program_cost (t : List Bool × List Bool × List Bool) :
    (program.run (AmplifiedProtocol.initial (code (encodeTriple t)))).2 ≤
      costConstant * ((encodeTriple t).length + 1) ^ 2 := by
  have hp := parse_run t
  have hpc := parse_cost t
  have hb := budget_cost (parse.run (AmplifiedProtocol.initial (code (encodeTriple t)))).1
  rw [hp.graph] at hb
  have hsize := AmplifiedStream.boolList_size t.1
  have hlen : t.1.length ≤ (encodeTriple t).length := by simp; omega
  have harg : listSize (t.1.map Bool.toNat) + 3 ≤ 3 * ((encodeTriple t).length + 1) := by omega
  have hb' := hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have h1 : 1 ≤ ((encodeTriple t).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [program, run_seq_snd]
  unfold costConstant
  nlinarith only [hpc, hb', h1]

end PCP.Lang.AmplifiedProtocolSetup
