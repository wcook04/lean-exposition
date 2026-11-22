/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.AmplifiedProtocolParse

/-! # Computing the exact canonical randomness budget from the stored graph -/

namespace PCP.Lang.AmplifiedProtocolSetup

open PCP.Machine PCP.Machine.LangSymbolBridge

def prepareBudget : Stmt 420 140 := .seq (.len 130 408)
  (.seq (.assign 409 (.const 2)) (.assign 0 (.add 408 409)))

def clog : Stmt 420 140 :=
  Clog.program.rename (Fin.castLE (by decide)) Fin.elim0

def finishBudget : Stmt 420 140 := .seq (.assign 409 (.const 32000000))
  (.seq (.assign 400 (.mul 2 409)) (.assign 400 (.add 400 409)))

def budget : Stmt 420 140 := .seq prepareBudget (.seq clog finishBudget)

theorem clog_result (st : State 420 140) :
    ((clog.run st).1.restrict (Fin.castLE (by decide)) Fin.elim0, (clog.run st).2) =
      Clog.program.run (st.restrict (Fin.castLE (by decide)) Fin.elim0) :=
  Clog.program.run_rename _ _ (Fin.castLE_injective _) (fun i => Fin.elim0 i) st

theorem clog_run (st : State 420 140) :
    (clog.run st).1.regs 2 = Nat.clog 2 (st.regs 0) := by
  have h := Clog.program_run (st.restrict (Fin.castLE (by decide)) Fin.elim0)
  rw [← clog_result] at h
  exact h

theorem clog_lists (st : State 420 140) : (clog.run st).1.lists = st.lists := by
  funext L
  apply Stmt.run_rename_list_outside
  intro i
  exact Fin.elim0 i

theorem clog_reg (st : State 420 140) (i : Fin 420) (hi : 5 ≤ i.val) :
    (clog.run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

attribute [local irreducible] clog

theorem budget_run (st : State 420 140) :
    (budget.run st).1.regs 400 =
      PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget (st.lists 130).length ∧
      (budget.run st).1.lists = st.lists ∧ (budget.run st).1.regs 414 = st.regs 414 := by
  have h := clog_run (prepareBudget.run st).1
  have hl := clog_lists (prepareBudget.run st).1
  have hr := clog_reg (prepareBudget.run st).1 414 (by decide)
  have hprep0 : (prepareBudget.run st).1.regs 0 = (st.lists 130).length + 2 := by
    simp [prepareBudget, Stmt.run, Expr.eval, Function.update]
  rw [hprep0] at h
  have hprepl : (prepareBudget.run st).1.lists = st.lists := by
    simp [prepareBudget, Stmt.run]
  have hprepr : (prepareBudget.run st).1.regs 414 = st.regs 414 :=
    run_regs_frame prepareBudget 414 (by decide) st
  rw [hprepl] at hl
  rw [hprepr] at hr
  simp only [budget, run_seq_fst]
  generalize hu : (clog.run (prepareBudget.run st).1).1 = u at *
  refine ⟨?_, ?_, ?_⟩
  · simp [finishBudget, Stmt.run, Expr.eval, Function.update, h,
      PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget, Nat.mul_comm]
  · simpa [finishBudget, Stmt.run] using hl
  · simpa [finishBudget, Stmt.run, Function.update] using hr

def program : Stmt 420 140 := .seq parse budget

attribute [local irreducible] parse budget
  PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget

theorem parsed_ready (t : List Bool × List Bool × List Bool) (st out : State 420 140)
    (b : ℕ) (hp : Parsed t st) (hb : out.regs 400 = b)
    (hl : out.lists = st.lists) (hr : out.regs 414 = st.regs 414) :
    AmplifiedStream.Ready out b t.1 t.2.1 t.2.2 ∧
      out.regs 414 = (encodeTriple t).length ∧ out.lists 1 = [] :=
  ⟨⟨hb, (congrFun hl 130).trans hp.graph, (congrFun hl 131).trans hp.bits,
    (congrFun hl 132).trans hp.answers, (congrFun hl 139).trans hp.empty⟩,
    hr.trans hp.length, (congrFun hl 1).trans hp.output⟩

theorem budget_ready (t : List Bool × List Bool × List Bool) (st : State 420 140)
    (hp : Parsed t st) :
    AmplifiedStream.Ready (budget.run st).1
      (PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget t.1.length) t.1 t.2.1 t.2.2 ∧
      (budget.run st).1.regs 414 = (encodeTriple t).length ∧
      (budget.run st).1.lists 1 = [] := by
  have hb := budget_run st
  have hn : (st.lists 130).length = t.1.length := by
    simpa only [List.length_map] using congrArg List.length hp.graph
  exact parsed_ready t st (budget.run st).1 _ hp
    (hb.1.trans (congrArg PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget hn)) hb.2.1 hb.2.2

theorem program_run (t : List Bool × List Bool × List Bool) :
    AmplifiedStream.Ready (program.run (AmplifiedProtocol.initial (code (encodeTriple t)))).1
      (PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget t.1.length) t.1 t.2.1 t.2.2 ∧
      (program.run (AmplifiedProtocol.initial (code (encodeTriple t)))).1.regs 414 =
        (encodeTriple t).length ∧
      (program.run (AmplifiedProtocol.initial (code (encodeTriple t)))).1.lists 1 = [] := by
  rw [program, run_seq_fst]
  exact budget_ready t _ (parse_run t)

theorem setup : AmplifiedProtocol.Setup program :=
  ⟨fun t => ⟨(program_run t).1, (program_run t).2.1⟩⟩

end PCP.Lang.AmplifiedProtocolSetup
