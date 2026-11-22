import PCP.Complexity.AmplifiedSequenceOutput
import PCP.Complexity.PolynomialBudgetLang
import PCP.Complexity.LangAnswerEncode

/-! Packing the actual repeated verifier result into the public machine alphabet. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Machine PCP.Machine.LangSymbolBridge

def budgetR : Fin 3 → Fin 420 := ![410, 411, 412]
def budgetQ : Fin 2 → Fin 140 := ![138, 139]
def budgetSetup : Stmt 420 140 :=
  .seq (.assign 410 (.var 414))
    (.seq (.assign 411 (.const 0)) (.assign 412 (.const 0)))
def budgetCode (cs : List ℕ) : Stmt 420 140 :=
  (PolynomialBudget.code cs).rename budgetR budgetQ
def budget (cs : List ℕ) : Stmt 420 140 := .seq budgetSetup (budgetCode cs)

def emitR : Fin 4 → Fin 420 := ![403, 411, 405, 406]
def emitQ : Fin 1 → Fin 140 := ![1]
def emit : Stmt 420 140 := .seq (.copy 139 1)
  (.ite 402 (AnswerEncode.query.rename emitR emitQ) (AnswerEncode.halt.rename emitR emitQ))

def encode (cs : List ℕ) : Stmt 420 140 := .seq (budget cs) emit

private theorem budgetR_injective : Function.Injective budgetR := by decide
private theorem budgetQ_injective : Function.Injective budgetQ := by decide
private theorem emitR_injective : Function.Injective emitR := by decide
private theorem emitQ_injective : Function.Injective emitQ := by decide

theorem budget_run (cs : List ℕ) (st : State 420 140) :
    ((budget cs).run st).1.regs 411 = PolynomialBudget.value cs (st.regs 414) := by
  let s := (budgetSetup.run st).1
  have hr := congrArg Prod.fst ((PolynomialBudget.code cs).run_rename budgetR budgetQ
    budgetR_injective budgetQ_injective s)
  have hp := (PolynomialBudget.code_spec cs (s.restrict budgetR budgetQ)).2
  rw [← hr] at hp
  simpa [budget, budgetCode, s, budgetSetup, Stmt.run, Expr.eval, Function.update,
    budgetR] using hp

theorem budget_regs (cs : List ℕ) (st : State 420 140) (i : Fin 420)
    (h0 : i ≠ 410) (h1 : i ≠ 411) (h2 : i ≠ 412) :
    ((budget cs).run st).1.regs i = st.regs i := by
  rw [budget, run_seq_fst, budgetCode, (PolynomialBudget.code cs).run_rename_reg_outside]
  · simp [budgetSetup, Stmt.run, Expr.eval, Function.update, h0, h1, h2]
  · intro j
    fin_cases j
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm

theorem budget_lists (cs : List ℕ) (st : State 420 140) (L : Fin 140) :
    ((budget cs).run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp [budget, budgetSetup, budgetCode, Stmt.listWrites, Stmt.listWrites_rename]

theorem emit_run (st : State 420 140) (C : ℕ) (ho : Output st C)
    (hb : C ≤ st.regs 411) (he : st.lists 139 = []) :
    (emit.run st).1.lists 1 = code (encodeAnswer (result st)) := by
  let s := setList st 1 []
  simp only [emit, run_seq_fst, run_copy_fst, he]
  change ((Stmt.ite 402 (AnswerEncode.query.rename emitR emitQ)
    (AnswerEncode.halt.rename emitR emitQ)).run s).1.lists 1 = _
  by_cases ht : st.regs 402 = 0
  · have hbool : st.regs 403 = (decide (st.regs 403 ≠ 0)).toNat := by
      have h := ho.halt ht
      interval_cases hval : st.regs 403 <;> simp
    have hr := congrArg Prod.fst (AnswerEncode.halt.run_rename emitR emitQ
      emitR_injective emitQ_injective s)
    have hp := AnswerEncode.halt_run (s.restrict emitR emitQ)
      (decide (st.regs 403 ≠ 0)) hbool (by simp [s, emitQ])
    rw [← hr] at hp
    simpa [run_ite_fst, s, ht, result, emitR, emitQ] using hp
  · have hr := congrArg Prod.fst (AnswerEncode.query.run_rename emitR emitQ
      emitR_injective emitQ_injective s)
    have hp := AnswerEncode.query_run (s.restrict emitR emitQ)
      ((ho.query ht).trans hb) (by simp [s, emitQ])
    rw [← hr] at hp
    simpa [run_ite_fst, s, ht, result, emitR, emitQ] using hp

theorem budget_output (cs : List ℕ) (st : State 420 140) (C : ℕ) (ho : Output st C) :
    Output ((budget cs).run st).1 C := by
  have h402 := budget_regs cs st 402 (by decide) (by decide) (by decide)
  have h403 := budget_regs cs st 403 (by decide) (by decide) (by decide)
  constructor
  · simpa only [h402] using ho.tag
  · rw [h402, h403]
    exact ho.halt
  · rw [h402, h403]
    exact ho.query

theorem encode_run (cs : List ℕ) (st : State 420 140) (C : ℕ) (ho : Output st C)
    (hb : C ≤ PolynomialBudget.value cs (st.regs 414)) (he : st.lists 139 = []) :
    ((encode cs).run st).1.lists 1 = code (encodeAnswer (result st)) := by
  have he' : ((budget cs).run st).1.lists 139 = [] := (budget_lists cs st 139).trans he
  have hb' : C ≤ ((budget cs).run st).1.regs 411 := by rwa [budget_run]
  rw [encode, run_seq_fst, emit_run _ C (budget_output cs st C ho) hb' he']
  simp only [result, budget_regs cs st 402 (by decide) (by decide) (by decide),
    budget_regs cs st 403 (by decide) (by decide) (by decide)]

end PCP.Lang.AmplifiedStream
