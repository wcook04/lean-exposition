import PCP.Complexity.AmplifiedWorkspace
import PCP.Complexity.LangTakePad
import PCP.Complexity.LangQueryStep

/-! Seed extraction, answer consumption and result selection for repetition. -/

namespace PCP.Lang.AmplifiedStream

def seedR : Fin 3 → Fin 420 := ![400, 405, 406]
def seedQ : Fin 3 → Fin 140 := ![131, 133, 139]
def seed : Stmt 420 140 := TakePad.program.rename seedR seedQ

def answerR : Fin 3 → Fin 420 := ![407, 405, 406]
def answerQ : Fin 3 → Fin 140 := ![132, 135, 139]
def consume : Stmt 420 140 :=
  .seq (.len 103 407) (TakePad.program.rename answerR answerQ)

def stepR : Fin 4 → Fin 420 := ![404, 403, 402, 300]
def stepQ : Fin 3 → Fin 140 := ![103, 132, 137]
def step : Stmt 420 140 := QueryStep.program.rename stepR stepQ

private theorem seedR_injective : Function.Injective seedR := by decide
private theorem seedQ_injective : Function.Injective seedQ := by decide
private theorem answerR_injective : Function.Injective answerR := by decide
private theorem answerQ_injective : Function.Injective answerQ := by decide
private theorem stepR_injective : Function.Injective stepR := by decide
private theorem stepQ_injective : Function.Injective stepQ := by decide

theorem seed_run (st : State 420 140) (he : st.lists 139 = []) :
    (seed.run st).1.lists 131 = (st.lists 131).drop (st.regs 400) ∧
    (seed.run st).1.lists 133 = TakePad.take (st.regs 400) (st.lists 131) ∧
    (seed.run st).1.lists 139 = [] ∧ (seed.run st).1.regs 400 = st.regs 400 := by
  have hr := congrArg Prod.fst (TakePad.program.run_rename seedR seedQ
    seedR_injective seedQ_injective st)
  have h := TakePad.program_run (st.restrict seedR seedQ) he
  rw [← hr] at h
  exact h

theorem seed_graph (st : State 420 140) : (seed.run st).1.lists 130 = st.lists 130 :=
  run_lists_frame seed 130 (by decide) st

theorem seed_answers (st : State 420 140) : (seed.run st).1.lists 132 = st.lists 132 :=
  run_lists_frame seed 132 (by decide) st

theorem seed_cost (st : State 420 140) (he : st.lists 139 = []) :
    (seed.run st).2 ≤ 20*(listSize (st.lists 131)+st.regs 400+1)^2 := by
  have hr := congrArg Prod.snd (TakePad.program.run_rename seedR seedQ
    seedR_injective seedQ_injective st)
  dsimp only [Prod.snd] at hr
  rw [show (seed.run st).2 = _ from hr]
  exact TakePad.program_cost _ he

theorem consume_run (st : State 420 140) (he : st.lists 139 = []) :
    (consume.run st).1.lists 132 = (st.lists 132).drop (st.lists 103).length ∧
    (consume.run st).1.lists 139 = [] := by
  let s := setReg st 407 (st.lists 103).length
  have hr := congrArg Prod.fst (TakePad.program.run_rename answerR answerQ
    answerR_injective answerQ_injective s)
  have h := TakePad.program_run (s.restrict answerR answerQ) he
  rw [← hr] at h
  exact ⟨h.1, h.2.2.1⟩

theorem consume_graph (st : State 420 140) :
    (consume.run st).1.lists 130 = st.lists 130 :=
  run_lists_frame consume 130 (by decide) st

theorem consume_bits (st : State 420 140) :
    (consume.run st).1.lists 131 = st.lists 131 :=
  run_lists_frame consume 131 (by decide) st

theorem consume_budget (st : State 420 140) :
    (consume.run st).1.regs 400 = st.regs 400 :=
  run_regs_frame consume 400 (by decide) st

theorem consume_cost (st : State 420 140) (he : st.lists 139 = []) :
    (consume.run st).2 ≤ listSize (st.lists 103)+Nat.size (st.lists 103).length+2+
      20*(listSize (st.lists 132)+(st.lists 103).length+1)^2 := by
  let s := setReg st 407 (st.lists 103).length
  have hr := congrArg Prod.snd (TakePad.program.run_rename answerR answerQ
    answerR_injective answerQ_injective s)
  dsimp only [Prod.snd] at hr
  have h := TakePad.program_cost (s.restrict answerR answerQ) he
  rw [← hr] at h
  change ((TakePad.program.rename answerR answerQ).run s).2 ≤
    20*(listSize (st.lists 132)+(st.lists 103).length+1)^2 at h
  change listSize (st.lists 103)+Nat.size (st.lists 103).length+1+
    ((TakePad.program.rename answerR answerQ).run s).2+1 ≤ _
  omega

theorem step_run (st : State 420 140) :
    (step.run st).1.regs 403 = (if (st.lists 132).length < (st.lists 103).length
      then (st.lists 103).getD (st.lists 132).length 0 else st.regs 300) ∧
    (step.run st).1.regs 402 =
      (if (st.lists 132).length < (st.lists 103).length then 1 else 0) := by
  have hr := congrArg Prod.fst (QueryStep.program.run_rename stepR stepQ
    stepR_injective stepQ_injective st)
  have h := QueryStep.program_run (st.restrict stepR stepQ)
  rw [← hr] at h
  exact h

theorem step_lists (st : State 420 140) (L : Fin 140) (hL : L ≠ 137) :
    (step.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp [step, Stmt.rename, QueryStep.program, QueryStep.setup, QueryStep.scan,
    QueryStep.pop, Stmt.listWrites, stepQ, hL]

theorem step_budget (st : State 420 140) :
    (step.run st).1.regs 400 = st.regs 400 :=
  run_regs_frame step 400 (by decide) st

theorem step_cost (st : State 420 140) :
    (step.run st).2 ≤ 20*(listSize (st.lists 103)+listSize (st.lists 132)+
      Nat.size (st.regs 300)+2)^2 := by
  have hr := congrArg Prod.snd (QueryStep.program.run_rename stepR stepQ
    stepR_injective stepQ_injective st)
  dsimp only [Prod.snd] at hr
  rw [show (step.run st).2 = _ from hr]
  exact QueryStep.program_cost _

end PCP.Lang.AmplifiedStream
