import PCP.Complexity.AmplifiedSequenceLang

/-! Repetition preserves its original input-length register and external empty list. -/

namespace PCP.Lang.AmplifiedStream

private theorem seed_length (st : State 420 140) :
    (seed.run st).1.regs 414 = st.regs 414 := run_regs_frame seed 414 (by decide) st

private theorem step_length (st : State 420 140) :
    (step.run st).1.regs 414 = st.regs 414 := run_regs_frame step 414 (by decide) st

private theorem consume_length (st : State 420 140) :
    (consume.run st).1.regs 414 = st.regs 414 := run_regs_frame consume 414 (by decide) st

attribute [local irreducible] AmplifiedWorkspace.call seed step consume

theorem round_frame (P : Stmt 400 128) (st : State 420 140) (he : st.lists 139 = []) :
    ((round P).run st).1.regs 414 = st.regs 414 ∧
    ((round P).run st).1.lists 139 = [] := by
  let s := (seed.run st).1
  let u := ((AmplifiedWorkspace.call P).run s).1
  have hs : s.lists 139 = [] := (seed_run st he).2.2.1
  exact ⟨(step_length u).trans ((AmplifiedWorkspace.call_regs P s hs 414 (by decide)).trans
    (seed_length st)), (step_lists u 139 (by decide)).trans
      ((AmplifiedWorkspace.call_lists P s hs 139 (by decide)).trans hs)⟩

attribute [local irreducible] round

theorem copies_frame (P : Stmt 400 128) (k : ℕ) (st : State 420 140)
    (he : st.lists 139 = []) :
    ((copies P k).run st).1.regs 414 = st.regs 414 ∧
    ((copies P k).run st).1.lists 139 = [] := by
  induction k generalizing st with
  | zero => simp [copies, Stmt.run, Expr.eval, Function.update, he]
  | succ k ih =>
      let s := ((round P).run st).1
      have hs := round_frame P st he
      change s.regs 414 = st.regs 414 ∧ s.lists 139 = [] at hs
      have hc := consume_run s hs.2
      have hi := ih (consume.run s).1 hc.2
      rw [copies, run_seq_fst]
      change ((Stmt.ite 402 .skip (.ite 403 (.seq consume (copies P k)) .skip)).run s).1.regs
        414 = st.regs 414 ∧
        ((Stmt.ite 402 .skip (.ite 403 (.seq consume (copies P k)) .skip)).run s).1.lists
          139 = []
      simp only [run_ite_fst]
      split_ifs
      · exact hs
      · exact ⟨hi.1.trans ((consume_length s).trans hs.1), hi.2⟩
      · exact hs

end PCP.Lang.AmplifiedStream
