/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowPhysical
import PCP.Complexity.QueryHistoryLang

/-!
# Reading a Hadamard row from the shared global history

Every physical address is read using the exact earliest-match rule. Missing
answers return zero, and repeated inconsistent histories are handled unchanged.
-/

namespace PCP.Lang.HadamardRow

/-- History input registers and work arrays are disjoint from stored row inputs. -/
def historyRegs (i : Fin 8) : Fin 100 := ⟨66 + i.val, by omega⟩
def historyLists : Fin 4 → Fin 32 := ![30, 31, 28, 0]

theorem historyRegs_injective : Function.Injective historyRegs := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa only [historyRegs, Nat.add_left_cancel_iff] using hh

theorem historyLists_injective : Function.Injective historyLists := by decide

def readHistory : Stmt 100 32 := QueryHistory.program.rename historyRegs historyLists

theorem readHistory_run (st : State 100 32) :
    (readHistory.run st).1.regs 68 =
      QueryHistory.read (st.lists 30) (st.lists 31) (st.regs 66) := by
  have h := congrArg (fun a : State 8 4 × ℕ => a.1.regs 2)
    (QueryHistory.program.run_rename historyRegs historyLists historyRegs_injective
      historyLists_injective st)
  have hh := h.trans (QueryHistory.program_run (st.restrict historyRegs historyLists)).1
  unfold readHistory
  simpa only [State.restrict_regs, State.restrict_lists,
    show historyRegs 2 = (68 : Fin 100) from rfl,
    show historyRegs 0 = (66 : Fin 100) from rfl,
    show historyLists 0 = (30 : Fin 32) from rfl,
    show historyLists 1 = (31 : Fin 32) from rfl] using hh

def answerBody : Stmt 100 32 :=
  .seq (.pop 25 66 65) (.seq readHistory (.push 29 68))

theorem answerBody_step (z : ℕ) (zs : List ℕ) (st : State 100 32)
    (hz : st.lists 25 = z :: zs) :
    (answerBody.run st).1.lists 25 = zs ∧
      (answerBody.run st).1.lists 29 =
        QueryHistory.read (st.lists 30) (st.lists 31) z :: st.lists 29 := by
  let u := setReg (setReg (setList st 25 zs) 66 z) 65 1
  have hr := readHistory_run u
  have h25 := run_lists_frame readHistory 25 (by decide) u
  have h29 := run_lists_frame readHistory 29 (by decide) u
  dsimp only [u] at hr h25 h29
  simp only [answerBody, run_seq_fst, run_pop_cons_fst st 25 66 65 hz]
  generalize hv : (readHistory.run (setReg (setReg (setList st 25 zs) 66 z) 65 1)).1 = v at *
  simp [run_push_fst, Function.update, hr, h25, h29]

theorem answerBody_sources (st : State 100 32) :
    (answerBody.run st).1.lists 30 = st.lists 30 ∧
      (answerBody.run st).1.lists 31 = st.lists 31 := by
  exact ⟨run_lists_frame answerBody 30 (by decide) st,
    run_lists_frame answerBody 31 (by decide) st⟩

theorem answer_iterate (zs : List ℕ) (c : ℕ) (st : State 100 32)
    (hz : st.lists 25 = zs) :
    (iterate answerBody.run c zs.length st).1.lists 29 =
      (zs.map (QueryHistory.read (st.lists 30) (st.lists 31))).reverse ++ st.lists 29 := by
  induction zs generalizing st with
  | nil => rfl
  | cons z zs ih =>
      have hs := answerBody_step z zs st hz
      have hf := answerBody_sources st
      simp only [List.length_cons, iterate_succ_fst]
      generalize hu : (answerBody.run st).1 = u at *
      rw [ih u hs.1, hf.1, hf.2, hs.2]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]

/-- Physical addresses are supplied in list `26`; collected answers appear in list `29`. -/
def collectAnswers : Stmt 100 32 :=
  .seq (.copy 7 29) (.seq (.copy 26 25) (.seq (.len 25 58)
    (.seq (.loop 58 answerBody) (.rev 29))))

theorem collectAnswers_run (zs : List ℕ) (st : State 100 32)
    (hz : st.lists 26 = zs) (he : st.lists 7 = []) :
    (collectAnswers.run st).1.lists 29 =
      zs.map (QueryHistory.read (st.lists 30) (st.lists 31)) := by
  let u := setReg (setList (setList st 29 []) 25 zs) 58 zs.length
  have hh := answer_iterate zs (Nat.size zs.length + 1) u (by simp [u])
  simp only [collectAnswers, run_seq_fst, run_copy_fst, run_len_fst, run_loop_fst,
    setReg_regs, setList_regs, setList_lists, Function.update, Fin.reduceEq,
    dite_false, dite_true, he, hz]
  change ((Stmt.rev 29).run (iterate answerBody.run
    (Nat.size zs.length + 1) zs.length u).1).1.lists 29 = _
  generalize hv : (iterate answerBody.run (Nat.size zs.length + 1) zs.length u).1 = v at *
  simp [run_rev_fst, hh, u, Function.update]

/-- The history and physical query trace remain available to the outer protocol. -/
theorem collectAnswers_frame (st : State 100 32) :
    (collectAnswers.run st).1.lists 26 = st.lists 26 ∧
      (collectAnswers.run st).1.lists 30 = st.lists 30 ∧
      (collectAnswers.run st).1.lists 31 = st.lists 31 := by
  exact ⟨run_lists_frame collectAnswers 26 (by decide) st,
    run_lists_frame collectAnswers 30 (by decide) st,
    run_lists_frame collectAnswers 31 (by decide) st⟩

/-- The correspondence is for arbitrary global Boolean answer histories. -/
theorem collectAnswers_bool (zs hs : List ℕ) (bs : List Bool) (st : State 100 32)
    (hz : st.lists 26 = zs) (he : st.lists 7 = [])
    (hh : st.lists 30 = hs) (hb : st.lists 31 = bs.map Bool.toNat) :
    (collectAnswers.run st).1.lists 29 =
      zs.map (fun a => (QueryTree.answersOracle hs bs a).toNat) := by
  rw [collectAnswers_run zs st hz he, hh, hb]
  exact List.map_congr_left fun z _ => QueryHistory.read_bool hs bs z

end PCP.Lang.HadamardRow
