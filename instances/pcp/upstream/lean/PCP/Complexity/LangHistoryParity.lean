import PCP.Complexity.QueryHistoryLang
import PCP.Complexity.LangRenaming
import PCP.Algebraic.BinarySeedPadding

/-!
# Parity of a stored list of physical proof queries

Each query uses the earliest matching answer in the original history. The
sources are retained, repeated queries are read repeatedly, and missing answers
contribute zero. The accumulator is reduced modulo two at every step.
-/

namespace PCP.Lang.HistoryParity

open PCP.Algebraic

def history : Stmt 12 6 := QueryHistory.program.rename (Fin.castAdd 4) (Fin.castAdd 2)

def body : Stmt 12 6 := .seq (.pop 5 0 7)
  (.seq history (.seq (.assign 8 (.add 8 2)) (.assign 8 (.mod 8 10))))

def setup : Stmt 12 6 := .seq (.copy 4 5) (.seq (.len 4 9)
  (.seq (.assign 8 (.const 0)) (.assign 10 (.const 2))))

def parity : Stmt 12 6 := .seq setup (.loop 9 body)

def finish : Stmt 12 6 := .seq (.assign 11 (.const 0)) (.assign 11 (.eq 8 11))

def program : Stmt 12 6 := .seq parity finish

def Context (qs bs xs : List ℕ) (st : State 12 6) : Prop :=
  st.lists 0 = qs ∧ st.lists 1 = bs ∧ st.lists 4 = xs ∧ st.regs 10 = 2

theorem history_result (st : State 12 6) :
    ((history.run st).1.restrict (Fin.castAdd 4) (Fin.castAdd 2), (history.run st).2) =
      QueryHistory.program.run (st.restrict (Fin.castAdd 4) (Fin.castAdd 2)) := by
  unfold history
  exact Stmt.run_rename _ _ _ (Fin.castAdd_injective 8 4) (Fin.castAdd_injective 4 2) st

theorem history_run (st : State 12 6) :
    (history.run st).1.regs 2 = QueryHistory.read (st.lists 0) (st.lists 1) (st.regs 0) ∧
    (history.run st).1.lists 0 = st.lists 0 ∧ (history.run st).1.lists 1 = st.lists 1 := by
  have h := QueryHistory.program_run (st.restrict (Fin.castAdd 4) (Fin.castAdd 2))
  rw [← history_result st] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem history_reg (st : State 12 6) (r : Fin 12) (hr : 8 ≤ r.val) :
    (history.run st).1.regs r = st.regs r := by
  exact QueryHistory.program.run_rename_reg_outside (Fin.castAdd 4) (Fin.castAdd 2) r
    (by intro j hj; have := congrArg Fin.val hj; simp only [Fin.val_castAdd] at this; omega) st

theorem history_list (st : State 12 6) (L : Fin 6) (hL : 4 ≤ L.val) :
    (history.run st).1.lists L = st.lists L := by
  exact QueryHistory.program.run_rename_list_outside (Fin.castAdd 4) (Fin.castAdd 2) L
    (by intro j hj; have := congrArg Fin.val hj; simp only [Fin.val_castAdd] at this; omega) st

theorem body_step (qs bs xs : List ℕ) (a : ℕ) (as : List ℕ) (st : State 12 6)
    (hc : Context qs bs xs st) (hw : st.lists 5 = a :: as) :
    (body.run st).1.regs 8 = (st.regs 8 + QueryHistory.read qs bs a) % 2 ∧
    (body.run st).1.lists 5 = as ∧ Context qs bs xs (body.run st).1 := by
  let s := setReg (setReg (setList st 5 as) 0 a) 7 1
  have hs0 : s.regs 0 = a := by simp [s, Function.update]
  have hs8 : s.regs 8 = st.regs 8 := by simp [s, Function.update]
  have hs10 : s.regs 10 = 2 := by simpa [s, Function.update] using hc.2.2.2
  have hsqs : s.lists 0 = qs := by simpa [s, Function.update] using hc.1
  have hsbs : s.lists 1 = bs := by simpa [s, Function.update] using hc.2.1
  have hsxs : s.lists 4 = xs := by simpa [s, Function.update] using hc.2.2.1
  have hp : ((Stmt.pop 5 0 7 : Stmt 12 6).run st).1 = s := by
    simp [Stmt.run, hw, s]
  have hh := history_run s
  have h8 := history_reg s 8 (by decide)
  have h10 := history_reg s 10 (by decide)
  have h4 := history_list s 4 (by decide)
  have h5 := history_list s 5 (by decide)
  rw [hs0, hsqs, hsbs] at hh
  rw [hs8] at h8
  rw [hs10] at h10
  rw [hsxs] at h4
  have hs5 : s.lists 5 = as := by simp [s]
  rw [hs5] at h5
  simp only [body, run_seq_fst, hp, run_assign_fst, Expr.eval, Context, setReg_regs,
    setReg_lists, Function.update_self, Function.update_of_ne (by decide : (10 : Fin 12) ≠ 8),
    hh.1, hh.2.1, hh.2.2, h8, h10, h4, h5]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem iterate_result (qs bs xs ws : List ℕ) (c : ℕ) (st : State 12 6)
    (hc : Context qs bs xs st) (hw : st.lists 5 = ws) (ha : st.regs 8 < 2) :
    (iterate body.run c ws.length st).1.regs 8 =
      (st.regs 8 + (ws.map (QueryHistory.read qs bs)).sum) % 2 ∧
    Context qs bs xs (iterate body.run c ws.length st).1 := by
  induction ws generalizing st with
  | nil =>
      simp only [List.length_nil, iterate, List.map_nil, List.sum_nil, Nat.add_zero]
      exact ⟨(Nat.mod_eq_of_lt ha).symm, hc⟩
  | cons a as ih =>
      have h := body_step qs bs xs a as st hc hw
      have ha' : (body.run st).1.regs 8 < 2 := by rw [h.1]; omega
      have hi := ih (body.run st).1 h.2.2 h.2.1 ha'
      rw [List.length_cons, iterate_succ_fst]
      refine ⟨?_, hi.2⟩
      rw [hi.1, h.1, List.map_cons, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc]

/-- The numeric output is the parity of precisely the requested physical reads. -/
theorem parity_run (st : State 12 6) :
    (parity.run st).1.regs 8 =
      (((st.lists 4).map (QueryHistory.read (st.lists 0) (st.lists 1))).sum) % 2 ∧
    (parity.run st).1.lists 0 = st.lists 0 ∧
    (parity.run st).1.lists 1 = st.lists 1 ∧
    (parity.run st).1.lists 4 = st.lists 4 := by
  let s := (setup.run st).1
  have hc : Context (st.lists 0) (st.lists 1) (st.lists 4) s := by
    simp [Context, s, setup, Stmt.run, Expr.eval, Function.update]
  have hw : s.lists 5 = st.lists 4 := rfl
  have ha : s.regs 8 = 0 := rfl
  have hn : s.regs 9 = (st.lists 4).length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have h := iterate_result _ _ _ _ (Nat.size (st.lists 4).length + 1) s hc hw
    (by rw [ha]; decide)
  rw [ha, Nat.zero_add] at h
  change (iterate body.run (Nat.size (s.regs 9) + 1) (s.regs 9) s).1.regs 8 = _ ∧
    (iterate body.run (Nat.size (s.regs 9) + 1) (s.regs 9) s).1.lists 0 = _ ∧
    (iterate body.run (Nat.size (s.regs 9) + 1) (s.regs 9) s).1.lists 1 = _ ∧
    (iterate body.run (Nat.size (s.regs 9) + 1) (s.regs 9) s).1.lists 4 = _
  rw [hn]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem finish_run (st : State 12 6) :
    (finish.run st).1.regs 11 = (decide (st.regs 8 = 0)).toNat := by
  simp [finish, Stmt.run, Expr.eval, Function.update]
  split_ifs with h <;> simp [h]

theorem program_run (st : State 12 6) :
    (program.run st).1.regs 11 = (decide
      ((((st.lists 4).map (QueryHistory.read (st.lists 0) (st.lists 1))).sum) % 2 = 0)).toNat := by
  rw [program, run_seq_fst, finish_run, (parity_run st).1]

end PCP.Lang.HistoryParity
