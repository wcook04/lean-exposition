import PCP.Complexity.LangHistoryParity

/-!
# Polynomial cost of exact history parity
-/

namespace PCP.Lang.HistoryParity

theorem read_size_le (qs bs : List ℕ) (a : ℕ) :
    Nat.size (QueryHistory.read qs bs a) ≤ listSize bs := by
  induction qs generalizing bs with
  | nil => simp [QueryHistory.read]
  | cons q qs ih =>
      cases bs with
      | nil => simp [QueryHistory.read]
      | cons b bs =>
          simp only [QueryHistory.read]
          split
          · exact size_le_listSize (by simp)
          · exact (ih bs).trans (by simp [listSize])

theorem history_cost (st : State 12 6) (W : ℕ)
    (hq : listSize (st.lists 0) ≤ W) (hb : listSize (st.lists 1) ≤ W)
    (ha : Nat.size (st.regs 0) ≤ W) :
    (history.run st).2 ≤ (QueryHistory.passConstant+20)*(3*W+2)^2 := by
  have h := QueryHistory.program_cost (st.restrict (Fin.castAdd 4) (Fin.castAdd 2))
  rw [← history_result st] at h
  change (history.run st).2 ≤ (QueryHistory.passConstant+20)*
    (listSize (st.lists 0)+listSize (st.lists 1)+Nat.size (st.regs 0)+2)^2 at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

private theorem assign_cost (r : Fin 12) (e : Expr 12) (st : State 12 6) :
    ((Stmt.assign r e).run st).2 = e.cost st.regs := rfl

theorem body_cost (qs bs xs : List ℕ) (a : ℕ) (as : List ℕ) (W : ℕ) (st : State 12 6)
    (hc : Context qs bs xs st) (hw : st.lists 5 = a :: as) (hacc : st.regs 8 < 2)
    (hq : listSize qs ≤ W) (hb : listSize bs ≤ W) (ha : Nat.size a ≤ W) :
    (body.run st).2 ≤ (QueryHistory.passConstant+40)*(3*W+2)^2 := by
  let s := setReg (setReg (setList st 5 as) 0 a) 7 1
  have hp : ((Stmt.pop 5 0 7 : Stmt 12 6).run st).1 = s := by
    simp [Stmt.run, hw, s]
  have hsqs : s.lists 0 = qs := by simpa [s, Function.update] using hc.1
  have hsbs : s.lists 1 = bs := by simpa [s, Function.update] using hc.2.1
  have hs0 : s.regs 0 = a := by simp [s, Function.update]
  have hs8 : s.regs 8 = st.regs 8 := by simp [s, Function.update]
  have hs10 : s.regs 10 = 2 := by simpa [s, Function.update] using hc.2.2.2
  have hh := history_cost s W (hsqs ▸ hq) (hsbs ▸ hb) (hs0 ▸ ha)
  have hr := (history_run s).1
  rw [hsqs, hsbs, hs0] at hr
  have h8 := history_reg s 8 (by decide)
  have h10 := history_reg s 10 (by decide)
  rw [hs8] at h8
  rw [hs10] at h10
  have hread : Nat.size (QueryHistory.read qs bs a) ≤ W := (read_size_le qs bs a).trans hb
  have hsa : Nat.size (st.regs 8) ≤ 1 :=
    (Nat.size_le_size (show st.regs 8 ≤ 1 by omega)).trans (by decide)
  have hsum := size_add_le (st.regs 8) (QueryHistory.read qs bs a)
  have hm : Nat.size ((st.regs 8+QueryHistory.read qs bs a)%2) ≤ 1 :=
    (Nat.size_le_size (show (st.regs 8+QueryHistory.read qs bs a)%2 ≤ 1 by omega)).trans
      (by decide)
  have hpop : ((Stmt.pop 5 0 7 : Stmt 12 6).run st).2 = Nat.size a+1 := by
    simp [Stmt.run, hw]
  simp only [body, run_seq_snd, hp, hpop, run_assign_fst, assign_cost,
    Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_true, dite_false, h8, h10, hr]
  have htwo : Nat.size 2 = 2 := rfl
  rw [htwo]
  nlinarith

private theorem listSize_drop_le (xs : List ℕ) (j : ℕ) :
    listSize (xs.drop j) ≤ listSize xs := by
  have h := listSize_append (xs.take j) (xs.drop j)
  rw [List.take_append_drop] at h
  omega

def Inv (qs bs xs : List ℕ) (j : ℕ) (st : State 12 6) : Prop :=
  Context qs bs xs st ∧ st.lists 5 = xs.drop j ∧ st.regs 8 < 2

theorem body_inv (qs bs xs : List ℕ) (j : ℕ) (st : State 12 6)
    (hj : j < xs.length) (hi : Inv qs bs xs j st) :
    Inv qs bs xs (j+1) (body.run st).1 := by
  have hw : st.lists 5 = xs[j] :: xs.drop (j+1) :=
    hi.2.1.trans (List.drop_eq_getElem_cons hj)
  have h := body_step qs bs xs xs[j] _ st hi.1 hw
  refine ⟨h.2.2, h.2.1, ?_⟩
  rw [h.1]
  omega

/-- Cubic cost in stored query and answer words, with no consistency assumption. -/
theorem parity_cost (st : State 12 6) :
    (parity.run st).2 ≤ (QueryHistory.passConstant+60)*
      (3*(listSize (st.lists 0)+listSize (st.lists 1)+listSize (st.lists 4)+1)+2)^3 := by
  let qs := st.lists 0
  let bs := st.lists 1
  let xs := st.lists 4
  let W := listSize qs+listSize bs+listSize xs+1
  let s := (setup.run st).1
  have hq : listSize qs ≤ W := by dsimp [W]; omega
  have hb : listSize bs ≤ W := by dsimp [W]; omega
  have hx : listSize xs ≤ W := by dsimp [W]; omega
  have hl : xs.length ≤ W := (length_le_listSize xs).trans hx
  have hs : Nat.size xs.length ≤ W := (size_le_self _).trans hl
  have hi : Inv qs bs xs 0 s := by
    simp [Inv, Context, qs, bs, xs, s, setup, Stmt.run, Expr.eval, Function.update]
  have hn : s.regs 9 = xs.length := by
    simp [s, xs, setup, Stmt.run, Expr.eval, Function.update]
  have hloop := iterate_cost_idx body.run (Nat.size xs.length+1)
    ((QueryHistory.passConstant+40)*(3*W+2)^2) xs.length (Inv qs bs xs)
    (fun j u hj hu => ⟨body_inv qs bs xs j u hj hu,
      body_cost qs bs xs xs[j] (xs.drop (j+1)) W u hu.1
        (hu.2.1.trans (List.drop_eq_getElem_cons hj)) hu.2.2 hq hb
        ((size_le_listSize (List.getElem_mem hj)).trans hx)⟩) s hi
  have hsetup : (setup.run st).2 ≤ 3*W+12 := by
    have htwo : Nat.size 2 = 2 := rfl
    simp only [setup, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, htwo,
      Nat.size_zero, Nat.zero_add, Nat.add_zero, setList_lists, Function.update,
      Fin.reduceEq, dite_false]
    dsimp only [xs] at hx hs
    omega
  have hsum : (parity.run st).2 ≤ 3*W+12+
      xs.length*(Nat.size xs.length+1+(QueryHistory.passConstant+40)*(3*W+2)^2)+
        Nat.size xs.length+2 := by
    change (setup.run st).2+((iterate body.run (Nat.size (s.regs 9)+1)
      (s.regs 9) s).2+Nat.size (s.regs 9)+1)+1 ≤ _
    rw [hn]
    omega
  have hm := Nat.mul_le_mul hl (show Nat.size xs.length+1+
    (QueryHistory.passConstant+40)*(3*W+2)^2 ≤
      W+1+(QueryHistory.passConstant+40)*(3*W+2)^2 by omega)
  apply hsum.trans
  change _ ≤ (QueryHistory.passConstant+60)*(3*W+2)^3
  nlinarith [Nat.zero_le (QueryHistory.passConstant*W^3),
    Nat.zero_le (QueryHistory.passConstant*W^2)]

theorem finish_cost (st : State 12 6) (h : st.regs 8 < 2) : (finish.run st).2 ≤ 5 := by
  have hs : Nat.size (st.regs 8) ≤ 1 :=
    (Nat.size_le_size (show st.regs 8 ≤ 1 by omega)).trans (by decide)
  simp only [finish, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, Nat.size_zero, Nat.zero_add,
    Nat.add_zero]
  split_ifs <;> simp only [Nat.size_zero, Nat.size_one] <;> omega

theorem program_cost (st : State 12 6) :
    (program.run st).2 ≤ (QueryHistory.passConstant+66)*
      (3*(listSize (st.lists 0)+listSize (st.lists 1)+listSize (st.lists 4)+1)+2)^3 := by
  have hp := parity_cost st
  have hf := finish_cost (parity.run st).1 (by rw [(parity_run st).1]; omega)
  have hpos : 1 ≤ (3*(listSize (st.lists 0)+listSize (st.lists 1)+
      listSize (st.lists 4)+1)+2)^3 := Nat.one_le_pow _ _ (by omega)
  rw [program, run_seq_snd]
  nlinarith

end PCP.Lang.HistoryParity
