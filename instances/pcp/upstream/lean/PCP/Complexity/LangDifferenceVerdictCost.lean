import PCP.Complexity.LangDifferenceVerdict

/-!
# Charged polynomial cost of the three-read difference verdict
-/

namespace PCP.Lang.DifferenceVerdict

/-- Every actual history answer remains a bit, including the default zero. -/
theorem read_le_one (qs : List ℕ) (bs : List Bool) (x : ℕ) :
    QueryHistory.read qs (bs.map Bool.toNat) x ≤ 1 := by
  rw [QueryHistory.read_bool]
  cases QueryTree.answersOracle qs bs x <;> decide

theorem readAt_cost (src : Fin 14) (st : State 14 4) (W : ℕ)
    (ha : Nat.size (st.regs src) ≤ W) (hq : listSize (st.lists 0) ≤ W)
    (hb : listSize (st.lists 1) ≤ W) :
    ((readAt src).run st).2 ≤ (QueryHistory.passConstant + 30) * (3 * W + 2) ^ 2 := by
  let s := setReg st 0 (st.regs src)
  have hc := QueryHistory.program_cost (s.restrict (Fin.castAdd 6) id)
  rw [← history_result s] at hc
  simp only [State.restrict_regs, State.restrict_lists,
    show (0 : Fin 8).castAdd 6 = (0 : Fin 14) from rfl, id_eq] at hc
  have hs0 : s.regs 0 = st.regs src := rfl
  rw [hs0] at hc
  change (history.run s).2 ≤ (QueryHistory.passConstant + 20) *
    (listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs src) + 2) ^ 2 at hc
  have hbound := hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (show listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs src) + 2 ≤
      3 * W + 2 by omega) 2))
  simp only [readAt, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var src).cost st.regs + (history.run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  nlinarith

theorem accumulate_cost (src : Fin 14) (qs : List ℕ) (bs : List Bool)
    (st : State 14 4) (W : ℕ) (hq : st.lists 0 = qs) (hb : st.lists 1 = bs.map Bool.toNat)
    (ha : Nat.size (st.regs src) ≤ W) (hqs : listSize qs ≤ W)
    (hbs : listSize (bs.map Bool.toNat) ≤ W) (hacc : st.regs 11 ≤ 3) :
    ((accumulate src).run st).2 ≤ (QueryHistory.passConstant + 40) * (3 * W + 2) ^ 2 := by
  have hc := readAt_cost src st W ha (hq ▸ hqs) (hb ▸ hbs)
  have hout := (readAt_run src st).1
  rw [hq, hb] at hout
  have hv := readAt_reg src 11 (by decide) st
  have hread := read_le_one qs bs (st.regs src)
  have hsa : Nat.size (st.regs 11) ≤ 2 := (Nat.size_le_size hacc).trans (by decide)
  have hsr : Nat.size (QueryHistory.read qs (bs.map Bool.toNat) (st.regs src)) ≤ 1 :=
    (Nat.size_le_size hread).trans (by decide)
  have hsum := size_add_le (st.regs 11)
    (QueryHistory.read qs (bs.map Bool.toNat) (st.regs src))
  simp only [accumulate, run_seq_snd]
  change ((readAt src).run st).2 +
    (Expr.add 11 2).cost ((readAt src).run st).1.regs + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hv, hout]
  nlinarith

theorem finish_cost (st : State 14 4) (h : st.regs 11 ≤ 3) : (finish.run st).2 ≤ 30 := by
  have hs : Nat.size (st.regs 11) ≤ 2 := (Nat.size_le_size h).trans (by decide)
  have hm : Nat.size (st.regs 11 % 2) ≤ 1 :=
    (Nat.size_le_size (show st.regs 11 % 2 ≤ 1 by omega)).trans (by decide)
  have h2 : Nat.size 2 = 2 := by decide
  simp only [finish, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, h2, Nat.size_zero, Nat.zero_add,
    Nat.add_zero]
  split_ifs <;> simp only [Nat.size_one, Nat.size_zero] <;> omega

/-- The actual three-read branch is quadratic in its stored input and address bit bound. -/
theorem program_cost (qs : List ℕ) (bs : List Bool) (x y z W : ℕ) (st : State 14 4)
    (hc : Context qs (bs.map Bool.toNat) x y z st)
    (hqs : listSize qs ≤ W) (hbs : listSize (bs.map Bool.toNat) ≤ W)
    (hx : Nat.size x ≤ W) (hy : Nat.size y ≤ W) (hz : Nat.size z ≤ W) :
    (program.run st).2 ≤ (3 * QueryHistory.passConstant + 160) * (3 * W + 2) ^ 2 := by
  let s := setReg st 11 0
  have hsc : Context qs (bs.map Bool.toNat) x y z s := by
    simpa [Context, s, Function.update] using hc
  have hs11 : s.regs 11 = 0 := rfl
  have hc1 := accumulate_cost 8 qs bs s W hsc.1 hsc.2.1 (hsc.2.2.1 ▸ hx) hqs hbs
    (by rw [hs11]; omega)
  have hu11 := accumulate_run 8 s
  have huc := accumulate_context 8 qs (bs.map Bool.toNat) x y z s hsc
  rw [hs11, hsc.1, hsc.2.1, hsc.2.2.1, Nat.zero_add] at hu11
  generalize hu : ((accumulate 8).run s).1 = u at *
  have hu3 : u.regs 11 ≤ 3 := by rw [hu11]; exact (read_le_one qs bs x).trans (by decide)
  have hc2 := accumulate_cost 9 qs bs u W huc.1 huc.2.1 (huc.2.2.2.1 ▸ hy) hqs hbs hu3
  have hv11 := accumulate_run 9 u
  have hvc := accumulate_context 9 qs (bs.map Bool.toNat) x y z u huc
  rw [hu11, huc.1, huc.2.1, huc.2.2.2.1] at hv11
  generalize hv : ((accumulate 9).run u).1 = v at *
  have hv3 : v.regs 11 ≤ 3 := by
    rw [hv11]
    have := read_le_one qs bs x
    have := read_le_one qs bs y
    omega
  have hc3 := accumulate_cost 10 qs bs v W hvc.1 hvc.2.1 (hvc.2.2.2.2 ▸ hz) hqs hbs hv3
  have hw11 := accumulate_run 10 v
  rw [hv11, hvc.1, hvc.2.1, hvc.2.2.2.2] at hw11
  have hc4 := finish_cost ((accumulate 10).run v).1 (by
    rw [hw11]
    have := read_le_one qs bs x
    have := read_le_one qs bs y
    have := read_le_one qs bs z
    omega)
  have hzero : ((Stmt.assign 11 (.const 0) : Stmt 14 4).run st).2 = 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval, hzero]
  dsimp only [s] at hu hc1
  rw [hu, hv]
  nlinarith

end PCP.Lang.DifferenceVerdict
