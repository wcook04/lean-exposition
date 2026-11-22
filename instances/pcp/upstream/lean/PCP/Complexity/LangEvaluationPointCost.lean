import PCP.Complexity.LangEvaluationPoint

/-!
# Polynomial charged cost of the stored four-block sampler
-/

namespace PCP.Lang.EvaluationPoint

open PCP.Algebraic

private theorem size_power (m i : ℕ) : Nat.size (m ^ i) ≤ i * Nat.size m + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
      have h := size_mul_le (m ^ i) m
      rw [← pow_succ] at h
      nlinarith

theorem multiply_loop_cost (m k n : ℕ) (st : State 47 13) (hm : 0 < m) (hn : n ≤ 3)
    (h36 : st.regs 36 = n) (h40 : st.regs 40 = k % m) (h46 : st.regs 46 = m) :
    ((Stmt.loop 36 multiply).run st).2 ≤ 1000 * (m + 1) ^ 2 := by
  let J (j : ℕ) (s : State 47 13) := s.regs 46 = m ∧ s.regs 40 = (k % m) * m ^ j
  have hstep (j : ℕ) (s : State 47 13) (_hj : j < st.regs 36) (hs : J j s) :
      J (j + 1) (multiply.run s).1 := by
    simp [J, multiply, run_assign_fst, Expr.eval, Function.update, hs.1, hs.2,
      pow_succ, Nat.mul_assoc]
  have hread (j : ℕ) (s : State 47 13) (hj : j < st.regs 36) (hs : J j s) :
      ∀ r ∈ multiply.uses, Nat.size (s.regs r) ≤ 4 * m + 4 := by
    have hi : j < 3 := by omega
    have hb := size_mul_le (k % m) (m ^ j)
    have hp := size_power m j
    have hm' := size_le_self m
    have hk := Nat.size_le_size (Nat.mod_lt k hm).le
    intro r hr
    simp only [multiply, Stmt.uses, Expr.uses, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hs.2]
      nlinarith
    · rw [hs.1]
      omega
  have hc := loop_cost_le 36 multiply (by rfl) st (4 * m + 4) J
    (by omega) hstep hread (by intro j s hj hs L hL; simp [multiply, Stmt.lUses] at hL)
    (by simp [J, h46, h40])
  have hC : multiply.C * (multiply.width + multiply.csize + 1) + 3 ≤ 30 := by decide
  have hc' := hc.trans (Nat.mul_le_mul_right _ hC)
  nlinarith

theorem budget_cost (m : ℕ) (st : State 47 13) (hm : st.regs 46 = m) :
    (budget.run st).2 ≤ 100 * (m + 1) := by
  have hm' := size_le_self m
  have hmul := size_mul_le 4 m
  have hadd := size_add_le (4 * m) 1
  have h4 : Nat.size 4 = 3 := by decide
  simp only [h4, Nat.size_one] at hmul hadd
  simp only [budget, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, dite_true, h4, Nat.size_one, hm]
  nlinarith

theorem prepare_cost (m : ℕ) (st : State 47 13) (hm : 0 < m)
    (h46 : st.regs 46 = m) (hk : st.regs 0 < 4 * m) :
    (prepare.run st).2 ≤ 2000 * (m + 1) ^ 2 := by
  let s := setReg (setReg st 40 (st.regs 0 % m)) 36 (st.regs 0 / m)
  have hn : st.regs 0 / m ≤ 3 := by
    have := (Nat.div_lt_iff_lt_mul hm).2 (show st.regs 0 < 4 * m from hk)
    omega
  have hl := multiply_loop_cost m (st.regs 0) (st.regs 0 / m) s hm hn
    (by simp [s, Function.update]) (by simp [s, Function.update])
    (by simpa [s, Function.update] using h46)
  have hi := multiply_iterate (Nat.size (s.regs 36) + 1) (s.regs 36) s
  have hb := budget_cost m ((Stmt.loop 36 multiply).run s).1
    (by simpa [run_loop_fst, s, Function.update] using hi.2.trans (by simpa [s] using h46))
  have hs0 := size_le_self (st.regs 0)
  have hsm := size_le_self m
  have hmod := Nat.size_le_size (Nat.mod_lt (st.regs 0) hm).le
  have hdiv := Nat.size_le_size (Nat.div_le_self (st.regs 0) m)
  have hc0 : ((Stmt.assign 40 (.mod 0 46) : Stmt 47 13).run st).2 =
      Nat.size (st.regs 0) + Nat.size m + Nat.size (st.regs 0 % m) + 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h46]
  have hc1 : ((Stmt.assign 36 (.div 0 46) : Stmt 47 13).run
      (setReg st 40 (st.regs 0 % m))).2 =
      Nat.size (st.regs 0) + Nat.size m + Nat.size (st.regs 0 / m) + 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update, h46]
  simp only [prepare, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_of_ne (by decide : (0 : Fin 47) ≠ 40),
    Function.update_of_ne (by decide : (46 : Fin 47) ≠ 40), h46]
  rw [hc0, hc1]
  change _ + (_ + (((Stmt.loop 36 multiply).run s).2 +
    (budget.run ((Stmt.loop 36 multiply).run s).1).2 + 1) + 1) + 1 ≤ _
  nlinarith

variable {t : ℕ} [NeZero t]

theorem kernel_cost (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hm : 0 < m) (hk : st.regs 0 < 4 * m) (hs : View m a st) :
    (kernel.run st).2 ≤ 20000000000 * (t + m + 1) ^ 4 := by
  have hc1 := prepare_cost m st hm hs.2.2.1 hk
  have hp := prepare_run st
  have hv := prepare_view m a st hs
  rw [hs.2.2.1] at hp
  generalize hu : (prepare.run st).1 = u at *
  have hc2 := BinaryFieldCodePower.program_cost (u.restrict powerRegs powerLists) a
    (exponent m (st.regs 0)) (4 * m + 1) hv.1 hv.2.1 hp.1 hp.2
    (exponent_size m _ hm hk) hv.2.2.2.1 hv.2.2.2.2
  have ho := BinaryFieldCodePower.program_run (u.restrict powerRegs powerLists) a
    (exponent m (st.regs 0)) (4 * m + 1) hv.1 hv.2.1 hp.1 hp.2
    (exponent_size m _ hm hk) hv.2.2.2.1 hv.2.2.2.2
  rw [← power_result u] at hc2 ho
  simp only [State.restrict_regs, show powerRegs 26 = (30 : Fin 47) from rfl] at ho
  have hsize : Nat.size (BinaryFieldCode.fieldEquiv t
      (a ^ exponent m (st.regs 0))).val ≤ t :=
    Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t _).isLt
  have hc3 : ((Stmt.assign 1 (.var 30) : Stmt 47 13).run (power.run u).1).2 ≤ 2 * t + 1 := by
    simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ho]
    omega
  let N := t + m + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hmN : m + 1 ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have hlin : N ≤ N ^ 4 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 4)
  have hquad : (m + 1) ^ 2 ≤ N ^ 4 :=
    (Nat.pow_le_pow_left hmN 2).trans (Nat.pow_le_pow_right hN (by decide))
  have hbig : (t + (4 * m + 1) + 1) ^ 4 ≤ 625 * N ^ 4 := by
    have h := Nat.pow_le_pow_left (show t + (4 * m + 1) + 1 ≤ 5 * N by dsimp [N]; omega) 4
    nlinarith only [h]
  have hc1' := hc1.trans (Nat.mul_le_mul_left 2000 hquad)
  have hc2' := hc2.trans (Nat.mul_le_mul_left 30000000 hbig)
  simp only [kernel, run_seq_snd, hu]
  change _ ≤ 20000000000 * N ^ 4
  nlinarith

/-- The complete stored sampler has polynomial cost in field width and block size. -/
theorem program_cost (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hm : 0 < m) (hs : View m a st) (he : st.lists 1 = []) :
    (program.run st).2 ≤ 100000000000 * (t + m + 1) ^ 5 := by
  let s := setReg (setReg st 3 4) 3 (4 * m)
  have hv : View m a s := by simpa [View, s, Function.update] using hs
  have hc : FramedTabulation.KernelCost kernel (st.lists 0) (4 * m)
      (20000000000 * (t + m + 1) ^ 4) (View m a) := by
    intro u _hi _h2 _h3 hk hu
    exact kernel_cost m a u hm hk hu
  have ht := FramedTabulation.tabulate_cost (kernel_spec m a (st.lists 0) hm)
    (view_stable m a) hc
    (fun k _ => Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t (a ^ exponent m k)).isLt)
    s rfl (by simp [s, Function.update]) he hv
  have hmul := size_mul_le 4 m
  have hsm := size_le_self m
  have hsize := size_le_self (4 * m)
  have h4 : Nat.size 4 = 3 := by decide
  have hc0 : ((Stmt.assign 3 (.const 4) : Stmt 47 13).run st).2 = 7 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h4]
  have hc1 : ((Stmt.assign 3 (.mul 3 46) : Stmt 47 13).run (setReg st 3 4)).2 ≤
      2 * m + 7 := by
    simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
      Function.update, Fin.reduceEq, dite_false, dite_true, hs.2.2.1, h4]
    omega
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, hs.2.2.1]
  rw [hc0]
  change 7 + (((Stmt.assign 3 (.mul 3 46) : Stmt 47 13).run (setReg st 3 4)).2 +
    ((Tabulation.tabulate kernel).run s).2 + 1) + 1 ≤ _
  let N := t + m + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hmN : m ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have hlin : N ≤ N ^ 4 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 4)
  have hprod : m * N ^ 4 ≤ N ^ 5 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ hmN |>.trans_eq (Nat.mul_comm _ _)
  have hpoly : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by decide)
  have hm4 : m ≤ N ^ 4 := hmN.trans hlin
  have ht4 : t ≤ N ^ 4 := htN.trans hlin
  change _ ≤ 100000000000 * N ^ 5
  change _ ≤ 4 * m * (20000000000 * N ^ 4 + 2 * t + 3 * Nat.size (4 * m) + 7) +
    Nat.size (4 * m) + 9 at ht
  have hbracket : 20000000000 * N ^ 4 + 2 * t + 3 * Nat.size (4 * m) + 7 ≤
      20000000021 * N ^ 4 := by nlinarith
  have ht' := ht.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left (4 * m) hbracket) _) _)
  nlinarith

end PCP.Lang.EvaluationPoint
