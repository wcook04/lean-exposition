/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowVerdict

/-!
# Constant cost of the elementary received-bit checks

Only actual input bits are bounded. Initial work registers can contain arbitrary
values; every read of a work slot follows its initialization.
-/

namespace PCP.Lang.HadamardRow

set_option maxHeartbeats 1200000 in
-- This enumerates the 64 possible six-bit prefixes and checks their exact charges.
theorem prefixCheck_cost (st : State 100 32)
    (hb : st.regs 74 ≤ 1) (ha : st.regs 75 ≤ 1) (hz : st.regs 76 ≤ 1)
    (hu : st.regs 77 ≤ 1) (hp : st.regs 78 ≤ 1) (hl : st.regs 79 ≤ 1) :
    (prefixCheck.run st).2 ≤ 100 := by
  interval_cases hbv : st.regs 74 <;> interval_cases hav : st.regs 75 <;>
    interval_cases hzv : st.regs 76 <;> interval_cases huv : st.regs 77 <;>
    interval_cases hpv : st.regs 78 <;> interval_cases hlv : st.regs 79 <;>
    simp only [prefixCheck, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update,
      setReg_regs, Fin.reduceEq, dite_false, dite_true, hbv, hav, hzv, huv, hpv, hlv] <;> decide

set_option maxHeartbeats 600000 in
-- This enumerates the 32 possible bit inputs to one factor equation.
theorem factorCheck_cost (p f : ℕ) (rest : List ℕ) (st : State 100 32)
    (h : st.lists 25 = p :: f :: rest) (htwo : st.regs 62 = 2)
    (hb : st.regs 74 ≤ 1) (hd : st.regs 69 ≤ 1) (hv : st.regs 63 ≤ 1)
    (hp : p ≤ 1) (hf : f ≤ 1) :
    (factorCheck.run st).2 ≤ 100 := by
  interval_cases hbv : st.regs 74 <;> interval_cases hdv : st.regs 69 <;>
    interval_cases hvv : st.regs 63 <;> interval_cases p <;> interval_cases f <;>
    simp only [factorCheck, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update,
      setReg_regs, setReg_lists, setList_regs, setList_lists,
      Fin.reduceEq, dite_false, dite_true, h, htwo, hbv, hdv, hvv] <;> decide

theorem factorVerdict_le (b d p f : ℕ) : factorVerdict b d p f ≤ 1 := by
  unfold factorVerdict
  split <;> omega

theorem prefixVerdict_le (b a z u lp l : ℕ) : prefixVerdict b a z u lp l ≤ 1 := by
  unfold prefixVerdict
  split <;> omega

theorem factorCheck_iterate_cost (ps : List (ℕ × ℕ)) (c : ℕ) (st : State 100 32)
    (h : st.lists 25 = pairAnswers ps) (htwo : st.regs 62 = 2)
    (hb : st.regs 74 ≤ 1) (hd : st.regs 69 ≤ 1) (hv : st.regs 63 ≤ 1)
    (hp : ∀ x ∈ ps, x.1 ≤ 1 ∧ x.2 ≤ 1) :
    (iterate factorCheck.run c ps.length st).2 ≤ ps.length * (c + 100) := by
  induction ps generalizing st with
  | nil => simp [iterate]
  | cons pf ps ih =>
      have hin : st.lists 25 = pf.1 :: pf.2 :: pairAnswers ps := h
      have hs := factorCheck_run pf.1 pf.2 (pairAnswers ps) st hin htwo
      have hc := factorCheck_cost pf.1 pf.2 (pairAnswers ps) st hin htwo hb hd hv
        (hp pf (by simp)).1 (hp pf (by simp)).2
      have h62 := run_regs_frame factorCheck 62 (by decide) st
      have h74 := run_regs_frame factorCheck 74 (by decide) st
      have h69 := run_regs_frame factorCheck 69 (by decide) st
      have hnext : (factorCheck.run st).1.regs 63 ≤ 1 := by
        rw [hs.1]
        exact (Nat.mul_le_mul hv (factorVerdict_le _ _ _ _)).trans_eq (by decide)
      have hh := ih (factorCheck.run st).1 hs.2 (h62.trans htwo)
        (h74 ▸ hb) (h69 ▸ hd) hnext (fun x hx => hp x (by simp [hx]))
      simp only [List.length_cons, iterate, Nat.succ_mul]
      omega

end PCP.Lang.HadamardRow
