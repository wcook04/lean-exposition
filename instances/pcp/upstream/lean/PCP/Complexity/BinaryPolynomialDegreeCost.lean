/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialDegreeScan
import PCP.Complexity.BinaryPolynomialMaskCost

/-!
# Polynomial charged cost of the complete irreducibility test
-/

namespace PCP.Lang.BinaryPolynomialDegreeScan

open BinaryPolynomialMaskScan BooleanLoops

theorem degreePrepare_cost (st : State 32 2) (q : ℕ)
    (hd : st.regs 24 ≤ q) (ht : st.regs 20 ≤ q) :
    (degreePrepare.run st).2 ≤ 1000 * (q + 1) := by
  have hc := loopFree_cost_le degreePrepare (by decide) st q
    (by
      intro r hr
      have hu : degreePrepare.uses = [24, 20, 24] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (size_le_self _).trans hd
      · exact (size_le_self _).trans ht
      · exact (size_le_self _).trans hd)
    (by simp [degreePrepare, Stmt.lUses])
  have hC : degreePrepare.C * (degreePrepare.width + degreePrepare.csize + 1) ≤ 1000 := by decide
  exact hc.trans (Nat.mul_le_mul_right _ hC)

theorem degreeCheck_cost (t code d : ℕ) (st : State 32 2) (hd : d ≤ t)
    (hcode : code < 2 ^ t) (hc : DegreeContext t code st)
    (hi : st.regs 24 = d) (hw : st.regs 29 = 2 ^ d) (hf : st.regs 27 < 2) :
    (degreeCheck.run st).2 ≤ 280000 * (2 ^ t + 1) ^ 5 := by
  have htq : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have hp := degreePrepare_cost st (2 ^ t) (by rw [hi]; exact hd.trans htq)
    (by rw [hc.1]; exact htq)
  let s := setReg (setReg st 8 d) 9 (t - d)
  have hs : (degreePrepare.run st).1 = s := by
    simp [degreePrepare, s, run_seq_fst, run_assign_fst, Expr.eval,
      Function.update, hi, hc.1]
  have hscan := maskScan_cost t code d s hd hcode
    (by simp [Context, s, Function.update, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hw])
    (by simpa [s, Function.update] using hf)
  simp only [degreeCheck, run_seq_snd, hs]
  nlinarith [Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
    Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

theorem degreeGuard_cost (st : State 32 2) (q : ℕ)
    (hd : st.regs 24 ≤ q) (ht : st.regs 20 ≤ q) :
    (degreeGuard.run st).2 ≤ 100000 * (q + 1) := by
  have hc := loopFree_cost_le degreeGuard (by decide) st q
    (by
      intro r hr
      have hu : degreeGuard.uses = [24, 24, 20] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (size_le_self _).trans hd
      · exact (size_le_self _).trans hd
      · exact (size_le_self _).trans ht)
    (by simp [degreeGuard, Stmt.lUses])
  have hC : degreeGuard.C * (degreeGuard.width + degreeGuard.csize + 1) ≤ 100000 := by decide
  exact hc.trans (Nat.mul_le_mul_right _ hC)

theorem degreeGuard_flag (st : State 32 2) : (degreeGuard.run st).1.regs 3 < 2 := by
  simp only [degreeGuard, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false]
  split_ifs <;> decide

theorem degreeConditional_cost (t code d : ℕ) (st : State 32 2) (hd : d ≤ t)
    (hcode : code < 2 ^ t) (hc : DegreeContext t code st)
    (hi : st.regs 24 = d) (hw : st.regs 29 = 2 ^ d) (hf : st.regs 27 < 2) :
    (degreeConditional.run st).2 ≤ 400000 * (2 ^ t + 1) ^ 5 := by
  have htq : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have hg := degreeGuard_cost st (2 ^ t) (by rw [hi]; exact hd.trans htq)
    (by rw [hc.1]; exact htq)
  have hs20 := run_regs_frame degreeGuard 20 (by decide) st
  have hs21 := run_regs_frame degreeGuard 21 (by decide) st
  have hs24 := run_regs_frame degreeGuard 24 (by decide) st
  have hs27 := run_regs_frame degreeGuard 27 (by decide) st
  have hs28 := run_regs_frame degreeGuard 28 (by decide) st
  have hs29 := run_regs_frame degreeGuard 29 (by decide) st
  have hs30 := run_regs_frame degreeGuard 30 (by decide) st
  have hs3 := degreeGuard_flag st
  simp only [degreeConditional, run_seq_snd, run_ite_snd]
  generalize hs : (degreeGuard.run st).1 = s at *
  have hcheck := degreeCheck_cost t code d s hd hcode
    ⟨hs20.trans hc.1, hs21.trans hc.2.1, hs28.trans hc.2.2.1, hs30.trans hc.2.2.2⟩
    (hs24.trans hi) (hs29.trans hw) (by simpa only [hs27] using hf)
  have hsize : Nat.size (s.regs 3) ≤ 1 := size_le_one_of_le_one (by omega)
  split_ifs
  · nlinarith [Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
      Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]
  · simp only [Stmt.run]
    nlinarith [Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
      Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

theorem degreeAdvance_cost (st : State 32 2) (q : ℕ)
    (hd : st.regs 24 ≤ q) (hw : st.regs 29 ≤ q) (h30 : st.regs 30 = 1) :
    (degreeAdvance.run st).2 ≤ 10000 * (q + 2) := by
  have hc := loopFree_cost_le degreeAdvance (by decide) st (q + 1)
    (by
      intro r hr
      have hu : degreeAdvance.uses = [24, 30, 29] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (size_le_self _).trans (hd.trans (by omega))
      · rw [h30]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega)
      · exact (size_le_self _).trans (hw.trans (by omega)))
    (by simp [degreeAdvance, Stmt.lUses])
  have hC : degreeAdvance.C * (degreeAdvance.width + degreeAdvance.csize + 1) ≤ 10000 := by
    decide
  exact hc.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (q + 1 + 1) hC)

theorem degreeBody_cost (t code d : ℕ) (st : State 32 2) (hd : d ≤ t)
    (hcode : code < 2 ^ t) (hc : DegreeContext t code st)
    (hi : st.regs 24 = d) (hw : st.regs 29 = 2 ^ d) (hf : st.regs 27 < 2) :
    (degreeBody.run st).2 ≤ 500000 * (2 ^ t + 1) ^ 5 := by
  have hcond := degreeConditional_cost t code d st hd hcode hc hi hw hf
  have hs24 := run_regs_frame degreeConditional 24 (by decide) st
  have hs29 := run_regs_frame degreeConditional 29 (by decide) st
  have hs30 := run_regs_frame degreeConditional 30 (by decide) st
  simp only [degreeBody, run_seq_snd]
  generalize hs : (degreeConditional.run st).1 = s at *
  have ha := degreeAdvance_cost s (2 ^ t)
    (by rw [hs24, hi]; exact hd.trans (Nat.lt_two_pow_self (n := t)).le)
    (by rw [hs29, hw]; exact Nat.pow_le_pow_right (by decide) hd) (hs30.trans hc.2.2.2)
  nlinarith [Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
    Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

/-- The full test is polynomial in the number of candidate coefficient masks. -/
theorem testCandidate_cost (t code : ℕ) (st : State 32 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = code) (h28 : st.regs 28 = 2 ^ t)
    (hcode : code < 2 ^ t) :
    (testCandidate.run st).2 ≤ 1000000 * (2 ^ t + 1) ^ 6 := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg (setReg (setReg st 24 0) 29 1) 30 1)
    27 (truth (0 < t))) 31 (t + 1)
  have hit := iterate_cost_idx degreeBody.run (Nat.size (t + 1) + 1)
    (500000 * (q + 1) ^ 5) (t + 1)
    (fun n u => DegreeContext t code u ∧ u.regs 24 = n ∧ u.regs 29 = 2 ^ n ∧
      u.regs 27 < 2)
    (by
      intro n u hn hu
      obtain ⟨hc, hd, hw, hf⟩ := degreeBody_step t code n u hu.1 hu.2.1 hu.2.2.1
      refine ⟨⟨hc, hd, hw, ?_⟩,
        degreeBody_cost t code n u (by omega) hcode hu.1 hu.2.1 hu.2.2.1 hu.2.2.2⟩
      rw [hf]
      have ht := truth_lt_two (DegreeGood t code n)
      have hm := Nat.mul_le_mul (show u.regs 27 ≤ 1 by omega)
        (show truth (DegreeGood t code n) ≤ 1 by omega)
      omega) s
    (by
      simp [s, DegreeContext, Function.update, h20, h21, h28]
      have := truth_lt_two (0 < t)
      omega)
  have htq : t ≤ q := (Nat.lt_two_pow_self (n := t)).le
  have hsT : Nat.size t ≤ q := (size_le_self _).trans htq
  have hsT1 : Nat.size (t + 1) ≤ q + 1 := (size_le_self _).trans (by omega)
  have hsTruth : Nat.size (truth (0 < t)) ≤ 1 :=
    size_le_one_of_le_one (by have := truth_lt_two (0 < t); omega)
  have hb : (t + 1) * (Nat.size (t + 1) + 1 + 500000 * (q + 1) ^ 5) ≤
      (q + 1) * (q + 2 + 500000 * (q + 1) ^ 5) := Nat.mul_le_mul (by omega) (by omega)
  have hb' := hit.trans hb
  simp only [testCandidate, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, h20]
  change (Expr.const 0).cost st.regs + ((Expr.const 1).cost _ +
    ((Expr.const 1).cost _ +
      ((Expr.lt 24 20).cost (setReg (setReg (setReg st 24 0) 29 1) 30 1).regs +
      ((Expr.add 20 30).cost (setReg (setReg (setReg (setReg st 24 0) 29 1) 30 1)
        27 (truth (0 < t))).regs +
        ((iterate degreeBody.run (Nat.size (t + 1) + 1) (t + 1) s).2 +
          Nat.size (t + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, dite_true, Nat.size_zero, show Nat.size 1 = 1 from rfl, h20]
  change _ ≤ 1000000 * (q + 1) ^ 6
  change Nat.size (if 0 < t then 1 else 0) ≤ 1 at hsTruth
  nlinarith [Nat.zero_le (q ^ 6), Nat.zero_le (q ^ 5), Nat.zero_le (q ^ 4),
    Nat.zero_le (q ^ 3), Nat.zero_le (q ^ 2)]

end PCP.Lang.BinaryPolynomialDegreeScan
