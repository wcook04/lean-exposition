/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialSelectorLang

/-!
# Charged cost of the complete irreducible-mask search
-/

namespace PCP.Lang.BinaryPolynomialSelector

open BinaryPolynomialDegreeScan BooleanLoops

theorem test36_cost (t code : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = code) (h28 : st.regs 28 = 2 ^ t)
    (hcode : code < 2 ^ t) :
    (test36.run st).2 ≤ 1000000 * (2 ^ t + 1) ^ 6 := by
  rw [test36, Stmt.run_rename_cost testCandidate testEmbedding id
    (show Function.Injective testEmbedding from Fin.castLE_injective _)
    Function.injective_id]
  exact testCandidate_cost t code _ h20 h21 h28 hcode

theorem candidateCheck_cost (t : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) (hi : st.regs 32 < 2 ^ t) :
    (candidateCheck.run st).2 ≤ 1010000 * (2 ^ t + 1) ^ 6 := by
  let s := setReg st 21 (st.regs 32)
  have hc := test36_cost t (st.regs 32) s
    (by simpa [s, Function.update] using h20) (by simp [s])
    (by simpa [s, Function.update] using h28) hi
  have hs : Nat.size (st.regs 32) ≤ 2 ^ t := (size_le_self _).trans hi.le
  simp only [candidateCheck, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 32).cost st.regs + (test36.run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  nlinarith [Nat.zero_le ((2 ^ t) ^ 6), Nat.zero_le ((2 ^ t) ^ 5),
    Nat.zero_le ((2 ^ t) ^ 4), Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

theorem candidateTail_cost (st : State 36 2) (q : ℕ)
    (hi : st.regs 32 ≤ q) (hr : st.regs 33 ≤ q)
    (h27 : st.regs 27 < 2) (h35 : st.regs 35 = 1) :
    (candidateTail.run st).2 ≤ 1000000 * (q + 2) := by
  have hc := loopFree_cost_le candidateTail (by decide) st (q + 1)
    (by
      intro r hh
      have hu : candidateTail.uses = [32, 33, 27, 32, 32, 35] := rfl
      rw [hu] at hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (size_le_self _).trans (hi.trans (by omega))
      · exact (size_le_self _).trans (hr.trans (by omega))
      · exact (size_le_self _).trans (by omega)
      · exact (size_le_self _).trans (hi.trans (by omega))
      · exact (size_le_self _).trans (hi.trans (by omega))
      · rw [h35]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega))
    (by simp [candidateTail, Stmt.lUses])
  have hC : candidateTail.C * (candidateTail.width + candidateTail.csize + 1) ≤ 1000000 := by
    decide
  exact hc.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (q + 1 + 1) hC)

theorem candidateBody_cost (t : ℕ) (st : State 36 2)
    (hc : SearchContext t st) (hi : st.regs 32 < 2 ^ t) (hr : st.regs 33 ≤ 2 ^ t) :
    (candidateBody.run st).2 ≤ 4000000 * (2 ^ t + 1) ^ 6 := by
  have hcheck := candidateCheck_cost t st hc.1 hc.2.1 hi
  have hs27 := candidateCheck_run st t hc.1 hc.2.1
  have hs32 := run_regs_frame candidateCheck 32 (by decide) st
  have hs33 := run_regs_frame candidateCheck 33 (by decide) st
  have hs35 := run_regs_frame candidateCheck 35 (by decide) st
  simp only [candidateBody, run_seq_snd]
  generalize hs : (candidateCheck.run st).1 = s at *
  have htail := candidateTail_cost s (2 ^ t) (by simpa only [hs32] using hi.le)
    (by simpa only [hs33] using hr) (by rw [hs27]; exact truth_lt_two _)
    (hs35.trans hc.2.2)
  nlinarith [Nat.zero_le ((2 ^ t) ^ 6), Nat.zero_le ((2 ^ t) ^ 5),
    Nat.zero_le ((2 ^ t) ^ 4), Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

/-- The full least-mask search has seventh-degree cost in the field cardinality. -/
theorem selectMask_cost (t : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) :
    (selectMask.run st).2 ≤ 5000000 * (2 ^ t + 1) ^ 7 := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg st 32 0) 33 q) 35 1
  have hit := iterate_cost_idx candidateBody.run (Nat.size q + 1)
    (4000000 * (q + 1) ^ 6) q
    (fun n u => SearchContext t u ∧ u.regs 32 = n ∧
      LeastInv (NumericPasses t) q n (u.regs 33))
    (by
      intro n u hn hu
      exact ⟨candidateBody_inv t n u hn hu.1 hu.2.1 hu.2.2,
        candidateBody_cost t u hu.1 (hu.2.1 ▸ hn) hu.2.2.1⟩) s
    (by simp [s, SearchContext, Function.update, h20, h28, q, leastInv_zero])
  have hsize : Nat.size q ≤ q := size_le_self _
  have hb : q * (Nat.size q + 1 + 4000000 * (q + 1) ^ 6) ≤
      q * (q + 1 + 4000000 * (q + 1) ^ 6) := Nat.mul_le_mul_left _ (by omega)
  have hb' := hit.trans hb
  simp only [selectMask, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, h28]
  change (Expr.const 0).cost st.regs + ((Expr.var 28).cost (setReg st 32 0).regs +
    ((Expr.const 1).cost _ + ((iterate candidateBody.run (Nat.size q + 1) q s).2 +
      Nat.size q + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, Nat.size_zero, show Nat.size 1 = 1 from rfl, h28]
  change _ ≤ 5000000 * (q + 1) ^ 7
  nlinarith [Nat.zero_le (q ^ 7), Nat.zero_le (q ^ 6), Nat.zero_le (q ^ 5),
    Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3), Nat.zero_le (q ^ 2)]

end PCP.Lang.BinaryPolynomialSelector
