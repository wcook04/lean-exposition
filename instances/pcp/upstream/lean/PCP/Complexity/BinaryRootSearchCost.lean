/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryRootSearchLang

/-!
# Charged cost of exhaustive primitive-root search
-/

namespace PCP.Lang.BinaryRootSearch

open PCP.Algebraic BinaryField BinaryFieldWordCode BinaryRootPredicate
open BinaryPolynomialSelector BooleanLoops

theorem rootSearchTail_cost (st : State 36 11) (q : ℕ)
    (hi : st.regs 32 ≤ q) (hr : st.regs 35 ≤ q)
    (h27 : st.regs 27 < 2) (h31 : st.regs 31 = 1) :
    (rootSearchTail.run st).2 ≤ 1000000 * (q + 2) := by
  rw [rootSearchTail, Stmt.run_rename_cost candidateTail tailRegs tailLists
    tailRegs_injective (show Function.Injective tailLists from Fin.castLE_injective _)]
  exact candidateTail_cost _ q hi hr h27 h31

theorem checkAddress_cost {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) (hi : st.regs 32 < 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((checkAddress full).run st).2 ≤ 110000000 * (2 ^ t + 4) ^ 5 := by
  let s := setReg st 33 (st.regs 32)
  have htq : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have htest : ((checkRoot full).run s).2 ≤ 100000000 * (2 ^ t + 4) ^ 5 := by
    cases full with
    | false =>
      have h := testRoot_cost s ⟨st.regs 32, hi⟩
        (by simpa [s, Function.update] using h20) (by simp [s])
        (by simpa [s] using hm) (by simpa [s] using he)
      exact h.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 4).trans
        (Nat.pow_le_pow_right (by omega) (by decide))))
    | true =>
      let a := (BinaryFieldCode.fieldEquiv t).symm ⟨st.regs 32, hi⟩
      have h := BinaryGeneratorPredicate.program_cost a s
        (by simpa [s, Function.update] using h20)
        (by simp [s, a]) (by simpa [s, Function.update] using h28)
        (by simpa [s] using hm) (by simpa [s] using he)
      exact h.trans (Nat.mul_le_mul_right _ (by decide))
  have hsize : Nat.size (st.regs 32) ≤ t := Nat.size_le.mpr hi
  simp only [checkAddress, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 32).cost st.regs + ((checkRoot full).run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  have hp : 2 ^ t + 4 ≤ (2 ^ t + 4)^5 := Nat.le_pow (by decide)
  nlinarith only [hsize, htq, hp, htest]

theorem searchBody_cost {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (hc : RootContext t st) (hi : st.regs 32 < 2 ^ t) (hr : st.regs 35 ≤ 2 ^ t) :
    ((searchBody full).run st).2 ≤ 200000000 * (2 ^ t + 4) ^ 5 := by
  have hcheck := checkAddress_cost full st hc.1 hc.2.1 hi hc.2.2.2.1 hc.2.2.2.2
  have hs27 := checkAddress_run full st hc.1 hc.2.1 hi hc.2.2.2.1 hc.2.2.2.2
  have hs31 := run_regs_frame (checkAddress full) 31 (by cases full <;> decide) st
  have hs32 := run_regs_frame (checkAddress full) 32 (by cases full <;> decide) st
  have hs35 := run_regs_frame (checkAddress full) 35 (by cases full <;> decide) st
  simp only [searchBody, run_seq_snd]
  generalize hs : ((checkAddress full).run st).1 = s at *
  have htail := rootSearchTail_cost s (2 ^ t) (by simpa only [hs32] using hi.le)
    (by simpa only [hs35] using hr) (by rw [hs27]; exact truth_lt_two _)
    (hs31.trans hc.2.2.1)
  have hp : 2 ^ t + 4 ≤ (2 ^ t + 4)^5 := Nat.le_pow (by decide)
  nlinarith only [hcheck, htail, hp]

/-- The explicit search, including all predicate evaluations and minimum updates. -/
theorem searchRoot_cost {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((searchRoot full).run st).2 ≤ 300000000 * (2 ^ t + 4) ^ 6 := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg st 32 0) 35 q) 31 1
  have hit := iterate_cost_idx (searchBody full).run (Nat.size q + 1)
    (200000000 * (q + 4) ^ 5) q
    (fun n u => RootContext t u ∧ u.regs 32 = n ∧
      LeastInv (CodeCandidate t full) q n (u.regs 35))
    (by
      intro n u hn hu
      exact ⟨searchBody_inv full n u hn hu.1 hu.2.1 hu.2.2,
        searchBody_cost full u hu.1 (hu.2.1 ▸ hn) hu.2.2.1⟩) s
    (by simp [s, RootContext, Function.update, h20, h28, q, hm, he, leastInv_zero])
  have hsize : Nat.size q ≤ q := size_le_self _
  have hb : q * (Nat.size q + 1 + 200000000 * (q + 4) ^ 5) ≤
      q * (q + 1 + 200000000 * (q + 4) ^ 5) := Nat.mul_le_mul_left _ (by omega)
  have hb' := hit.trans hb
  simp only [searchRoot, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, h28]
  change (Expr.const 0).cost st.regs + ((Expr.var 28).cost (setReg st 32 0).regs +
    ((Expr.const 1).cost _ + ((iterate (searchBody full).run (Nat.size q + 1) q s).2 +
      Nat.size q + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, Nat.size_zero, show Nat.size 1 = 1 from rfl, h28]
  change _ ≤ 300000000 * (q + 4) ^ 6
  nlinarith [Nat.zero_le (q ^ 6), Nat.zero_le (q ^ 5), Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3), Nat.zero_le (q ^ 2)]

end PCP.Lang.BinaryRootSearch
