/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowQueries
import PCP.Complexity.HadamardRowLoopCost

/-!
# Complete numeric Hadamard query cost

This certificate includes all coefficient arithmetic, code serialization, source
copying, bounded iteration, and final reversal into the exact semantic order.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def queryConstant : ℕ := 7 * baseStepConstant + 1000100

theorem queries_cost (hr : 1 ≤ r) (s : TestRandomness t r) (st : State 80 32)
    (hc : Context s st) :
    (queries.run st).2 ≤ queryConstant * factorSize t r ^ 9 := by
  let u := setList st 24 []
  have hu : Context s u := by simpa [Context, u, Function.update] using hc
  have hp := (prefix_spec hr s).output u hu
  have hpc := (prefix_spec hr s).context u hu
  have hcost := (prefix_spec hr s).cost u hu
  dsimp only [u] at hp hpc hcost
  simp only [queries, run_seq_snd, run_copy_snd, run_copy_fst, hc.2.2.1]
  generalize hv : (initialQueries.run (setList st 24 [])).1 = v at *
  have hf := factorLoop_run s v hpc
  have hfcost := factorLoop_cost s v hpc
  generalize hw : (factorLoop.run v).1 = w at *
  have htrace : (w.lists 24).reverse = (ComputableHadamardTest.queries hr s).map code := by
    simp only [hf.2, hp, setList_lists, Function.update_self, List.append_nil,
      List.reverse_append, List.reverse_reverse, queries_decomposition]
  have hsize : listSize (w.lists 24) ≤ (2 * r + 4) * (2 ^ t + 1) := by
    rw [← listSize_reverse, htrace]
    exact queryCodes_size hr s
  simp only [run_rev_snd, listSize, List.map_nil, List.sum_nil]
  change 0 + 1 + ((initialQueries.run (setList st 24 [])).2 +
    ((factorLoop.run v).2 + (listSize (w.lists 24) + 1) + 1) + 1) + 1 ≤ _
  have hb : baseSize t r ≤ factorSize t r := by
    have hh : Nat.size r ≤ 3 * r := (size_le_self _).trans (by omega)
    exact Nat.add_le_add_right (Nat.add_le_add_left hh _) 5
  have hpow : baseSize t r ^ 8 ≤ factorSize t r ^ 9 :=
    (Nat.pow_le_pow_left hb 8).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hcost' := hcost.trans (Nat.mul_le_mul_left _ hpow)
  have hm1 : 2 * r + 4 ≤ factorSize t r :=
    (by omega : 2 * r + 4 ≤ 3 * r + 5).trans
      (Nat.add_le_add_right (Nat.le_add_left _ _) 5)
  have hm2 : 2 ^ t + 1 ≤ factorSize t r :=
    Nat.add_le_add_left (by omega : 1 ≤ 3 * r + 5) _ |>.trans_eq (by unfold factorSize; omega)
  have hpow2 : factorSize t r ^ 2 ≤ factorSize t r ^ 9 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  have hsize' : listSize (w.lists 24) ≤ factorSize t r ^ 9 :=
    hsize.trans ((Nat.mul_le_mul hm1 hm2).trans (by simpa only [pow_two] using hpow2))
  have hpos : 1 ≤ factorSize t r ^ 9 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  unfold queryConstant factorBodyConstant at *
  nlinarith only [hcost', hfcost, hsize', hpos]

end PCP.Lang.HadamardRow
