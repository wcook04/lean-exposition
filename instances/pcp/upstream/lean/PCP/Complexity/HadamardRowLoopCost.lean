/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowLoop
import PCP.Complexity.HadamardRowFactorCost

/-!
# Polynomial charged cost of the complete factor loop

The stored seed codes contribute their bit lengths. Each of the `r-1` iterations
has an eighth-degree bound in the field size and row degree.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

private theorem assignCost (x : Fin 80) (e : Expr 80) (st : State 80 32) :
    ((Stmt.assign x e).run st).2 = e.cost st.regs := rfl

def factorBodyConstant : ℕ := 2 * baseStepConstant + 1000000

theorem factorBody_cost (s : TestRandomness t r) (k : Fin (r - 1)) (cs : List ℕ)
    (st : State 80 32) (hc : Context s st) (hk : st.regs 59 = k.val)
    (hone : st.regs 61 = 1) (hcs : st.lists 25 = code (s.factor k) :: cs) :
    (factorBody.run st).2 ≤ factorBodyConstant * factorSize t r ^ 8 := by
  let u := setReg st 60 (st.regs 59 + st.regs 61)
  have hu : Context s u := by simpa [Context, u, Function.update] using hc
  have hua : u.regs 60 = k.val + 1 := by simp [u, hk, hone]
  have hl := HadamardFactorLoad.load_run (s.factor k) cs u hu.1 hua hu.2.2.1 hcs
  have hlc := HadamardFactorLoad.load_cost (s.factor k) cs u hu.1 hua hu.2.2.1 hcs
  have hctx := HadamardFactorLoad.load_context s (s.factor k) cs u hu hua hcs
  have h60 := run_regs_frame HadamardFactorLoad.load 60 (by decide) u
  have h59 := run_regs_frame HadamardFactorLoad.load 59 (by decide) u
  have h61 := run_regs_frame HadamardFactorLoad.load 61 (by decide) u
  dsimp only [u] at hl hlc hctx h60 h59 h61
  simp only [factorBody, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hv : (HadamardFactorLoad.load.run
    (setReg st 60 (st.regs 59 + st.regs 61))).1 = v at *
  have hpc := pair_cost (TestRandomness.productDegree_le k) s (s.factor k) v hctx
    (h60.trans hua) hl.1
  have hp59 := run_regs_frame pair 59 (by decide) v
  have hp61 := run_regs_frame pair 61 (by decide) v
  generalize hw : (pair.run v).1 = w at *
  have hw59 : w.regs 59 = k.val := by simpa [Function.update] using hp59.trans (h59.trans hk)
  have hw61 : w.regs 61 = 1 := by simpa [Function.update] using hp61.trans (h61.trans hone)
  rw [hk, hone] at hlc
  simp only [assignCost, Expr.cost, Expr.readSize, Expr.eval, hw59, hw61, hk,
    hone, Nat.size_one]
  have hdegree : Nat.size (k.val + 1) ≤ r := (size_le_self _).trans (by omega)
  have hkSize : Nat.size k.val ≤ r := (size_le_self _).trans (by omega)
  have h4 : (2 ^ t + Nat.size (k.val + 1) + 3) ^ 4 ≤ factorSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by
      change 2 ^ t + Nat.size (k.val + 1) + 3 ≤ 2 ^ t + 3 * r + 5
      exact (by omega : ∀ q a r, a ≤ r → q + a + 3 ≤ q + 3 * r + 5) _ _ _ hdegree) 4).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hl' := hlc.trans (Nat.mul_le_mul_left _ h4)
  have hlow : r + 5 ≤ factorSize t r ^ 8 :=
    (by
      exact Nat.add_le_add_right ((by omega : r ≤ 3 * r).trans
        (Nat.le_add_left _ _)) 5 : r + 5 ≤ factorSize t r).trans (Nat.le_pow (by decide))
  unfold factorBodyConstant
  nlinarith only [hl', hpc, hdegree, hkSize, hlow]

theorem factorCodes_size (s : TestRandomness t r) :
    listSize (factorCodes s) ≤ (r - 1) * (2 ^ t + 1) := by
  have hb : ∀ x ∈ factorCodes s, Nat.size x + 1 ≤ 2 ^ t + 1 := by
    intro x hx
    simp only [factorCodes, List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact Nat.add_le_add_right (code_size (s.factor k)) 1
  have hsum := List.sum_le_length_nsmul (factorCodes s |>.map fun x => Nat.size x + 1)
    (2 ^ t + 1) (by simpa only [List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] using hb)
  simpa [listSize, factorCodes] using hsum

theorem factorInit_cost (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    (factorInit.run st).2 ≤ 10 * factorSize t r ^ 2 := by
  have hcodes := factorCodes_size s
  have hs : Nat.size r ≤ r := size_le_self _
  have hsub : Nat.size (r - 1) ≤ r := (size_le_self _).trans (Nat.sub_le _ _)
  simp only [factorInit, run_seq_snd, run_copy_snd, run_copy_fst,
    assignCost, run_assign_fst, Expr.cost, Expr.readSize, Expr.eval,
    setReg_regs, setList_regs, Function.update, Fin.reduceEq, dite_false, dite_true,
    Nat.size_one, Nat.size_zero, hc.2.1, hc.2.2.2.2.2.2]
  have hm : r + 2 ^ t + 5 ≤ factorSize t r := by unfold factorSize; omega
  have hcodes' : listSize (factorCodes s) ≤ r * (2 ^ t + 1) :=
    hcodes.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  nlinarith only [hcodes', hs, hsub, hm, Nat.zero_le (2 ^ t)]

theorem factorLoop_cost (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    (factorLoop.run st).2 ≤ (factorBodyConstant + 20) * factorSize t r ^ 9 := by
  have hinit := factorInit_cost s st hc
  have hi := factorInit_run s st hc
  simp only [factorLoop, run_seq_snd, run_loop_snd]
  generalize hu : (factorInit.run st).1 = u at *
  rw [hi.2]
  have hit := iterate_cost_idx factorBody.run (Nat.size (r - 1) + 1)
    (factorBodyConstant * factorSize t r ^ 8) (r - 1)
    (FactorInvariant s (st.lists 24)) (by
      intro j v hj hv
      refine ⟨factorBody_invariant s _ j v hj hv, ?_⟩
      have hcs := hv.2.2.2.1.trans (factorCodes_drop s j hj)
      exact factorBody_cost s ⟨j, hj⟩ ((factorCodes s).drop (j + 1)) v
        hv.1 hv.2.1 hv.2.2.1 hcs) u hi.1
  have hlow : r + 1 ≤ factorSize t r :=
    (by omega : r + 1 ≤ 3 * r + 5).trans (by
      exact Nat.add_le_add_right (Nat.le_add_left _ _) 5)
  have hr : r - 1 ≤ factorSize t r := (by omega : r - 1 ≤ r + 1).trans hlow
  have hs : Nat.size (r - 1) + 1 ≤ factorSize t r :=
    (Nat.add_le_add_right (size_le_self _) 1).trans ((by omega : r - 1 + 1 ≤ r + 1).trans hlow)
  have hp2 : factorSize t r ^ 2 ≤ factorSize t r ^ 9 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  have hp1 : factorSize t r ≤ factorSize t r ^ 9 := Nat.le_pow (by decide)
  have hmul := Nat.mul_le_mul hr
    (Nat.add_le_add_right hs (factorBodyConstant * factorSize t r ^ 8))
  have hlast : (r - 1) * (Nat.size (r - 1) + 1 +
      factorBodyConstant * factorSize t r ^ 8) ≤
      factorSize t r ^ 2 + factorBodyConstant * factorSize t r ^ 9 := by
    convert hmul using 1; ring
  have hpos : 1 ≤ factorSize t r ^ 9 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hinit, hit, hlast, hs, hp2, hp1, hpos]

end PCP.Lang.HadamardRow
