/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelKernel

/-!
# Polynomial charged bounds for label-evaluation kernels

The bound uses the full Boolean domain size and applies to every degree bound,
including degrees exceeding the number of variables.
-/

namespace PCP.Lang.BooleanLabelKernel

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList

variable {t a b : ℕ}

theorem evaluate_cost (right : Bool) (p : Coefficients t a) (x : Fin (2 ^ t))
    (st : State 57 20) (ht : st.regs 20 = t) (hx : st.regs 24 = x.val)
    (hm : st.lists (evalLists right 0) = BooleanMask.masks t a)
    (hp : st.lists (evalLists right 1) = encode p) :
    ((evaluate right).run st).2 ≤
      1000 * (BooleanMaskSubset.passConstant + 200) * (2 ^ t + 3) ^ 6 := by
  let s := setReg (setReg st 36 (st.regs 20)) 38 (st.regs 24)
  have hs := BooleanCoefficientEvaluation.evaluate_cost (s.restrict evalRegs (evalLists right))
    (by change ∀ c ∈ st.lists (evalLists right 1), c < 2; rw [hp]; exact encode_bits p)
  change _ ≤ (BooleanMaskSubset.passConstant + 200) *
    (st.regs 20 + Nat.size (st.regs 24) + listSize (st.lists (evalLists right 0)) +
      listSize (st.lists (evalLists right 1)) + (st.lists (evalLists right 0)).length + 4) ^ 3 at hs
  rw [ht, hx, hm, hp] at hs
  have hxsize : Nat.size x.val ≤ t := Nat.size_le.mpr x.isLt
  have hmask := BooleanCoefficientTransform.masks_size t a
  have hlen := BooleanCoefficientTransform.masks_length_le t a
  have hcoef : listSize (encode p) ≤ 2 * 2 ^ t := by
    have hh := BinaryField.listSize_bits (encode_bits p)
    simp only [encode_length, BooleanMask.masks_length] at hh hlen
    omega
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hM : t + Nat.size x.val + listSize (BooleanMask.masks t a) +
      listSize (encode p) + (BooleanMask.masks t a).length + 4 ≤ 8 * (2 ^ t + 3) ^ 2 := by
    nlinarith only [hxsize, hmask, hcoef, hlen, htq, Nat.zero_le ((2 ^ t) ^ 2)]
  have hc : ((BooleanCoefficientEvaluation.evaluate.rename evalRegs (evalLists right)).run s).2 ≤
      512 * (BooleanMaskSubset.passConstant + 200) * (2 ^ t + 3) ^ 6 := by
    rw [Stmt.run_rename_cost BooleanCoefficientEvaluation.evaluate evalRegs (evalLists right)
      evalRegs_injective (evalLists_injective right)]
    calc
      _ ≤ (BooleanMaskSubset.passConstant + 200) * (8 * (2 ^ t + 3) ^ 2) ^ 3 :=
        hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 3))
      _ = _ := by ring
  have hwidth : Nat.size t ≤ 2 ^ t := (size_le_self _).trans htq
  simp only [evaluate, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 20).cost st.regs + ((Expr.var 24).cost (setReg st 36 (st.regs 20)).regs +
    ((BooleanCoefficientEvaluation.evaluate.rename evalRegs (evalLists right)).run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, ht, hx]
  have hpow : 2 ^ t + 3 ≤ (2 ^ t + 3) ^ 6 := Nat.le_pow (by decide)
  nlinarith only [hc, hwidth, hxsize, htq, hpow]

def kernelConstant : ℕ := 2100 * (BooleanMaskSubset.passConstant + 200)

theorem kernel_cost (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (x : Fin (2 ^ t)) (st : State 57 20) (hc : Context p q st)
    (hx : st.regs 24 = x.val) :
    ((kernel product).run st).2 ≤ kernelConstant * (2 ^ t + 3) ^ 6 := by
  have hleft := evaluate_cost false p x st hc.1 hx hc.2.1 hc.2.2.1
  have hl := evaluate_run false p x st hc.1 hx hc.2.1 hc.2.2.1
  have hs20 := run_regs_frame (evaluate false) 20 (by decide) st
  have hs24 := run_regs_frame (evaluate false) 24 (by decide) st
  have hs19 := run_lists_frame (evaluate false) 19 (by decide) st
  have hs18 := run_lists_frame (evaluate false) 18 (by decide) st
  simp only [kernel, run_seq_snd]
  generalize hs : ((evaluate false).run st).1 = s at *
  have hpos : 1 ≤ (2 ^ t + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  cases product with
  | false =>
    change ((evaluate false).run st).2 + 1 + 1 ≤ _
    unfold kernelConstant
    nlinarith only [hleft, hpos, Nat.zero_le BooleanMaskSubset.passConstant]
  | true =>
    let u := setReg s 51 (s.regs 46)
    have hright := evaluate_cost true q x u
      (by simpa [u, Function.update] using hs20.trans hc.1)
      (by simpa [u, Function.update] using hs24.trans hx)
      (hs19.trans hc.2.2.2.1) (hs18.trans hc.2.2.2.2)
    have hr := evaluate_run true q x u
      (by simpa [u, Function.update] using hs20.trans hc.1)
      (by simpa [u, Function.update] using hs24.trans hx)
      (hs19.trans hc.2.2.2.1) (hs18.trans hc.2.2.2.2)
    have h51 := run_regs_frame (evaluate true) 51 (by decide) u
    dsimp only [u] at hright hr h51
    simp only [ite_true, productTail, run_seq_snd, run_assign_fst, Expr.eval]
    generalize hu : ((evaluate true).run (setReg s 51 (s.regs 46))).1 = v at *
    change ((evaluate false).run st).2 + ((Expr.var 46).cost s.regs +
      (((evaluate true).run (setReg s 51 (s.regs 46))).2 +
        (Expr.mul 51 46).cost v.regs + 1) + 1) + 1 ≤ _
    have hpv := ZMod.val_lt (BooleanCoefficientArithmetic.evaluate (point t x) p)
    have hqv := ZMod.val_lt (BooleanCoefficientArithmetic.evaluate (point t x) q)
    have hpz := size_le_one_of_le_one (Nat.le_of_lt_succ hpv)
    have hqz := size_le_one_of_le_one (Nat.le_of_lt_succ hqv)
    have hmul := size_le_one_of_le_one (by nlinarith :
      (BooleanCoefficientArithmetic.evaluate (point t x) p).val *
        (BooleanCoefficientArithmetic.evaluate (point t x) q).val ≤ 1)
    simp only [Expr.cost, Expr.readSize, Expr.eval, h51, setReg_regs,
      Function.update_self, hl, hr]
    rw [hl] at hright
    unfold kernelConstant
    nlinarith only [hleft, hright, hpz, hqz, hmul, hpos,
      Nat.zero_le BooleanMaskSubset.passConstant]

end PCP.Lang.BooleanLabelKernel
