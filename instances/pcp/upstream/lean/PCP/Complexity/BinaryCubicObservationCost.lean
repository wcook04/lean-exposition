/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryCubicObservation
import PCP.Complexity.BinaryCubicCodeCost

/-!
# Cost of affine cubic observations

The bound includes numeric field arithmetic and stored affine evaluation. It is
polynomial in the full Boolean point-domain size, as required by table generation.
-/

namespace PCP.Lang.BinaryCubicObservation

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode

private theorem assign_cost {R Q : ℕ} (x : Fin R) (e : Expr R) (st : State R Q) :
    ((Stmt.assign x e).run st).2 = e.cost st.regs := rfl

/-- A uniform bound for applying the stored affine label to a numeric field result. -/
theorem observe_cost {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 52 16)
    (ht : st.regs 20 = t) (ha : st.regs 26 = (fieldEquiv t a).val)
    (hm : st.lists 12 = BooleanMask.masks t 1) (hL : st.lists 13 = encode L) :
    (observe.run st).2 ≤ 1000 * (BooleanMaskSubset.passConstant + 200) * (2 ^ t + 3) ^ 6 := by
  let s := setReg (setReg st 36 (st.regs 20)) 38 (st.regs 26)
  have hs := BooleanCoefficientEvaluation.evaluate_cost (s.restrict evalRegs evalLists)
    (by change ∀ c ∈ st.lists 13, c < 2; rw [hL]; exact encode_bits L)
  change _ ≤ (BooleanMaskSubset.passConstant + 200) *
    (st.regs 20 + Nat.size (st.regs 26) + listSize (st.lists 12) +
      listSize (st.lists 13) + (st.lists 12).length + 4) ^ 3 at hs
  rw [ht, ha, hm, hL] at hs
  have hcode : Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt
  have hmask := BooleanCoefficientTransform.masks_size t 1
  have hcoef : listSize (encode L) ≤ 2 * (1 + t) := by
    simpa [encode_length, BooleanCoefficientIndex.dimension_one] using
      BinaryField.listSize_bits (encode_bits L)
  have hlen : (BooleanMask.masks t 1).length = 1 + t := by simp
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hM : t + Nat.size (fieldEquiv t a).val + listSize (BooleanMask.masks t 1) +
      listSize (encode L) + (BooleanMask.masks t 1).length + 4 ≤ 8 * (2 ^ t + 3) ^ 2 := by
    nlinarith only [hcode, hmask, hcoef, hlen, htq, Nat.zero_le ((2 ^ t) ^ 2)]
  have hc : (evaluate52.run s).2 ≤
      512 * (BooleanMaskSubset.passConstant + 200) * (2 ^ t + 3) ^ 6 := by
    rw [evaluate52, Stmt.run_rename_cost BooleanCoefficientEvaluation.evaluate evalRegs evalLists
      evalRegs_injective evalLists_injective]
    calc
      _ ≤ (BooleanMaskSubset.passConstant + 200) * (8 * (2 ^ t + 3) ^ 2) ^ 3 :=
        hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 3))
      _ = _ := by ring
  have hwidth : Nat.size t ≤ 2 ^ t := (size_le_self _).trans htq
  have hpoint : Nat.size (st.regs 26) ≤ 2 ^ t := by rw [ha]; exact hcode.trans htq
  simp only [observe, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 20).cost st.regs +
    ((Expr.var 26).cost (setReg st 36 (st.regs 20)).regs + (evaluate52.run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, ht]
  have hpow : 2 ^ t + 3 ≤ (2 ^ t + 3) ^ 6 := Nat.le_pow (by decide)
  nlinarith only [hc, hwidth, hpoint, hpow]

theorem cube52_cost {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) : (cube52.run st).2 ≤ 80000000 * (t + 1) ^ 4 := by
  rw [cube52, Stmt.run_rename_cost cubeMinusOne fieldRegs fieldLists
    (show Function.Injective fieldRegs from Fin.castLE_injective _)
    (show Function.Injective fieldLists from Fin.castLE_injective _)]
  exact cubeMinusOne_cost _ a ht ha hm he

theorem mul52_cost {t : ℕ} [NeZero t] (a b : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hb : st.regs 25 = (fieldEquiv t b).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) : (mul52.run st).2 ≤ 20000000 * (t + 1) ^ 4 := by
  rw [mul52, Stmt.run_rename_cost (binary .mul) fieldRegs fieldLists
    (show Function.Injective fieldRegs from Fin.castLE_injective _)
    (show Function.Injective fieldLists from Fin.castLE_injective _)]
  exact binary_cost .mul (Nat.pos_of_ne_zero (NeZero.ne t)) _ (fieldEquiv t a)
    (fieldEquiv t b) ht ha hb hm he

theorem weightedTail_cost {t : ℕ} [NeZero t] (a w saved : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 26 = (fieldEquiv t a).val) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hsave : st.regs 50 = (fieldEquiv t saved).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) : (weightedTail.run st).2 ≤ 21000000 * (t + 1) ^ 4 := by
  let s := setReg (setReg st 24 (st.regs 51)) 25 (st.regs 26)
  have hc := mul52_cost w a s (by simpa [s, Function.update] using ht)
    (by simpa [s, Function.update] using hw) (by simpa [s] using ha) hm he
  have hframe := run_regs_frame mul52 50 (by decide) s
  have hssave : s.regs 50 = (fieldEquiv t saved).val := by
    simpa [s, Function.update] using hsave
  have hwsize : Nat.size (st.regs 51) ≤ t := by rw [hw]; exact Nat.size_le.mpr (fieldEquiv t w).isLt
  have hasize : Nat.size (st.regs 26) ≤ t := by rw [ha]; exact Nat.size_le.mpr (fieldEquiv t a).isLt
  have hsavedsize : Nat.size ((mul52.run s).1.regs 50) ≤ t := by
    rw [hframe, hssave]
    exact Nat.size_le.mpr (fieldEquiv t saved).isLt
  dsimp only [s] at hc hframe hsavedsize
  simp only [weightedTail, run_seq_snd, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  generalize hz : mul52.run (setReg (setReg st 24 (st.regs 51)) 25 (st.regs 26)) = z at *
  simp only [assign_cost, Expr.cost, Expr.readSize, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  have hpow : t ≤ (t + 1) ^ 4 := (Nat.le_succ _).trans (Nat.le_pow (by decide))
  have hpositive : 1 ≤ (t + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  omega

theorem weightedField_cost {t : ℕ} [NeZero t] (a w : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) : (weightedField.run st).2 ≤ 110000000 * (t + 1) ^ 4 := by
  let s := setReg st 50 (st.regs 24)
  have hst : s.regs 20 = t := by simpa [s, Function.update] using ht
  have hsa : s.regs 24 = (fieldEquiv t a).val := by simpa [s, Function.update] using ha
  have hc := cube52_cost a s hst hsa hm he
  have hr := cube52_run a s hst hsa hm he
  have hs20 := run_regs_frame cube52 20 (by decide) s
  have hs51 := run_regs_frame cube52 51 (by decide) s
  have hs50 := run_regs_frame cube52 50 (by decide) s
  have hs3 := run_lists_frame cube52 3 (by decide) s
  have hs7 := run_lists_frame cube52 7 (by decide) s
  have hsw : s.regs 51 = (fieldEquiv t w).val := by simpa [s, Function.update] using hw
  have hssaved : s.regs 50 = (fieldEquiv t a).val := by simpa [s] using ha
  dsimp only [s] at hc hr hs20 hs51 hs50 hs3 hs7 hst hsw hssaved
  simp only [weightedField, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hsu : (cube52.run (setReg st 50 (st.regs 24))).1 = u at *
  have hf := weightedTail_cost (a ^ 3 - 1) w a u (hs20.trans hst) hr
    (hs51.trans hsw) (hs50.trans hssaved) (hs3.trans hm) (hs7.trans he)
  have hasize : Nat.size (st.regs 24) ≤ t := by rw [ha]; exact Nat.size_le.mpr (fieldEquiv t a).isLt
  simp only [assign_cost, Expr.cost, Expr.readSize, Expr.eval]
  have hpow : t ≤ (t + 1) ^ 4 := (Nat.le_succ _).trans (Nat.le_pow (by decide))
  have hpositive : 1 ≤ (t + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  omega

/-- Shared constant for weighted and unweighted observation kernels. -/
def observationConstant : ℕ := 200000000 + 1000 * (BooleanMaskSubset.passConstant + 200)

theorem kernel_cost {t : ℕ} [NeZero t] (weighted : Bool)
    (a w : BinaryMaterializedField.Element t) (L : Coefficients t 1) (st : State 52 16)
    (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hw : st.regs 51 = (fieldEquiv t w).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hL : st.lists 13 = encode L) :
    ((kernel weighted).run st).2 ≤ observationConstant * (2 ^ t + 3) ^ 6 := by
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hpow : (t + 1) ^ 4 ≤ (2 ^ t + 3) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 4).trans
      (Nat.pow_le_pow_right (by have := Nat.zero_le (2 ^ t); omega) (by decide))
  have hpositive : 1 ≤ (2 ^ t + 3) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  cases weighted
  · have hc := cube52_cost a st ht ha hmod he
    have hr := cube52_run a st ht ha hmod he
    have hs20 := run_regs_frame cube52 20 (by decide) st
    have hs12 := run_lists_frame cube52 12 (by decide) st
    have hs13 := run_lists_frame cube52 13 (by decide) st
    simp only [kernel, Bool.false_eq_true, ite_false, cubic, run_seq_snd]
    generalize hs : (cube52.run st).1 = s at *
    have ho := observe_cost (a ^ 3 - 1) L s (hs20.trans ht) hr (hs12.trans hm) (hs13.trans hL)
    unfold observationConstant
    nlinarith only [hc, ho, hpow, hpositive]
  · have hc := weightedField_cost a w st ht ha hw hmod he
    have hr := weightedField_run a w st ht ha hw hmod he
    have hs20 := run_regs_frame weightedField 20 (by decide) st
    have hs12 := run_lists_frame weightedField 12 (by decide) st
    have hs13 := run_lists_frame weightedField 13 (by decide) st
    simp only [kernel, ite_true, weightedCubic, run_seq_snd]
    generalize hs : (weightedField.run st).1 = s at *
    have ho := observe_cost (w * (a ^ 3 - 1)) L s (hs20.trans ht) hr
      (hs12.trans hm) (hs13.trans hL)
    unfold observationConstant
    nlinarith only [hc, ho, hpow, hpositive]

end PCP.Lang.BinaryCubicObservation
