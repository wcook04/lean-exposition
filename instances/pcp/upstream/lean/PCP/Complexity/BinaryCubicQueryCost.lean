/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryCubicQueryLang

/-!
# Polynomial cost of the complete cubic coefficient query

This includes affine-mask generation, concrete field truth-table construction,
and the complete bounded coefficient-recovery transform.
-/

namespace PCP.Lang.BinaryCubicQueryLang

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode
open BinaryCubicTable BinaryCubicObservation

variable {t : ℕ}

private theorem assign_cost {R Q : ℕ} (x : Fin R) (e : Expr R) (st : State R Q) :
    ((Stmt.assign x e).run st).2 = e.cost st.regs := rfl

theorem affineMasks_cost (st : State 54 17) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (affineMasks.run st).2 ≤ 500000 * (2 ^ t + 4) ^ 4 := by
  let s := setReg st 21 1
  have hc : ((BooleanMask.enumerateMasks.rename enumRegs affineLists).run s).2 ≤
      400000 * (2 ^ t + 4) ^ 4 := by
    rw [Stmt.run_rename_cost BooleanMask.enumerateMasks enumRegs affineLists
      (show Function.Injective enumRegs from Fin.castLE_injective _) affineLists_injective]
    have hh := BooleanMask.enumerateMasks_cost t 1 (s.restrict enumRegs affineLists)
      (by simpa [State.restrict, enumRegs, s, Function.update] using ht)
      (by rfl) (by simpa [State.restrict, affineLists, s] using he)
    simpa only [Nat.size_one, Nat.add_assoc] using hh
  simp only [affineMasks, run_seq_snd, run_assign_fst, Expr.eval, assign_cost,
    Expr.cost, Expr.readSize, Nat.size_one]
  change 3 + ((BooleanMask.enumerateMasks.rename enumRegs affineLists).run s).2 + 1 ≤ _
  have hp : 1 ≤ (2 ^ t + 4) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  omega

theorem prepare_cost (st : State 54 17) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (prepare.run st).2 ≤ 1000000 * (2 ^ t + 4) ^ 4 := by
  have hc := affineMasks_cost st ht he
  have hq := affineMasks_cardinality st ht
  simp only [prepare, run_seq_snd]
  generalize hs : (affineMasks.run st).1 = s at *
  simp only [assign_cost, Expr.cost, Expr.readSize, Expr.eval, Nat.size_one]
  have hsize : Nat.size (s.regs 28) ≤ 2 ^ t := by rw [hq]; exact size_le_self _
  have hp : 2 ^ t + 4 ≤ (2 ^ t + 4) ^ 4 := Nat.le_pow (by decide)
  omega

theorem transform54_cost (f : (Fin t → ZMod 2) → ZMod 2) (st : State 54 17)
    (ht : st.regs 20 = t) (hr : st.regs 23 = 3) (hv : st.lists 16 = table t f)
    (he : st.lists 7 = []) :
    (transform54.run st).2 ≤ (10000000 + 625 * (BooleanMaskSubset.passConstant + 300)) *
      (2 ^ t + 5) ^ 8 := by
  rw [transform54, Stmt.run_rename_cost BooleanCoefficientTransform.transform
    enumRegs transformLists
    (show Function.Injective enumRegs from Fin.castLE_injective _) transformLists_injective]
  have h := BooleanCoefficientTransform.transform_cost t 3 f (st.restrict enumRegs transformLists)
    ht hr hv he
  simpa only [show Nat.size 3 = 2 from rfl, Nat.add_assoc] using h

/-- A fixed coefficient of a degree-eight polynomial bounds the whole query translation. -/
def queryConstant : ℕ :=
  12000000 + observationConstant + 625 * (BooleanMaskSubset.passConstant + 300)

theorem query_cost [NeZero t] (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (ht : st.regs 20 = t)
    (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hL : st.lists 13 = encode L) :
    ((query weighted).run st).2 ≤ queryConstant * (2 ^ t + 5) ^ 8 := by
  have hprep := prepare_cost st ht he
  have hc := prepare_context w L st ht hw hm he hL
  simp only [query, run_seq_snd]
  generalize hs : (prepare.run st).1 = s at *
  have htab := tabulate_cost weighted w L s hc
  have htable := tabulate_table weighted w L s hc
  have hs20 := run_regs_frame (tabulate weighted) 20 (by cases weighted <;> decide) s
  have hs7 := run_lists_frame (tabulate weighted) 7 (by cases weighted <;> decide) s
  generalize hu : ((tabulate weighted).run s).1 = u at *
  have htrans := transform54_cost (booleanFunction weighted w L) (setReg u 23 3)
    (by simpa [Function.update] using hs20.trans hc.1) (by simp)
    htable (hs7.trans hc.2.2.2.1)
  simp only [run_assign_fst, Expr.eval, assign_cost, Expr.cost, Expr.readSize,
    show Nat.size 3 = 2 from rfl]
  have hbase : 1 ≤ 2 ^ t + 5 := Nat.succ_le_succ (Nat.zero_le _)
  have hpp : (2 ^ t + 4) ^ 4 ≤ (2 ^ t + 5) ^ 8 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 4).trans
      (Nat.pow_le_pow_right hbase (by decide))
  have htp : (2 ^ t + 3) ^ 7 ≤ (2 ^ t + 5) ^ 8 :=
    (Nat.pow_le_pow_left (by omega) 7).trans (Nat.pow_le_pow_right hbase (by decide))
  have hp : 1 ≤ (2 ^ t + 5) ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hprep' := hprep.trans (Nat.mul_le_mul_left 1000000 hpp)
  have htab' := htab.trans (Nat.mul_le_mul_left (observationConstant + 40) htp)
  unfold queryConstant
  nlinarith only [hprep', htab', htrans, hp]

end PCP.Lang.BinaryCubicQueryLang
