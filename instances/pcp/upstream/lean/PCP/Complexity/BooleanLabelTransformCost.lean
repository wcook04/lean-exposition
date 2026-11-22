/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelTransform

/-!
# Polynomial charged bounds for complete coefficient-label transformations

All source-mask construction, actual truth-table evaluation, output-mask
construction and coefficient recovery are included in the degree-eight bound.
-/

namespace PCP.Lang.BooleanLabelTransform

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList
open BooleanLabelKernel BooleanLabelTable

variable {t a b r : ℕ}

theorem masks_cost (right : Bool) (st : State 57 20) (ht : st.regs 20 = t)
    (hd : st.regs (degreeReg right) = a) (he : st.lists 7 = []) :
    ((masks right).run st).2 ≤ 500000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  let s := setReg st 21 a
  have hc : ((BooleanMask.enumerateMasks.rename enumRegs (enumLists right)).run s).2 ≤
      400000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
    rw [Stmt.run_rename_cost BooleanMask.enumerateMasks enumRegs (enumLists right)
      (show Function.Injective enumRegs from Fin.castLE_injective _) (enumLists_injective right)]
    apply BooleanMask.enumerateMasks_cost t a
    · simpa [State.restrict, s, enumRegs, Function.update] using ht
    · simp [State.restrict, s, enumRegs]
    · cases right <;> simpa [State.restrict, s, enumLists] using he
  simp only [masks, run_seq_snd, run_assign_fst, Expr.eval, hd]
  change (Expr.var (degreeReg right)).cost st.regs +
    ((BooleanMask.enumerateMasks.rename enumRegs (enumLists right)).run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hd]
  have hlow : Nat.size a + 3 ≤ (2 ^ t + Nat.size a + 3) ^ 4 :=
    (Nat.add_le_add_right (Nat.le_add_left (Nat.size a) (2 ^ t)) 3).trans (Nat.le_pow (by decide))
  nlinarith only [hc, hlow]

theorem prepare_cost (st : State 57 20) (ht : st.regs 20 = t)
    (ha : st.regs 54 = a) (hb : st.regs 55 = b) (he : st.lists 7 = []) :
    (prepare.run st).2 ≤ 1200000 * (2 ^ t + Nat.size a + Nat.size b + 3) ^ 4 := by
  have hl := masks_cost false st ht ha he
  have hs20 := run_regs_frame (masks false) 20 (by decide) st
  have hs55 := run_regs_frame (masks false) 55 (by decide) st
  have hs7 := run_lists_frame (masks false) 7 (by decide) st
  simp only [prepare, run_seq_snd]
  generalize hs : ((masks false).run st).1 = s at *
  have hr := masks_cost true s (hs20.trans ht) (hs55.trans hb) (hs7.trans he)
  have hN := masks_cardinality true s (hs20.trans ht)
  generalize hu : ((masks true).run s).1 = u at *
  change ((masks false).run st).2 + (((masks true).run s).2 +
    ((Expr.var 28).cost u.regs + (Expr.const 1).cost (setReg u 52 (u.regs 28)).regs + 1) + 1) +
    1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hN, Nat.size_one]
  have hl' := hl.trans (Nat.mul_le_mul_left 500000 (Nat.pow_le_pow_left (by omega :
    2 ^ t + Nat.size a + 3 ≤ 2 ^ t + Nat.size a + Nat.size b + 3) 4))
  have hr' := hr.trans (Nat.mul_le_mul_left 500000 (Nat.pow_le_pow_left (by omega :
    2 ^ t + Nat.size b + 3 ≤ 2 ^ t + Nat.size a + Nat.size b + 3) 4))
  have hn : Nat.size (2 ^ t) ≤ 2 ^ t := size_le_self _
  have hlow : 2 ^ t + 3 ≤ (2 ^ t + Nat.size a + Nat.size b + 3) ^ 4 :=
    (by omega : 2 ^ t + 3 ≤ 2 ^ t + Nat.size a + Nat.size b + 3).trans
      (Nat.le_pow (by decide))
  nlinarith only [hl', hr', hn, hlow]

theorem recover_cost (f : (Fin t → ZMod 2) → ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (hv : st.lists 16 = table t f)
    (he : st.lists 7 = []) :
    (recover.run st).2 ≤ (10000000 + 625 * (BooleanMaskSubset.passConstant + 300)) *
      (2 ^ t + Nat.size r + 3) ^ 8 := by
  rw [recover, Stmt.run_rename_cost BooleanCoefficientTransform.transform enumRegs transformLists
    (show Function.Injective enumRegs from Fin.castLE_injective _) transformLists_injective]
  exact BooleanCoefficientTransform.transform_cost t r f
    (st.restrict enumRegs transformLists) ht hr hv he

def queryConstant : ℕ :=
  13000000 + kernelConstant + 625 * (BooleanMaskSubset.passConstant + 300)

theorem query_cost (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (ht : st.regs 20 = t) (ha : st.regs 54 = a)
    (hb : st.regs 55 = b) (hr : st.regs 56 = r) (he : st.lists 7 = [])
    (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    ((query product).run st).2 ≤
      queryConstant * (2 ^ t + Nat.size a + Nat.size b + Nat.size r + 3) ^ 8 := by
  let M := 2 ^ t + Nat.size a + Nat.size b + Nat.size r + 3
  have hprep := prepare_cost st ht ha hb he
  have hc := prepare_context p q st ht ha hb he hp hq
  have hs56 := run_regs_frame prepare 56 (by decide) st
  simp only [query, run_seq_snd]
  generalize hs : (prepare.run st).1 = s at *
  have htable := tabulate_table product p q s hc
  have htab := tabulate_cost product p q s hc
  have hu20 := run_regs_frame (tabulate product) 20 (by cases product <;> decide) s
  have hu56 := run_regs_frame (tabulate product) 56 (by cases product <;> decide) s
  have hu7 := run_lists_frame (tabulate product) 7 (by cases product <;> decide) s
  generalize hu : ((tabulate product).run s).1 = u at *
  have hrec := recover_cost (function product p q) (setReg u 23 (u.regs 56))
    (by simpa [Function.update] using hu20.trans hc.1.1)
    (by simpa using hu56.trans (hs56.trans hr)) htable (hu7.trans hc.2.2.2)
  change (prepare.run st).2 + (((tabulate product).run s).2 +
    ((Expr.var 56).cost u.regs + (recover.run (setReg u 23 (u.regs 56))).2 + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hu56, hs56, hr]
  have hMpos : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have h4 : (2 ^ t + Nat.size a + Nat.size b + 3) ^ 4 ≤ M ^ 8 :=
    (Nat.pow_le_pow_left (by dsimp [M]; omega) 4).trans
      (Nat.pow_le_pow_right hMpos (by decide))
  have h7 : (2 ^ t + 3) ^ 7 ≤ M ^ 8 :=
    (Nat.pow_le_pow_left (by dsimp [M]; omega) 7).trans
      (Nat.pow_le_pow_right hMpos (by decide))
  have h8 : (2 ^ t + Nat.size r + 3) ^ 8 ≤ M ^ 8 :=
    Nat.pow_le_pow_left (by dsimp [M]; omega) _
  have hprep' := hprep.trans (Nat.mul_le_mul_left 1200000 h4)
  have htab' := htab.trans (Nat.mul_le_mul_left (kernelConstant + 40) h7)
  rw [hu56, hs56, hr] at hrec
  have hrec' := hrec.trans (Nat.mul_le_mul_left _ h8)
  have hlow : Nat.size r + 3 ≤ M ^ 8 :=
    (by simpa only [M, Nat.add_assoc] using
      (Nat.le_add_left (Nat.size r + 3) (2 ^ t + Nat.size a + Nat.size b)) :
      Nat.size r + 3 ≤ M).trans
        (Nat.le_pow (by decide))
  change _ ≤ queryConstant * M ^ 8
  unfold queryConstant
  nlinarith only [hprep', htab', hrec', hlow]

/-- Embedding includes duplication of the source array and preparation of both source degrees. -/
theorem embed_cost (p : Coefficients t a) (st : State 57 20)
    (ht : st.regs 20 = t) (ha : st.regs 54 = a) (hr : st.regs 56 = r)
    (he : st.lists 7 = []) (hp : st.lists 13 = encode p) :
    (embed.run st).2 ≤ (queryConstant + 100) *
      (2 ^ t + Nat.size a + Nat.size a + Nat.size r + 3) ^ 8 := by
  let s := setReg (setList st 18 (st.lists 13)) 55 (st.regs 54)
  have hh := query_cost false p p s
    (by simpa [s, Function.update] using ht) (by simpa [s, Function.update] using ha)
    (by simpa [s] using ha) (by simpa [s, Function.update] using hr)
    (by simpa [s, Function.update] using he) (by simpa [s, Function.update] using hp)
    (by simpa [s] using hp)
  have hsize : listSize (encode p) ≤ 2 * 2 ^ t := by
    have hbits := BinaryField.listSize_bits (encode_bits p)
    have hlen := BooleanCoefficientTransform.masks_length_le t a
    simp only [encode_length, BooleanMask.masks_length] at hbits hlen
    omega
  simp only [embed, run_seq_snd, run_copy_snd, run_copy_fst, run_assign_fst, Expr.eval,
    setList_regs]
  change (listSize (st.lists 13) + 1) + ((Expr.var 54).cost st.regs +
    ((query false).run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, ha, hp]
  have hlow : 2 ^ t + Nat.size a + 3 ≤
      (2 ^ t + Nat.size a + Nat.size a + Nat.size r + 3) ^ 8 :=
    (by omega : 2 ^ t + Nat.size a + 3 ≤
      2 ^ t + Nat.size a + Nat.size a + Nat.size r + 3).trans (Nat.le_pow (by decide))
  nlinarith only [hh, hsize, hlow]

end PCP.Lang.BooleanLabelTransform
