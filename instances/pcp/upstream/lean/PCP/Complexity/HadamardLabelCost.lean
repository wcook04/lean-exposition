/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardLabelLang

/-!
# Charged costs of Hadamard row label adapters

Serialization bounds count binary code sizes, not numeric code values. All
coefficient transformations retain the complete materialized cost certificates.
-/

namespace PCP.Lang.HadamardLabel

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList

variable {t a b r : ℕ}

theorem encode_size (p : Coefficients t r) : listSize (encode p) ≤ 2 * 2 ^ t := by
  have hb := BinaryField.listSize_bits (encode_bits p)
  have hd := BooleanCoefficientTransform.masks_length_le t r
  simp only [encode_length, BooleanMask.masks_length] at hb hd
  omega

theorem decode_cost (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists 0 = encode p) :
    (decode.run st).2 ≤ (WordCodec.passConstant * 3 + 20) * (2 ^ t + 1) ^ 2 := by
  rw [decode, Stmt.run_rename_cost WordCodec.decode decodeRegs decodeLists
    (show Function.Injective decodeRegs from Fin.castLE_injective _)
    (show Function.Injective decodeLists from fun i j _ => Subsingleton.elim i j)]
  have hc := WordCodec.decode_cost (st.restrict decodeRegs decodeLists)
    (by change BinaryField.Bits (st.lists 0); rw [hp]; exact encode_bits p)
  change _ ≤ (WordCodec.passConstant * 3 + 20) * ((st.lists 0).length + 1) ^ 2 at hc
  rw [hp, encode_length] at hc
  have hd := BooleanCoefficientTransform.masks_length_le t r
  rw [BooleanMask.masks_length] at hd
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem emit_cost (L : Fin 32) (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists L = encode p) :
    ((emit L).run st).2 ≤ (WordCodec.passConstant * 3 + 30) * (2 ^ t + 1) ^ 2 := by
  let s := setList st 0 (st.lists L)
  have hc := decode_cost p s (by simpa [s] using hp)
  have ho := decode_run p s (by simpa [s] using hp)
  dsimp only [s] at hc ho
  simp only [emit, run_seq_snd, run_copy_snd, run_copy_fst]
  generalize hs : (decode.run (setList st 0 (st.lists L))).1 = u at *
  change (listSize (st.lists L) + 1) + ((decode.run (setList st 0 (st.lists L))).2 +
    (Nat.size (u.regs 1) + 1) + 1) + 1 ≤ _
  rw [ho]
  have hpSize : listSize (st.lists L) ≤ 2 * 2 ^ t := by rw [hp]; exact encode_size p
  have hcode := code_size p
  nlinarith [Nat.zero_le ((2 ^ t) ^ 2)]

theorem add_cost (p q : Coefficients t r) (st : State 80 32)
    (hp : st.lists 28 = encode p) (hq : st.lists 29 = encode q) (he : st.lists 7 = []) :
    (add.run st).2 ≤ 60 * (2 ^ t + 1) ^ 2 := by
  rw [add, Stmt.run_rename_cost BooleanLabelAddition.add addRegs addLists
    (show Function.Injective addRegs from Fin.castLE_injective _) addLists_injective]
  have hc := BooleanLabelAddition.add_cost p q (st.restrict addRegs addLists) hp hq he
  have hd := BooleanCoefficientTransform.masks_length_le t r
  rw [BooleanMask.masks_length] at hd
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem sum_cost (L K : Fin 32) (hK : K ≠ 28) (p q : Coefficients t r)
    (st : State 80 32) (hp : st.lists L = encode p) (hq : st.lists K = encode q)
    (he : st.lists 7 = []) :
    ((sum L K).run st).2 ≤ 70 * (2 ^ t + 1) ^ 2 := by
  let s := setList (setList st 28 (st.lists L)) 29 (st.lists K)
  have hc := add_cost p q s (by simp [s, Function.update, hp])
    (by simpa [s] using hq) (by simp [s, Function.update, he])
  simp only [sum, run_seq_snd, run_copy_snd, run_copy_fst, setList_lists,
    Function.update_of_ne hK]
  change (listSize (st.lists L) + 1) + ((listSize (st.lists K) + 1) +
    (add.run s).2 + 1) + 1 ≤ _
  rw [hp, hq]
  nlinarith [encode_size p, encode_size q, Nat.zero_le ((2 ^ t) ^ 2)]

theorem emitSum_cost (L K : Fin 32) (hK : K ≠ 28) (p q : Coefficients t r)
    (st : State 80 32) (hp : st.lists L = encode p) (hq : st.lists K = encode q)
    (he : st.lists 7 = []) :
    ((emitSum L K).run st).2 ≤ (WordCodec.passConstant * 3 + 101) * (2 ^ t + 1) ^ 2 := by
  have hsum := sum_cost L K hK p q st hp hq he
  have hh := sum_run L K hK p q st hp hq he
  simp only [emitSum, run_seq_snd]
  generalize hs : ((sum L K).run st).1 = s at *
  have hemit := emit_cost 1 (p + q) s hh
  have hpos : 1 ≤ (2 ^ t + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hsum, hemit, hpos]

theorem embed_cost (p : Coefficients t a) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 54 = a) (hr : st.regs 56 = r)
    (he : st.lists 7 = []) (hp : st.lists 13 = encode p) :
    (embed.run st).2 ≤ (BooleanLabelTransform.queryConstant + 100) *
      (2 ^ t + Nat.size a + Nat.size a + Nat.size r + 3) ^ 8 := by
  rw [embed, Stmt.run_rename_cost BooleanLabelTransform.embed transformRegs transformLists
    (show Function.Injective transformRegs from Fin.castLE_injective _)
    (show Function.Injective transformLists from Fin.castLE_injective _)]
  exact BooleanLabelTransform.embed_cost p (st.restrict transformRegs transformLists)
    ht ha hr he hp

theorem product_cost (p : Coefficients t a) (q : Coefficients t b)
    (st : State 80 32) (ht : st.regs 20 = t) (ha : st.regs 54 = a)
    (hb : st.regs 55 = b) (hr : st.regs 56 = r) (he : st.lists 7 = [])
    (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    (product.run st).2 ≤ BooleanLabelTransform.queryConstant *
      (2 ^ t + Nat.size a + Nat.size b + Nat.size r + 3) ^ 8 := by
  rw [product, Stmt.run_rename_cost (BooleanLabelTransform.query true) transformRegs transformLists
    (show Function.Injective transformRegs from Fin.castLE_injective _)
    (show Function.Injective transformLists from Fin.castLE_injective _)]
  exact BooleanLabelTransform.query_cost true p q (st.restrict transformRegs transformLists)
    ht ha hb hr he hp hq

theorem constant_cost (z : ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hr : st.regs 56 = r) (hz : st.regs 51 = z.val)
    (he : st.lists 7 = []) :
    (constant.run st).2 ≤ (BooleanLabelTransform.queryConstant + 200) *
      (2 ^ t + Nat.size r + 3) ^ 8 := by
  rw [constant, Stmt.run_rename_cost BooleanLabelConstructors.constant transformRegs transformLists
    (show Function.Injective transformRegs from Fin.castLE_injective _)
    (show Function.Injective transformLists from Fin.castLE_injective _)]
  exact BooleanLabelConstructors.constant_cost z (st.restrict transformRegs transformLists)
    ht hr hz he

end PCP.Lang.HadamardLabel
