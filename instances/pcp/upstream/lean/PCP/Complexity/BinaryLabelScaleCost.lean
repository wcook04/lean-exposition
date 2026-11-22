/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryLabelScale

/-!
# Charged cost of transposed scalar labels

Every output coordinate is produced by an actual materialized multiplication and
stored Boolean observation. The final bound is polynomial in the field order.
-/

namespace PCP.Lang.BinaryLabelScale

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode
open BinaryCubicObservation

variable {t : ℕ} [NeZero t]

def kernelConstant : ℕ := 21000000 + 1000 * (BooleanMaskSubset.passConstant + 200)

theorem observeProduct_cost (a b : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hb : st.regs 25 = (fieldEquiv t b).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hw : st.lists 13 = encode (BooleanCoefficientArithmetic.homogeneousIndex
      (by decide : 1 ≤ 1) w)) :
    (observeProduct.run st).2 ≤ kernelConstant * (2 ^ t + 3) ^ 6 := by
  have hc := mul52_cost a b st ht ha hb hmod he
  have hp := mul52_run a b st ht ha hb hmod he
  have hs20 := run_regs_frame mul52 20 (by decide) st
  have hs12 := run_lists_frame mul52 12 (by decide) st
  have hs13 := run_lists_frame mul52 13 (by decide) st
  simp only [observeProduct, run_seq_snd]
  generalize hs : (mul52.run st).1 = s at *
  have ho := observe_cost (a * b) (BooleanCoefficientArithmetic.homogeneousIndex
    (by decide : 1 ≤ 1) w) s (hs20.trans ht) hp (hs12.trans hm) (hs13.trans hw)
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hp4 : (t + 1) ^ 4 ≤ (2 ^ t + 3) ^ 6 :=
    (Nat.pow_le_pow_left (by omega : t + 1 ≤ 2 ^ t + 3) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hm' := hc.trans (Nat.mul_le_mul_left 20000000 hp4)
  have hpos : 1 ≤ (2 ^ t + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold kernelConstant
  nlinarith only [hm', ho, hpos]

theorem kernel_cost (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) (j : ℕ) (hj : j < t)
    (hi : st.regs 25 = 2 ^ j) :
    (kernel.run st).2 ≤ kernelConstant * (2 ^ t + 3) ^ 6 := by
  rw [kernel, Stmt.run_rename_cost observeProduct kernelRegs kernelLists
    (show Function.Injective kernelRegs from Fin.castLE_injective _)
    (show Function.Injective kernelLists from Fin.castLE_injective _)]
  exact observeProduct_cost a (basis ⟨j, hj⟩) w (st.restrict kernelRegs kernelLists)
    hc.1 hc.2.1 (by rw [basis_code]; exact hi) hc.2.2.1 hc.2.2.2.1
    hc.2.2.2.2.1 hc.2.2.2.2.2

theorem body_cost (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) (j : ℕ) (hj : j < t)
    (hi : st.regs 25 = 2 ^ j) :
    (body.run st).2 ≤ (kernelConstant + 10) * (2 ^ t + 3) ^ 6 := by
  have hk := kernel_cost a w st hc j hj hi
  have hr := kernel_run a w st hc j hj hi
  have hs25 := kernel_reg st 25 (by decide)
  have hsize : Nat.size (st.regs 25) ≤ t := by
    apply Nat.size_le.mpr
    rw [hi]
    exact Nat.pow_lt_pow_right (by decide) hj
  have hnext : Nat.size (st.regs 25 + st.regs 25) ≤ t + 1 := by
    apply Nat.size_le.mpr
    rw [hi, ← Nat.mul_two, ← pow_succ]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hbit : Nat.size (bit a w j) ≤ 1 :=
    size_le_one_of_le_one (Nat.le_of_lt_succ (bit_lt_two a w j))
  simp only [body, run_seq_snd]
  generalize hs : (kernel.run st).1 = s at *
  change (kernel.run st).2 + ((Nat.size (s.regs 46) + 1) +
    (Expr.add 25 25).cost (setList s 16 (s.regs 46 :: s.lists 16)).regs + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setList_regs, hr, hs25]
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hlow : t + 3 ≤ (2 ^ t + 3) ^ 6 :=
    (Nat.add_le_add_right htq 3).trans (Nat.le_pow (by decide))
  nlinarith only [hk, hsize, hnext, hbit, hlow]

theorem tabulate_cost (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) :
    (tabulate.run st).2 ≤ (kernelConstant + 40) * (2 ^ t + 3) ^ 7 := by
  let q := 2 ^ t
  let K := kernelConstant + 10
  let s := setReg (setList st 16 []) 25 1
  let Inv := fun j (u : State 54 18) => Context a w u ∧ u.regs 25 = 2 ^ j ∧
    listSize (u.lists 16) ≤ 2 * j
  have hinit : Inv 0 s := by
    simp [Inv, Context, s, Function.update, listSize, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2]
  have hstep : ∀ j u, j < t → Inv j u → Inv (j + 1) (body.run u).1 := by
    intro j u hj hu
    have hh := body_step a w u hu.1 j hj hu.2.1
    refine ⟨body_context a w u hu.1, hh.1, ?_⟩
    rw [hh.2]
    have hb : Nat.size (bit a w j) ≤ 1 :=
      size_le_one_of_le_one (Nat.le_of_lt_succ (bit_lt_two a w j))
    change Nat.size (bit a w j) + 1 + listSize (u.lists 16) ≤ _
    have hp := hu.2.2
    omega
  have hit := iterate_cost_idx body.run (Nat.size t + 1) (K * (q + 3) ^ 6) t Inv
    (by
      intro j u hj hu
      exact ⟨hstep j u hj hu, body_cost a w u hu.1 j hj hu.2.1⟩) s hinit
  have hout := iterate_inv body.run (Nat.size t + 1) t Inv hstep s hinit
  have hsz : Nat.size t ≤ t := size_le_self _
  have htq : t ≤ q := (Nat.lt_two_pow_self (n := t)).le
  have hit' : (iterate body.run (Nat.size t + 1) t s).2 ≤
      (q + 3) * (q + 3 + K * (q + 3) ^ 6) := hit.trans
    (Nat.mul_le_mul (by omega) (Nat.add_le_add_right (by omega) _))
  simp only [tabulate, run_seq_snd, run_copy_snd, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_snd, run_loop_fst, run_rev_snd, setReg_regs, setList_regs,
    Function.update, Fin.reduceEq, dite_false, hc.2.2.2.1, hc.1]
  change (listSize ([] : List ℕ) + 1) + ((Expr.const 1).cost _ +
    (((iterate body.run (Nat.size t + 1) t s).2 + Nat.size t + 1) +
      (listSize ((iterate body.run (Nat.size t + 1) t s).1.lists 16) + 1) + 1) + 1) + 1 ≤ _
  simp only [show listSize ([] : List ℕ) = 0 from rfl,
    Expr.cost, Expr.readSize, Expr.eval, Nat.size_one]
  change _ ≤ (K + 30) * (q + 3) ^ 7
  have hpow : (q + 3) ^ 2 ≤ (q + 3) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlow : q + 3 ≤ (q + 3) ^ 7 := Nat.le_pow (by decide)
  nlinarith only [hit', hout.2.2, hsz, htq, hpow, hlow]

omit [NeZero t] in
theorem masks_cost (st : State 54 18) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (masks.run st).2 ≤ 500000 * (2 ^ t + 4) ^ 4 := by
  rw [masks, Stmt.run_rename_cost BinaryCubicQueryLang.affineMasks id masksLists
    Function.injective_id (show Function.Injective masksLists from Fin.castLE_injective _)]
  exact BinaryCubicQueryLang.affineMasks_cost (st.restrict id masksLists) ht he

omit [NeZero t] in
theorem prepare_cost (w : Fin t → ZMod 2) (st : State 54 18)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (prepare.run st).2 ≤ 600000 * (2 ^ t + 4) ^ 4 := by
  have hm := masks_cost st ht he
  have hs17 := run_lists_frame masks 17 (by decide) st
  have hbits : BinaryField.Bits (List.ofFn (fun i => (w i).val)) := by
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hsize := BinaryField.listSize_bits hbits
  simp only [List.length_ofFn] at hsize
  simp only [prepare, run_seq_snd]
  generalize hs : (masks.run st).1 = s at *
  change (masks.run st).2 + ((listSize (s.lists 17) + 1) +
    ((Expr.const 0).cost _ + (Nat.size 0 + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero, hs17, hw]
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hlow : t + 4 ≤ (2 ^ t + 4) ^ 4 :=
    (Nat.add_le_add_right htq 4).trans (Nat.le_pow (by decide))
  nlinarith only [hm, hsize, hlow]

/-- The complete transpose program includes all mask construction and output materialization. -/
theorem scale_cost (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (scale.run st).2 ≤ (kernelConstant + 700000) * (2 ^ t + 4) ^ 7 := by
  have hp := prepare_cost w st ht he hw
  have hc := prepare_context a w st ht ha hmod he hw
  simp only [scale, run_seq_snd]
  generalize hs : (prepare.run st).1 = s at *
  have ht := tabulate_cost a w s hc
  have h4 : (2 ^ t + 4) ^ 4 ≤ (2 ^ t + 4) ^ 7 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (2 ^ t + 3) ^ 7 ≤ (2 ^ t + 4) ^ 7 := Nat.pow_le_pow_left (by omega) _
  have hp' := hp.trans (Nat.mul_le_mul_left 600000 h4)
  have ht' := ht.trans (Nat.mul_le_mul_left (kernelConstant + 40) h7)
  have hpos : 1 ≤ (2 ^ t + 4) ^ 7 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [hp', ht', hpos]

end PCP.Lang.BinaryLabelScale
