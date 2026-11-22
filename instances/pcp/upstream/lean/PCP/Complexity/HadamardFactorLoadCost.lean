/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardFactorLoad

/-!
# Charged cost of degree-dependent factor materialization

The numeric factor code is charged by its coefficient-word bit length. The
program never performs a loop bounded by that potentially huge numeric code.
-/

namespace PCP.Lang.HadamardFactorLoad

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList HadamardLabel

variable {t a : ℕ}

theorem masks_cost (st : State 80 32) (ht : st.regs 20 = t)
    (ha : st.regs 54 = a) (he : st.lists 7 = []) :
    (masks.run st).2 ≤ 500000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  rw [masks, Stmt.run_rename_cost (BooleanLabelTransform.masks false) transformRegs transformLists
    (show Function.Injective transformRegs from Fin.castLE_injective _)
    (show Function.Injective transformLists from Fin.castLE_injective _)]
  exact BooleanLabelTransform.masks_cost false (st.restrict transformRegs transformLists) ht ha he

theorem materialize_cost (p : Coefficients t a) (st : State 80 32)
    (hn : st.regs 20 = BooleanCoefficientIndex.dimension t a)
    (hp : st.regs 33 = code p) (he : st.lists 7 = []) :
    (materialize.run st).2 ≤ 400 * (2 ^ t + 1) ^ 2 := by
  rw [materialize, Stmt.run_rename_cost BinaryPolynomialSelector.materialize
    materializeRegs materializeLists
    (show Function.Injective materializeRegs from Fin.castLE_injective _)
    materializeLists_injective]
  have hc := BinaryPolynomialSelector.materialize_cost
    (st.restrict materializeRegs materializeLists) he
  change _ ≤ 100 * (st.regs 20 + Nat.size (st.regs 33) + 1) ^ 2 at hc
  rw [hn, hp] at hc
  have hcode := code_size p
  have hd := BooleanCoefficientTransform.masks_length_le t a
  rw [BooleanMask.masks_length] at hd
  calc
    _ ≤ 100 * (2 * (2 ^ t + 1)) ^ 2 :=
      hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = _ := by ring

theorem saveAndPop_cost (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (hp : st.lists 25 = code p :: cs) :
    (saveAndPop.run st).2 ≤ 5 * (2 ^ t + Nat.size a + 3) := by
  have htSize : Nat.size t ≤ 2 ^ t := (size_le_self _).trans (Nat.lt_two_pow_self (n := t)).le
  have hcode := code_size p
  simp only [saveAndPop, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hp,
    setReg_lists, setReg_regs, setList_regs, Function.update, Fin.reduceEq,
    dite_false, ht, ha]
  omega

theorem setup_cost (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    (setup.run st).2 ≤ 600000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  have hc := saveAndPop_cost p cs st ht ha hp
  have hs := saveAndPop_run st (code p) cs hp
  have hs20 := run_regs_frame saveAndPop 20 (by decide) st
  have hs7 := run_lists_frame saveAndPop 7 (by decide) st
  simp only [setup, run_seq_snd]
  generalize hu : (saveAndPop.run st).1 = u at *
  have hm := masks_cost u (hs20.trans ht) (hs.2.2.1.trans ha) (hs7.trans he)
  have hlow : 2 ^ t + Nat.size a + 3 ≤ (2 ^ t + Nat.size a + 3) ^ 4 :=
    Nat.le_pow (by decide)
  have hpos : 1 ≤ (2 ^ t + Nat.size a + 3) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hc, hm, hlow, hpos]

theorem loadTail_cost (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (hp : Prepared p cs st) :
    (loadTail.run st).2 ≤ 500 * (2 ^ t + 1) ^ 2 := by
  let u := setReg (setReg st 20 (st.lists 12).length) 33 (st.regs 64)
  have hn : u.regs 20 = BooleanCoefficientIndex.dimension t a := by
    simp [u, Function.update, hp.2.2.1]
  have hcode : u.regs 33 = code p := by simpa [u] using hp.2.1
  have hc := materialize_cost p u hn hcode hp.2.2.2.2
  have hu57 := run_regs_frame materialize 57 (by decide) u
  dsimp only [u] at hc hu57
  simp only [loadTail, run_seq_snd, run_len_snd, run_len_fst, run_assign_fst,
    Expr.eval, setReg_regs, Function.update_of_ne (by decide : (64 : Fin 80) ≠ 20)]
  generalize hv : (materialize.run
    (setReg (setReg st 20 (st.lists 12).length) 33 (st.regs 64))).1 = v at *
  change (listSize (st.lists 12) + Nat.size (st.lists 12).length + 1) +
    ((Expr.var 64).cost (setReg st 20 (st.lists 12).length).regs +
      ((materialize.run (setReg (setReg st 20 (st.lists 12).length) 33 (st.regs 64))).2 +
        (Expr.var 57).cost v.regs + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hu57, hp.1]
  have hsize : Nat.size (st.regs 64) ≤ 2 ^ t := by rw [hp.2.1]; exact code_size p
  have hlist : listSize (st.lists 12) ≤ 2 ^ t * (2 ^ t + 1) := by
    rw [hp.2.2.1]; exact BooleanCoefficientTransform.masks_size t a
  have hlen : Nat.size (st.lists 12).length ≤ 2 ^ t := by
    rw [hp.2.2.1]
    exact (size_le_self _).trans (BooleanCoefficientTransform.masks_length_le t a)
  have htSize : Nat.size t ≤ 2 ^ t := (size_le_self _).trans (Nat.lt_two_pow_self (n := t)).le
  nlinarith only [hc, hsize, hlist, hlen, htSize, Nat.zero_le ((2 ^ t) ^ 2)]

/-- All mask enumeration, cursor extraction, serialization and width restoration are charged. -/
theorem load_cost (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    (load.run st).2 ≤ 700000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  have hs := setup_cost p cs st ht ha he hp
  have hc := setup_run p cs st ht ha he hp
  simp only [load, run_seq_snd]
  generalize hu : (setup.run st).1 = u at *
  have ht := loadTail_cost p cs u hc
  have h2 : (2 ^ t + 1) ^ 2 ≤ (2 ^ t + Nat.size a + 3) ^ 4 :=
    (Nat.pow_le_pow_left (by omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have ht' := ht.trans (Nat.mul_le_mul_left _ h2)
  have hpos : 1 ≤ (2 ^ t + Nat.size a + 3) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hs, ht', hpos]

end PCP.Lang.HadamardFactorLoad
