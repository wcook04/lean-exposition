/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedCodec
import PCP.Complexity.HadamardFactorLoadCost
import PCP.Complexity.LangPowerTwo

/-!
# Computing coefficient cardinalities for the actual Hadamard seed codec

All dimensions are counted from the stored increasing-mask list. Powers of two
are constructed by doubling, with their growing binary representation charged.
-/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic BinaryPolynomialSpace HadamardLabel

variable {t a : ℕ}

def subRegs : Fin 80 → Fin 100 := Fin.castLE (by decide)
def powerRegs : Fin 8 → Fin 100 := fun i => ⟨68 + i.val, by omega⟩
def powerLists : Fin 2 → Fin 32 := Fin.castLE (by decide)

theorem powerRegs_injective : Function.Injective powerRegs := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [powerRegs] at this
  omega

def masks : Stmt 100 32 := HadamardFactorLoad.masks.rename subRegs id

def power : Stmt 100 32 := PowerTwo.program.rename powerRegs powerLists

def count (a : ℕ) : Stmt 100 32 := .seq (.assign 54 (.const a))
  (.seq masks (.seq (.len 12 70) power))

theorem masks_run (st : State 100 32) (ht : st.regs 20 = t)
    (ha : st.regs 54 = a) (he : st.lists 7 = []) :
    (masks.run st).1.lists 12 = BooleanMask.masks t a := by
  have h := congrArg (fun z : State 80 32 × ℕ => z.1.lists 12)
    (HadamardFactorLoad.masks.run_rename subRegs id
      (Fin.castLE_injective _) Function.injective_id st)
  exact h.trans (HadamardFactorLoad.masks_run (st.restrict subRegs id) ht ha he)

theorem power_run (st : State 100 32) : (power.run st).1.regs 73 = 2 ^ st.regs 70 := by
  have h := PowerTwo.program_run (st.restrict powerRegs powerLists)
  have hr := PowerTwo.program.run_rename powerRegs powerLists powerRegs_injective
    (Fin.castLE_injective _) st
  rw [← hr] at h
  exact h

theorem count_run (a : ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((count a).run st).1.regs 70 = BooleanCoefficientIndex.dimension t a ∧
      ((count a).run st).1.regs 73 = cardinal t a := by
  have hm := masks_run (a := a) (setReg st 54 a) (by simpa [Function.update] using ht)
    (by simp) he
  simp only [count, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hu : (masks.run (setReg st 54 a)).1 = u at *
  simp only [run_len_fst]
  have hp := power_run (setReg u 70 (u.lists 12).length)
  have hf := run_regs_frame power 70 (by decide) (setReg u 70 (u.lists 12).length)
  simp only [setReg_regs, Function.update_self, hm, BooleanMask.masks_length] at hp hf
  simpa only [hm, BooleanMask.masks_length, cardinal] using And.intro hf hp

theorem count_frame (a : ℕ) (st : State 100 32) :
    ((count a).run st).1.regs 20 = st.regs 20 ∧
      ((count a).run st).1.lists 7 = st.lists 7 ∧
      ((count a).run st).1.lists 25 = st.lists 25 := by
  exact ⟨run_regs_frame (count a) 20 (by simp only [count, Stmt.regWrites]; decide) st,
    run_lists_frame (count a) 7 (by simp only [count, Stmt.listWrites]; decide) st,
    run_lists_frame (count a) 25 (by simp only [count, Stmt.listWrites]; decide) st⟩

theorem masks_cost (st : State 100 32) (ht : st.regs 20 = t)
    (ha : st.regs 54 = a) (he : st.lists 7 = []) :
    (masks.run st).2 ≤ 500000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  rw [masks, Stmt.run_rename_cost HadamardFactorLoad.masks subRegs id
    (show Function.Injective subRegs from Fin.castLE_injective _)
    Function.injective_id]
  exact HadamardFactorLoad.masks_cost (st.restrict subRegs id) ht ha he

theorem power_cost (st : State 100 32) :
    (power.run st).2 ≤ 20 * (st.regs 70 + 1) ^ 2 := by
  rw [power, Stmt.run_rename_cost PowerTwo.program powerRegs powerLists
    powerRegs_injective (show Function.Injective powerLists from Fin.castLE_injective _)]
  exact PowerTwo.program_cost (st.restrict powerRegs powerLists)

theorem count_cost (a : ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((count a).run st).2 ≤ 600000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  have hm := masks_run (a := a) (setReg st 54 a) (by simpa [Function.update] using ht)
    (by simp) he
  have hc := masks_cost (a := a) (setReg st 54 a) (by simpa [Function.update] using ht)
    (by simp) he
  simp only [count, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hu : (masks.run (setReg st 54 a)).1 = u at *
  have hp := power_cost (setReg u 70 (u.lists 12).length)
  simp only [setReg_regs, Function.update_self] at hp
  have hs : listSize (u.lists 12) ≤ 2 ^ t * (2 ^ t + 1) := by
    rw [hm]; exact BooleanCoefficientTransform.masks_size t a
  have hn : (u.lists 12).length ≤ 2 ^ t := by
    rw [hm]; exact BooleanCoefficientTransform.masks_length_le t a
  have hsn := (size_le_self _).trans hn
  have hsmall : (2 ^ t + Nat.size a + 3) ^ 2 ≤
      (2 ^ t + Nat.size a + 3) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left 20
    ((Nat.pow_le_pow_left (by omega : (u.lists 12).length + 1 ≤
      2 ^ t + Nat.size a + 3) 2).trans hsmall))
  simp only [run_len_snd, run_len_fst]
  change (Nat.size a + Nat.size a + 1) + ((masks.run (setReg st 54 a)).2 +
    (listSize (u.lists 12) + Nat.size (u.lists 12).length + 1 +
      (power.run (setReg u 70 (u.lists 12).length)).2 + 1) + 1) + 1 ≤ _
  nlinarith only [hc, hp', hs, hsn, hsmall,
    Nat.zero_le (Nat.size a), Nat.zero_le ((Nat.size a) ^ 2)]

end PCP.Lang.HadamardSeed
