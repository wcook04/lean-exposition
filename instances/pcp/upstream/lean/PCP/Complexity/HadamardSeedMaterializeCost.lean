/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedMaterialize
import PCP.Complexity.HadamardRowLoopCost

/-! # Charged costs of turning decoded seed cells into stored row words -/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList HadamardLabel

variable {t r a : ℕ}

theorem factors_cost (fs cs : List ℕ) (st : State 100 32)
    (hc : st.lists 25 = fs ++ cs) :
    ((factors fs.length).run st).2 ≤ 4 * listSize fs + 1 := by
  induction fs generalizing st with
  | nil => simp [factors, Stmt.run, listSize]
  | cons f fs ih =>
      have hf : (factorStep.run st).1.lists 25 = fs ++ cs := by
        simp [factorStep, Stmt.run, Function.update, hc]
      have hcost : (factorStep.run st).2 = Nat.size f + 1 + (Nat.size f + 1) + 1 := by
        simp [factorStep, Stmt.run, Function.update, hc]
      have h := ih (factorStep.run st).1 hf
      simp only [List.length_cons, factors, run_seq_snd, hcost,
        listSize, List.map_cons, List.sum_cons] at h ⊢
      omega

theorem splitFactors_cost (s : Hadamard.TestRandomness t r) (cs : List ℕ)
    (st : State 100 32) (he : st.lists 7 = [])
    (hc : st.lists 25 = HadamardRow.factorCodes s ++ cs) :
    ((splitFactors r).run st).2 ≤ 5 * (r - 1) * (2 ^ t + 1) + 5 := by
  let u := setList st 23 []
  have hu : u.lists 25 = HadamardRow.factorCodes s ++ cs := by
    simpa [u, Function.update] using hc
  have hf := factors_cost (HadamardRow.factorCodes s) cs u hu
  have ho := (factors_run (HadamardRow.factorCodes s) cs u hu).2
  have hn : (HadamardRow.factorCodes s).length = r - 1 := by
    simp [HadamardRow.factorCodes]
  rw [hn] at hf ho
  have hs := HadamardRow.factorCodes_size s
  have hsize : listSize (((factors (r - 1)).run u).1.lists 23) =
      listSize (HadamardRow.factorCodes s) := by
    rw [ho, show u.lists 23 = [] from rfl, List.append_nil, listSize_reverse]
  simp only [splitFactors, run_seq_snd, run_copy_snd, run_copy_fst, he, run_rev_snd]
  change 1 + (((factors (r - 1)).run u).2 +
    (listSize (((factors (r - 1)).run u).1.lists 23) + 1) + 1) + 1 ≤ _
  rw [hsize]
  nlinarith only [hf, hs]

theorem load_cost (p : Coefficients t a) (cs : List ℕ) (st : State 100 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    (load.run st).2 ≤ 700000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  rw [load, Stmt.run_rename_cost HadamardFactorLoad.load subRegs id
    (show Function.Injective subRegs from Fin.castLE_injective _)
    Function.injective_id]
  exact HadamardFactorLoad.load_cost p cs (st.restrict subRegs id) ht ha he hp

theorem loadTo_cost (p : Coefficients t a) (cs : List ℕ) (dst : Fin 32)
    (st : State 100 32) (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    ((loadTo a dst).run st).2 ≤ 710000 * (2 ^ t + Nat.size a + 3) ^ 4 := by
  have ht' : (setReg st 60 a).regs 20 = t := by simpa [Function.update] using ht
  have hc := load_cost p cs (setReg st 60 a) ht' (by simp) he hp
  have ho := (load_run p cs (setReg st 60 a) ht' (by simp) he hp).1
  have hs := encode_size p
  have hlow : 2 ^ t + Nat.size a + 3 ≤ (2 ^ t + Nat.size a + 3) ^ 4 :=
    Nat.le_pow (by decide)
  simp only [loadTo, run_seq_snd, run_assign_fst, Expr.eval, run_copy_snd, ho]
  change (Nat.size a + Nat.size a + 1) +
    ((load.run (setReg st 60 a)).2 + (listSize (encode p) + 1) + 1) + 1 ≤ _
  nlinarith only [hc, hs, hlow]

theorem words_cost (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.lists 25 = [code s.linear, code s.auxiliary, code s.base]) :
    ((words r).run st).2 ≤ 2200000 * (2 ^ t + r + 4) ^ 4 := by
  have h1 := loadTo_run s.linear _ 22 (by decide) (by decide) st ht he hc
  have c1 := loadTo_cost s.linear _ 22 st ht he hc
  simp only [words, run_seq_snd]
  generalize hu : ((loadTo 1 22).run st).1 = u at *
  have h2 := loadTo_run s.auxiliary _ 21 (by decide) (by decide) u h1.2.1 h1.2.2.2 h1.2.2.1
  have c2 := loadTo_cost s.auxiliary _ 21 u h1.2.1 h1.2.2.2 h1.2.2.1
  generalize hv : ((loadTo r 21).run u).1 = v at *
  have c3 := loadTo_cost s.base [] 20 v h2.2.1 h2.2.2.2 h2.2.2.1
  have b1 : (2 ^ t + Nat.size 1 + 3) ^ 4 ≤ (2 ^ t + r + 4) ^ 4 :=
    Nat.pow_le_pow_left (by change 2 ^ t + 1 + 3 ≤ _; omega) _
  have br : (2 ^ t + Nat.size r + 3) ^ 4 ≤ (2 ^ t + r + 4) ^ 4 :=
    Nat.pow_le_pow_left (by have := size_le_self r; omega) _
  have c1' := c1.trans (Nat.mul_le_mul_left _ b1)
  have c2' := c2.trans (Nat.mul_le_mul_left _ br)
  have c3' := c3.trans (Nat.mul_le_mul_left _ br)
  have hlow : 2 ^ t + r + 4 ≤ (2 ^ t + r + 4) ^ 4 := Nat.le_pow (by decide)
  change (loadTo 1 22 |>.run st).2 + ((loadTo r 21 |>.run u).2 +
    ((loadTo r 20 |>.run v).2 + (Nat.size r + Nat.size r + 1) + 1) + 1) + 1 ≤ _
  have hs := size_le_self r
  nlinarith only [c1', c2', c3', hlow, hs, Nat.zero_le (2 ^ t), Nat.zero_le r]

theorem materialize_cost (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.lists 25 = HadamardRow.factorCodes s ++
      [code s.linear, code s.auxiliary, code s.base]) :
    ((materialize r).run st).2 ≤ 2300000 * (2 ^ t + r + 4) ^ 4 := by
  have hs := splitFactors_cost s _ st he hc
  have ho := splitFactors_run s _ st ht he hc
  simp only [materialize, run_seq_snd]
  generalize hu : ((splitFactors r).run st).1 = u at *
  have hw := words_cost s u ho.2.2.1 ho.2.2.2 ho.2.1
  have hb : r - 1 ≤ r := Nat.sub_le _ _
  have hprod := Nat.mul_le_mul_right (2 ^ t + 1) (Nat.mul_le_mul_left 5 hb)
  have hp : (2 ^ t + r + 4) ^ 2 ≤ (2 ^ t + r + 4) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  nlinarith only [hs, hw, hprod, hp, Nat.zero_le (2 ^ t), Nat.zero_le r,
    Nat.zero_le ((2 ^ t) ^ 2), Nat.zero_le (r ^ 2)]

end PCP.Lang.HadamardSeed
