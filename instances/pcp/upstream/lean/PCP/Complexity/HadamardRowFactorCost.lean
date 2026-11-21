/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowFactor

/-!
# Charged cost of the two Hadamard factor queries

The uniform bound accommodates every factor degree below the row degree. In
production the row degree is one or three; no loop uses a numeric coefficient code.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r a : ℕ}

def factorSize (t r : ℕ) : ℕ := 2 ^ t + 3 * r + 5

theorem productPart_cost (h : 1 + a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (productPart.run st).2 ≤ baseStepConstant * factorSize t r ^ 8 := by
  let u := setReg (setReg (setList st 13 (st.lists 22)) 54 1) 55 (st.regs 60)
  have hprod := HadamardLabel.product_cost s.linear p u
    (by simpa [u, Function.update] using hc.1) (by simp [u, Function.update])
    (by simpa [u] using ha) (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1) (by simpa [u, Function.update] using hp)
  have hl := HadamardLabel.product_run h s.linear p u
    (by simpa [u, Function.update] using hc.1) (by simp [u, Function.update])
    (by simpa [u] using ha) (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1) (by simpa [u, Function.update] using hp)
  have hu7 := run_lists_frame HadamardLabel.product 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.product 20 (by decide) u
  dsimp only [u] at hprod hl hu7 hu20
  simp only [productPart, productPrepare, run_seq_snd, run_seq_fst, run_copy_snd, run_copy_fst,
    run_assign_fst, Expr.eval, setReg_regs, setList_regs,
    Function.update_of_ne (by decide : (60 : Fin 80) ≠ 54)]
  generalize hv : (HadamardLabel.product.run
    (setReg (setReg (setList st 13 (st.lists 22)) 54 1) 55 (st.regs 60))).1 = v at *
  have hsum := emitSum_cost 5 20 (by decide)
    (BooleanCoefficientArithmetic.mixedProduct h s.linear p) s.base v hl
    (by simpa [Function.update] using hu20.trans hc.2.2.2.1)
    (by simpa [Function.update] using hu7.trans hc.2.2.1)
  change ((listSize (st.lists 22) + 1) + ((Expr.const 1).cost _ +
    (Expr.var 60).cost (setReg (setList st 13 (st.lists 22)) 54 1).regs + 1) + 1) +
      ((HadamardLabel.product.run
        (setReg (setReg (setList st 13 (st.lists 22)) 54 1) 55 (st.regs 60))).2 +
        ((emitSum 5 20).run v).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_one, setReg_regs,
    setList_regs, Function.update_of_ne (by decide : (60 : Fin 80) ≠ 54)]
  have hsource : listSize (st.lists 22) ≤ 2 * 2 ^ t := by
    rw [hc.2.2.2.2.2.1]; exact HadamardLabel.encode_size s.linear
  have hdegree : Nat.size (st.regs 60) ≤ r := by rw [ha]; exact (size_le_self _).trans (by omega)
  have hsa : Nat.size a ≤ r := (size_le_self _).trans (by omega)
  have hsr : Nat.size r ≤ r := size_le_self _
  have h8 : (2 ^ t + Nat.size 1 + Nat.size a + Nat.size r + 3) ^ 8 ≤ factorSize t r ^ 8 :=
    Nat.pow_le_pow_left (by simp only [Nat.size_one, factorSize]; omega) _
  have h2 : (2 ^ t + 1) ^ 2 ≤ factorSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by change 2 ^ t + 1 ≤ 2 ^ t + 3 * r + 5; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hp' := hprod.trans (Nat.mul_le_mul_left _ h8)
  have hs' := hsum.trans (Nat.mul_le_mul_left _ h2)
  have hlow : 2 ^ t + r + 5 ≤ factorSize t r ^ 8 :=
    (by unfold factorSize; omega : 2 ^ t + r + 5 ≤ factorSize t r).trans (Nat.le_pow (by decide))
  unfold baseStepConstant
  nlinarith only [hp', hs', hsource, hdegree, hlow, Nat.zero_le WordCodec.passConstant]

theorem factorPart_cost (h : a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (factorPart.run st).2 ≤ baseStepConstant * factorSize t r ^ 8 := by
  let u := setReg (setList st 13 (st.lists 18)) 54 (st.regs 60)
  have hembed := HadamardLabel.embed_cost p u
    (by simpa [u, Function.update] using hc.1) (by simpa [u] using ha)
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1) (by simpa [u] using hp)
  have hl := HadamardLabel.embed_run h p u
    (by simpa [u, Function.update] using hc.1) (by simpa [u] using ha)
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1) (by simpa [u] using hp)
  have hu7 := run_lists_frame HadamardLabel.embed 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.embed 20 (by decide) u
  dsimp only [u] at hembed hl hu7 hu20
  simp only [factorPart, factorPrepare, run_seq_snd, run_seq_fst, run_copy_snd, run_copy_fst,
    run_assign_fst, Expr.eval, setList_regs]
  generalize hv : (HadamardLabel.embed.run
    (setReg (setList st 13 (st.lists 18)) 54 (st.regs 60))).1 = v at *
  have hsum := emitSum_cost 5 20 (by decide)
    (BooleanCoefficientArithmetic.embed h p) s.base v hl
    (by simpa [Function.update] using hu20.trans hc.2.2.2.1)
    (by simpa [Function.update] using hu7.trans hc.2.2.1)
  change ((listSize (st.lists 18) + 1) + (Expr.var 60).cost st.regs + 1) +
    ((HadamardLabel.embed.run (setReg (setList st 13 (st.lists 18)) 54 (st.regs 60))).2 +
      ((emitSum 5 20).run v).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  have hsource : listSize (st.lists 18) ≤ 2 * 2 ^ t := by rw [hp]; exact HadamardLabel.encode_size p
  have hdegree : Nat.size (st.regs 60) ≤ r := by rw [ha]; exact (size_le_self _).trans h
  have hsa : Nat.size a ≤ r := (size_le_self _).trans h
  have hsr : Nat.size r ≤ r := size_le_self _
  have h8 : (2 ^ t + Nat.size a + Nat.size a + Nat.size r + 3) ^ 8 ≤ factorSize t r ^ 8 :=
    Nat.pow_le_pow_left (by unfold factorSize; omega) _
  have h2 : (2 ^ t + 1) ^ 2 ≤ factorSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by change 2 ^ t + 1 ≤ 2 ^ t + 3 * r + 5; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have he' := hembed.trans (Nat.mul_le_mul_left _ h8)
  have hs' := hsum.trans (Nat.mul_le_mul_left _ h2)
  have hlow : 2 ^ t + r + 5 ≤ factorSize t r ^ 8 :=
    (by unfold factorSize; omega : 2 ^ t + r + 5 ≤ factorSize t r).trans (Nat.le_pow (by decide))
  unfold baseStepConstant
  nlinarith only [he', hs', hsource, hdegree, hlow, Nat.zero_le WordCodec.passConstant]

theorem pair_cost (h : 1 + a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (pair.run st).2 ≤ (2 * baseStepConstant + 1) * factorSize t r ^ 8 := by
  have hprod := productPart_cost h s p st hc ha hp
  have hctx := context_frame productPart productPart_stable s st hc
  have hsource := productPart_source st
  simp only [pair, run_seq_snd]
  generalize hs : (productPart.run st).1 = u at *
  have hfactor := factorPart_cost (by omega : a ≤ r) s p u hctx
    (hsource.2.trans ha) (hsource.1.trans hp)
  have hpos : 1 ≤ factorSize t r ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hprod, hfactor, hpos]

end PCP.Lang.HadamardRow
