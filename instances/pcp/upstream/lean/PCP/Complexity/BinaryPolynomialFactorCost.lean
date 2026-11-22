/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialFactorLang

/-!
# Charged cost of finite polynomial factor checks
-/

namespace PCP.Lang.BinaryPolynomialFactor

open BinaryPolynomialCoefficient

theorem convolution24_cost (st : State 24 2) (t : ℕ)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9)
    (hn : st.regs 12 ≤ t) :
    (convolution24.run st).2 ≤ 210000 * (2 ^ t + 1) ^ 3 := by
  rw [convolution24, Stmt.run_rename_cost convolutionProgram convolutionEmbedding id
    (show Function.Injective convolutionEmbedding from Fin.castLE_injective _)
    Function.injective_id]
  exact convolution_cost _ t hd he hj hk hn

theorem coefficient24_cost (st : State 24 2) (hcode : st.regs 1 < 2 ^ st.regs 0) :
    (coefficient24.run st).2 ≤ 30 * (2 ^ st.regs 0 + Nat.size (st.regs 2) + 1) ^ 2 := by
  rw [coefficient24, Stmt.run_rename_cost coefficient coefficientEmbedding id
    (show Function.Injective coefficientEmbedding from Fin.castLE_injective _)
    Function.injective_id]
  exact coefficient_cost _ hcode

theorem productCoefficient_cost (st : State 24 2) (t : ℕ)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9)
    (hn : st.regs 23 ≤ t) :
    (productCoefficient.run st).2 ≤ 220000 * (2 ^ t + 1) ^ 3 := by
  let s := setReg st 12 (st.regs 23)
  have hc := convolution24_cost s t (by simpa [s, Function.update] using hd)
    (by simpa [s, Function.update] using he) (by simpa [s, Function.update] using hj)
    (by simpa [s, Function.update] using hk) (by simpa [s] using hn)
  have ho : Nat.size ((convolution24.run s).1.regs 13) ≤ 1 := by
    rw [convolution24_run]
    exact size_le_one_of_le_one (by
      have h : convolution (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) (s.regs 12) < 2 :=
        Nat.mod_lt _ (by decide)
      omega)
  have hs : Nat.size (st.regs 23) ≤ 2 ^ t :=
    (size_le_self _).trans (hn.trans (Nat.lt_two_pow_self (n := t)).le)
  simp only [productCoefficient, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 23).cost st.regs + ((convolution24.run s).2 +
    (Expr.var 13).cost (convolution24.run s).1.regs + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  nlinarith [Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

theorem candidateCoefficient_cost (st : State 24 2) (t : ℕ) (ht : st.regs 20 = t)
    (hcode : st.regs 21 < 2 ^ t) (hn : st.regs 23 ≤ t) :
    (candidateCoefficient.run st).2 ≤ 200 * (2 ^ t + 1) ^ 2 := by
  let s := setReg (setReg (setReg st 0 t) 1 (st.regs 21)) 2 (st.regs 23)
  have hs0 : s.regs 0 = t := by simp [s, Function.update]
  have hs1 : s.regs 1 = st.regs 21 := by simp [s, Function.update]
  have hs2 : s.regs 2 = st.regs 23 := by simp [s]
  have hc := coefficient24_cost s (by simpa only [hs0, hs1] using hcode)
  rw [hs0, hs2] at hc
  have htQ : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have hsT : Nat.size t ≤ 2 ^ t := (size_le_self _).trans htQ
  have hsCode : Nat.size (st.regs 21) ≤ 2 ^ t := (size_le_self _).trans hcode.le
  have hsIndex : Nat.size (st.regs 23) ≤ 2 ^ t := (size_le_self _).trans (hn.trans htQ)
  have hc' : (coefficient24.run s).2 ≤ 30 * (2 * 2 ^ t + 1) ^ 2 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  simp only [candidateCoefficient, run_seq_snd, run_assign_fst, Expr.eval, ht]
  change (Expr.var 20).cost st.regs + ((Expr.var 21).cost (setReg st 0 t).regs +
    ((Expr.var 23).cost (setReg (setReg st 0 t) 1 (st.regs 21)).regs +
      (coefficient24.run s).2 + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, ht]
  nlinarith

theorem compareTail_cost (st : State 24 2) (t : ℕ)
    (h3 : st.regs 3 < 2) (h19 : st.regs 19 < 2) (h22 : st.regs 22 < 2)
    (h23 : st.regs 23 ≤ t) (h15 : st.regs 15 = 1) :
    (compareTail.run st).2 ≤ 1974 * (t + 2) := by
  have hc := loopFree_cost_le compareTail (by decide) st (t + 1)
    (by
      intro r hr
      have hu : compareTail.uses = [3, 19, 22, 23, 15] := by rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (size_le_one_of_le_one (by omega : st.regs 3 ≤ 1)).trans (by omega)
      · exact (size_le_one_of_le_one (by omega : st.regs 19 ≤ 1)).trans (by omega)
      · exact (size_le_one_of_le_one (by omega : st.regs 22 ≤ 1)).trans (by omega)
      · exact (size_le_self _).trans (h23.trans (by omega))
      · rw [h15]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega))
    (by simp [compareTail, Stmt.lUses])
  have hC : compareTail.C * (compareTail.width + compareTail.csize + 1) = 1974 := by decide
  rw [hC] at hc
  simpa only [Nat.add_assoc] using hc

theorem matchBody_cost (st : State 24 2) (t : ℕ)
    (ht : st.regs 20 = t) (hcode : st.regs 21 < 2 ^ t)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9)
    (hn : st.regs 23 ≤ t) (ha : st.regs 22 < 2) :
    (matchBody.run st).2 ≤ 230000 * (2 ^ t + 1) ^ 3 := by
  have hp := productCoefficient_cost st t hd he hj hk hn
  have hs20 := run_regs_frame productCoefficient 20 (by decide) st
  have hs21 := run_regs_frame productCoefficient 21 (by decide) st
  have hs22 := run_regs_frame productCoefficient 22 (by decide) st
  have hs23 := run_regs_frame productCoefficient 23 (by decide) st
  have hs19 := productCoefficient_run st
  have hs15 := productCoefficient_sets_one st
  simp only [matchBody, run_seq_snd]
  generalize hs : (productCoefficient.run st).1 = s at *
  have hc := candidateCoefficient_cost s t (hs20.trans ht) (by simpa only [hs21] using hcode)
    (by simpa only [hs23] using hn)
  have hu3 := candidateCoefficient_run s
  have hu19 := run_regs_frame candidateCoefficient 19 (by decide) s
  have hu15 := run_regs_frame candidateCoefficient 15 (by decide) s
  have hu22 := run_regs_frame candidateCoefficient 22 (by decide) s
  have hu23 := run_regs_frame candidateCoefficient 23 (by decide) s
  generalize hu : (candidateCoefficient.run s).1 = u at *
  have htail := compareTail_cost u t (by rw [hu3]; exact value_lt_two _ _ _)
    (by rw [hu19, hs19]; exact Nat.mod_lt _ (by decide))
    (by simpa only [hu22, hs22] using ha) (by simpa only [hu23, hs23] using hn)
    (hu15.trans hs15)
  have htQ : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  nlinarith [Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

/-- The complete factor-product check has quartic charged cost in candidate-space size. -/
theorem matchProduct_cost (st : State 24 2) (t : ℕ)
    (ht : st.regs 20 = t) (hcode : st.regs 21 < 2 ^ t)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9) :
    (matchProduct.run st).2 ≤ 240000 * (2 ^ t + 1) ^ 4 := by
  let s := setReg (setReg (setReg (setReg st 22 1) 23 0) 15 1) 7 (t + 1)
  have hinit : MatchInv t (st.regs 21) (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) 0 s :=
    by simp [MatchInv, MatchesPrefix, s, ht, Function.update]
  have hit := iterate_cost_idx matchBody.run (Nat.size (t + 1) + 1)
    (230000 * (2 ^ t + 1) ^ 3) (t + 1)
    (MatchInv t (st.regs 21) (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11))
    (by
      intro n u hn hu
      refine ⟨matchBody_inv _ _ _ _ _ _ n u hu, ?_⟩
      obtain ⟨h8, h9, h10, h11, h20, h21, h23, h22⟩ := hu
      apply matchBody_cost u t h20
      · simpa only [h21] using hcode
      · simpa only [h8] using hd
      · simpa only [h9] using he
      · simpa only [h10, h8] using hj
      · simpa only [h11, h9] using hk
      · rw [h23]; omega
      · rw [h22]; split_ifs <;> decide) s hinit
  let Q := 2 ^ t
  have htQ : t ≤ Q := (Nat.lt_two_pow_self (n := t)).le
  have hsz : Nat.size t ≤ Q := (size_le_self _).trans htQ
  have hsz1 : Nat.size (t + 1) ≤ Q + 1 := (size_le_self _).trans (by omega)
  have hbig : (t + 1) * (Nat.size (t + 1) + 1 + 230000 * (Q + 1) ^ 3) ≤
      (Q + 1) * (Q + 2 + 230000 * (Q + 1) ^ 3) := Nat.mul_le_mul (by omega) (by omega)
  simp only [matchProduct, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, ht]
  change (Expr.const 1).cost st.regs + ((Expr.const 0).cost _ + ((Expr.const 1).cost _ +
    ((Expr.add 20 15).cost (setReg (setReg (setReg st 22 1) 23 0) 15 1).regs +
      ((iterate matchBody.run (Nat.size (t + 1) + 1) (t + 1) s).2 +
        Nat.size (t + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, dite_true, Nat.size_zero, show Nat.size 1 = 1 from rfl, ht]
  change _ ≤ 240000 * (Q + 1) ^ 4
  have hsum := hit.trans hbig
  nlinarith [Nat.zero_le (Q ^ 4), Nat.zero_le (Q ^ 3), Nat.zero_le (Q ^ 2)]

end PCP.Lang.BinaryPolynomialFactor
