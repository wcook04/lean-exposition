/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialCoefficientLang

/-!
# Charged bounds for the numeric coefficient convolution

The polynomial-search arithmetic is bounded in the candidate-space size `2^t`.
These coarse bounds are sufficient for the production fields, whose cardinality
has already been bounded polynomially in the encoded graph input length.
-/

namespace PCP.Lang.BinaryPolynomialCoefficient

theorem value_lt_two (d code k : ℕ) : value d code k < 2 := by
  unfold value
  split_ifs
  · exact Nat.mod_lt _ (by decide)
  · decide
  · decide

theorem coefficient20_cost (st : State 20 2) (hcode : st.regs 1 < 2 ^ st.regs 0) :
    (coefficient20.run st).2 ≤ 30 * (2 ^ st.regs 0 + Nat.size (st.regs 2) + 1) ^ 2 := by
  rw [coefficient20, Stmt.run_rename_cost _ _ _ regEmbedding_injective Function.injective_id]
  exact coefficient_cost _ hcode

theorem leftCoefficient_cost (st : State 20 2) (t : ℕ) (hd : st.regs 8 ≤ t)
    (hcode : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 14 ≤ t) :
    (leftCoefficient.run st).2 ≤ 200 * (2 ^ t + 1) ^ 2 := by
  let Q := 2 ^ t
  let s := setReg (setReg (setReg st 0 (st.regs 8)) 1 (st.regs 10)) 2 (st.regs 14)
  have hs0 : s.regs 0 = st.regs 8 := by simp [s, Function.update]
  have hs1 : s.regs 1 = st.regs 10 := by simp [s, Function.update]
  have hs2 : s.regs 2 = st.regs 14 := by simp [s]
  have hc := coefficient20_cost s (by simpa only [hs0, hs1] using hcode)
  rw [hs0, hs2] at hc
  have ho := coefficient20_run s
  have hsmall : Nat.size ((coefficient20.run s).1.regs 3) ≤ 1 := by
    rw [ho]
    exact size_le_one_of_le_one (by have := value_lt_two (s.regs 0) (s.regs 1) (s.regs 2); omega)
  have htQ : t ≤ Q := (Nat.lt_two_pow_self (n := t)).le
  have hdQ : 2 ^ st.regs 8 ≤ Q := Nat.pow_le_pow_right (by decide) hd
  have hsDegree : Nat.size (st.regs 8) ≤ Q := (size_le_self _).trans (hd.trans htQ)
  have hsCode : Nat.size (st.regs 10) ≤ Q := (size_le_self _).trans (hcode.le.trans hdQ)
  have hsIndex : Nat.size (st.regs 14) ≤ Q := (size_le_self _).trans (hk.trans htQ)
  have hc' : (coefficient20.run s).2 ≤ 30 * (2 * Q + 1) ^ 2 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  simp only [leftCoefficient, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 8).cost st.regs + ((Expr.var 10).cost (setReg st 0 (st.regs 8)).regs +
    ((Expr.var 14).cost (setReg (setReg st 0 (st.regs 8)) 1 (st.regs 10)).regs +
      ((coefficient20.run s).2 + (Expr.var 3).cost (coefficient20.run s).1.regs + 1) + 1) + 1) +
    1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false]
  change _ ≤ 200 * (Q + 1) ^ 2
  nlinarith

theorem rightCoefficient_cost (st : State 20 2) (t : ℕ) (hd : st.regs 9 ≤ t)
    (hcode : st.regs 11 < 2 ^ st.regs 9) (hn : st.regs 12 ≤ t)
    (hi : st.regs 14 ≤ t) :
    (rightCoefficient.run st).2 ≤ 200 * (2 ^ t + 1) ^ 2 := by
  let Q := 2 ^ t
  let s := setReg (setReg (setReg st 0 (st.regs 9)) 1 (st.regs 11)) 2 (st.regs 12 - st.regs 14)
  have hs0 : s.regs 0 = st.regs 9 := by simp [s, Function.update]
  have hs1 : s.regs 1 = st.regs 11 := by simp [s, Function.update]
  have hs2 : s.regs 2 = st.regs 12 - st.regs 14 := by simp [s]
  have hc := coefficient20_cost s (by simpa only [hs0, hs1] using hcode)
  rw [hs0, hs2] at hc
  have htQ : t ≤ Q := (Nat.lt_two_pow_self (n := t)).le
  have hdQ : 2 ^ st.regs 9 ≤ Q := Nat.pow_le_pow_right (by decide) hd
  have hsDegree : Nat.size (st.regs 9) ≤ Q := (size_le_self _).trans (hd.trans htQ)
  have hsCode : Nat.size (st.regs 11) ≤ Q := (size_le_self _).trans (hcode.le.trans hdQ)
  have hsN : Nat.size (st.regs 12) ≤ Q := (size_le_self _).trans (hn.trans htQ)
  have hsI : Nat.size (st.regs 14) ≤ Q := (size_le_self _).trans (hi.trans htQ)
  have hsIndex : Nat.size (st.regs 12 - st.regs 14) ≤ Q :=
    (size_le_self _).trans ((Nat.sub_le _ _).trans (hn.trans htQ))
  have hc' : (coefficient20.run s).2 ≤ 30 * (2 * Q + 1) ^ 2 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  simp only [rightCoefficient, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 9).cost st.regs + ((Expr.var 11).cost (setReg st 0 (st.regs 9)).regs +
    ((Expr.sub 12 14).cost (setReg (setReg st 0 (st.regs 9)) 1 (st.regs 11)).regs +
      (coefficient20.run s).2 + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false]
  change _ ≤ 200 * (Q + 1) ^ 2
  nlinarith

theorem convolutionTail_cost (st : State 20 2) (t : ℕ)
    (h3 : st.regs 3 < 2) (h17 : st.regs 17 < 2) (h13 : st.regs 13 < 2)
    (h14 : st.regs 14 ≤ t) (h15 : st.regs 15 = 1) (h16 : st.regs 16 = 2) :
    (convolutionTail.run st).2 ≤ 36876 * (t + 3) := by
  have hc := loopFree_cost_le convolutionTail (by decide) st (t + 2)
    (by
      intro r hr
      have hu : convolutionTail.uses = [17, 3, 13, 16, 14, 15] := by rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (size_le_one_of_le_one (by omega : st.regs 17 ≤ 1)).trans (by omega)
      · exact (size_le_one_of_le_one (by omega : st.regs 3 ≤ 1)).trans (by omega)
      · exact (size_le_one_of_le_one (by omega : st.regs 13 ≤ 1)).trans (by omega)
      · rw [h16]; exact (show Nat.size 2 = 2 by decide).le.trans (by omega)
      · exact (size_le_self _).trans (h14.trans (by omega))
      · rw [h15]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega))
    (by simp [convolutionTail, Stmt.lUses])
  have hC : convolutionTail.C * (convolutionTail.width + convolutionTail.csize + 1) = 36876 :=
    by decide
  rw [hC] at hc
  simpa only [Nat.add_assoc] using hc

theorem convolutionBody_cost (st : State 20 2) (t : ℕ)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9)
    (hn : st.regs 12 ≤ t) (hi : st.regs 14 ≤ t) (ha : st.regs 13 < 2)
    (h1 : st.regs 15 = 1) (h2 : st.regs 16 = 2) :
    (convolutionBody.run st).2 ≤ 200000 * (2 ^ t + 1) ^ 2 := by
  let s := (leftCoefficient.run st).1
  let u := (rightCoefficient.run s).1
  have hs9 : s.regs 9 = st.regs 9 := run_regs_frame leftCoefficient 9 (by decide) st
  have hs11 : s.regs 11 = st.regs 11 := run_regs_frame leftCoefficient 11 (by decide) st
  have hs12 : s.regs 12 = st.regs 12 := run_regs_frame leftCoefficient 12 (by decide) st
  have hs14 : s.regs 14 = st.regs 14 := run_regs_frame leftCoefficient 14 (by decide) st
  have hl := leftCoefficient_cost st t hd hj hi
  have hr := rightCoefficient_cost s t (by simpa only [hs9] using he)
    (by simpa only [hs11, hs9] using hk) (by simpa only [hs12] using hn)
    (by simpa only [hs14] using hi)
  have hu3 : u.regs 3 < 2 := by rw [rightCoefficient_run]; exact value_lt_two _ _ _
  have hu17 : u.regs 17 < 2 := by
    rw [run_regs_frame rightCoefficient 17 (by decide), leftCoefficient_run]
    exact value_lt_two _ _ _
  have hu13 : u.regs 13 < 2 := by
    rw [run_regs_frame rightCoefficient 13 (by decide),
      run_regs_frame leftCoefficient 13 (by decide)]
    exact ha
  have hu14 : u.regs 14 ≤ t := by
    rw [run_regs_frame rightCoefficient 14 (by decide), hs14]
    exact hi
  have hu15 : u.regs 15 = 1 := (run_regs_frame rightCoefficient 15 (by decide) s).trans
    ((run_regs_frame leftCoefficient 15 (by decide) st).trans h1)
  have hu16 : u.regs 16 = 2 := (run_regs_frame rightCoefficient 16 (by decide) s).trans
    ((run_regs_frame leftCoefficient 16 (by decide) st).trans h2)
  have ht := convolutionTail_cost u t hu3 hu17 hu13 hu14 hu15 hu16
  have htQ : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  dsimp only [u, s] at hr ht
  simp only [convolutionBody, run_seq_snd]
  nlinarith

/-- A convolution is evaluated by the actual nested coefficient programs,
with a cubic bound in the common candidate-space size. -/
theorem convolution_cost (st : State 20 2) (t : ℕ)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9)
    (hn : st.regs 12 ≤ t) :
    (convolutionProgram.run st).2 ≤ 210000 * (2 ^ t + 1) ^ 3 := by
  let n := st.regs 12
  let s := setReg (setReg (setReg (setReg (setReg st 13 0) 14 0) 15 1) 16 2) 18 (n + 1)
  have hinit : ConvolutionInv (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) n 0 s := by
    simp [ConvolutionInv, s, n, Function.update]
  have hit := iterate_cost_idx convolutionBody.run (Nat.size (n + 1) + 1)
    (200000 * (2 ^ t + 1) ^ 2) (n + 1)
    (ConvolutionInv (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) n)
    (by
      intro z u hz hu
      refine ⟨convolutionBody_inv _ _ _ _ _ z u hu, ?_⟩
      obtain ⟨h8, h9, h10, h11, h12, h14, h15, h16, h13⟩ := hu
      apply convolutionBody_cost u t
      · simpa only [h8] using hd
      · simpa only [h9] using he
      · simpa only [h10, h8] using hj
      · simpa only [h11, h9] using hk
      · simpa only [h12] using hn
      · rw [h14]; omega
      · rw [h13]; exact Nat.mod_lt _ (by decide)
      · exact h15
      · exact h16) s hinit
  let Q := 2 ^ t
  have htQ : t ≤ Q := (Nat.lt_two_pow_self (n := t)).le
  have hsz : Nat.size n ≤ Q := (size_le_self _).trans (hn.trans htQ)
  have hsz1 : Nat.size (n + 1) ≤ Q + 1 := (size_le_self _).trans (by omega)
  have hbig : (n + 1) * (Nat.size (n + 1) + 1 + 200000 * (Q + 1) ^ 2) ≤
      (Q + 1) * (Q + 2 + 200000 * (Q + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  simp only [convolutionProgram, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update_self]
  simp only [Function.update, Fin.reduceEq, dite_true, dite_false]
  change (Expr.const 0).cost st.regs + ((Expr.const 0).cost _ + ((Expr.const 1).cost _ +
    ((Expr.const 2).cost _ + ((Expr.add 12 15).cost
      (setReg (setReg (setReg (setReg st 13 0) 14 0) 15 1) 16 2).regs +
      ((iterate convolutionBody.run (Nat.size (n + 1) + 1) (n + 1) s).2 +
        Nat.size (n + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, dite_true, Nat.size_zero, show Nat.size 1 = 1 from rfl,
    show Nat.size 2 = 2 by decide]
  change _ ≤ 210000 * (Q + 1) ^ 3
  have hsum := hit.trans hbig
  nlinarith [Nat.zero_le (Q ^ 3), Nat.zero_le (Q ^ 2)]

end PCP.Lang.BinaryPolynomialCoefficient
