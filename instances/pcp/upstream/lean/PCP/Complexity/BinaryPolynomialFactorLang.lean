/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialConvolutionCost

/-!
# Numeric polynomial factor checks

This module compares every coefficient of a proposed monic factor product with
the candidate polynomial. The loop calls the proved coefficient and convolution
programs, using numeric masks and fixed register files throughout.
-/

namespace PCP.Lang.BinaryPolynomialFactor

open PCP.Algebraic BinaryPolynomialCoefficient

def convolutionEmbedding : Fin 20 → Fin 24 := Fin.castLE (by decide)
def coefficientEmbedding : Fin 8 → Fin 24 := Fin.castLE (by decide)

def convolution24 : Stmt 24 2 := convolutionProgram.rename convolutionEmbedding id
def coefficient24 : Stmt 24 2 := coefficient.rename coefficientEmbedding id

theorem convolution24_run (st : State 24 2) :
    (convolution24.run st).1.regs 13 =
      convolution (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) (st.regs 12) := by
  have h := congrArg (fun z : State 20 2 × ℕ => z.1.regs 13)
    (convolutionProgram.run_rename convolutionEmbedding id (Fin.castLE_injective _)
      Function.injective_id st)
  exact h.trans (convolution_run _)

theorem coefficient24_run (st : State 24 2) :
    (coefficient24.run st).1.regs 3 = value (st.regs 0) (st.regs 1) (st.regs 2) := by
  have h := congrArg (fun z : State 8 2 × ℕ => z.1.regs 3)
    (coefficient.run_rename coefficientEmbedding id (Fin.castLE_injective _)
      Function.injective_id st)
  exact h.trans (coefficient_run _)

/-- Read the product coefficient at the current index, saving it outside scratch space. -/
def productCoefficient : Stmt 24 2 :=
  .seq (.assign 12 (.var 23)) (.seq convolution24 (.assign 19 (.var 13)))

theorem productCoefficient_run (st : State 24 2) :
    (productCoefficient.run st).1.regs 19 =
      convolution (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) (st.regs 23) := by
  simp only [productCoefficient, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  rw [convolution24_run]
  simp [Function.update]

theorem convolution_sets_one (st : State 20 2) :
    (convolutionProgram.run st).1.regs 15 = 1 := by
  have hf := run_regs_frame (.loop (18 : Fin 20) convolutionBody) 15 (by decide)
  simp only [convolutionProgram, run_seq_fst, run_assign_fst, Expr.eval, hf]
  simp [Function.update]

theorem productCoefficient_sets_one (st : State 24 2) :
    (productCoefficient.run st).1.regs 15 = 1 := by
  have h := congrArg (fun z : State 20 2 × ℕ => z.1.regs 15)
    (convolutionProgram.run_rename convolutionEmbedding id (Fin.castLE_injective _)
      Function.injective_id (setReg st 12 (st.regs 23)))
  simp only [productCoefficient, run_seq_fst, run_assign_fst, Expr.eval]
  simp only [setReg_regs, Function.update_of_ne (by decide : (15 : Fin 24) ≠ 19)]
  exact h.trans (convolution_sets_one _)

/-- Read the candidate coefficient at the same current index. -/
def candidateCoefficient : Stmt 24 2 :=
  .seq (.assign 0 (.var 20)) (.seq (.assign 1 (.var 21))
    (.seq (.assign 2 (.var 23)) coefficient24))

theorem candidateCoefficient_run (st : State 24 2) :
    (candidateCoefficient.run st).1.regs 3 = value (st.regs 20) (st.regs 21) (st.regs 23) := by
  simp only [candidateCoefficient, run_seq_fst, run_assign_fst, Expr.eval]
  rw [coefficient24_run]
  simp [Function.update]

def compareTail : Stmt 24 2 :=
  .seq (.assign 3 (.eq 3 19)) (.seq (.assign 22 (.mul 22 3)) (.assign 23 (.add 23 15)))

def matchBody : Stmt 24 2 :=
  .seq productCoefficient (.seq candidateCoefficient compareTail)

theorem matchBody_step (st : State 24 2) :
    (matchBody.run st).1.regs 22 = st.regs 22 *
      (if value (st.regs 20) (st.regs 21) (st.regs 23) =
        convolution (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) (st.regs 23)
        then 1 else 0) ∧
    (matchBody.run st).1.regs 23 = st.regs 23 + 1 := by
  have hs19 := productCoefficient_run st
  have hs15 := productCoefficient_sets_one st
  have hs20 := run_regs_frame productCoefficient 20 (by decide) st
  have hs21 := run_regs_frame productCoefficient 21 (by decide) st
  have hs22 := run_regs_frame productCoefficient 22 (by decide) st
  have hs23 := run_regs_frame productCoefficient 23 (by decide) st
  simp only [matchBody, run_seq_fst]
  generalize hs : (productCoefficient.run st).1 = s at *
  have hu3 := candidateCoefficient_run s
  rw [hs20, hs21, hs23] at hu3
  have hu19 := run_regs_frame candidateCoefficient 19 (by decide) s
  have hu15 := run_regs_frame candidateCoefficient 15 (by decide) s
  have hu22 := run_regs_frame candidateCoefficient 22 (by decide) s
  have hu23 := run_regs_frame candidateCoefficient 23 (by decide) s
  rw [hs19] at hu19
  rw [hs15] at hu15
  rw [hs22] at hu22
  rw [hs23] at hu23
  generalize hu : (candidateCoefficient.run s).1 = u at *
  simp only [compareTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    hu3, hu19, hu15, hu22, hu23, and_self]

def MatchesPrefix (t code d e j k n : ℕ) : Prop :=
  ∀ i ∈ Finset.range n, value t code i = convolution d e j k i

instance (t code d e j k n : ℕ) : Decidable (MatchesPrefix t code d e j k n) :=
  inferInstanceAs (Decidable (∀ i ∈ Finset.range n, value t code i = convolution d e j k i))

theorem matchesPrefix_succ (t code d e j k n : ℕ) :
    MatchesPrefix t code d e j k (n + 1) ↔
      MatchesPrefix t code d e j k n ∧ value t code n = convolution d e j k n := by
  simp [MatchesPrefix, Finset.range_add_one, and_comm]

def MatchInv (t code d e j k n : ℕ) (st : State 24 2) : Prop :=
  st.regs 8 = d ∧ st.regs 9 = e ∧ st.regs 10 = j ∧ st.regs 11 = k ∧
  st.regs 20 = t ∧ st.regs 21 = code ∧ st.regs 23 = n ∧
  st.regs 22 = if MatchesPrefix t code d e j k n then 1 else 0

theorem matchBody_inv (t code d e j k n : ℕ) (st : State 24 2)
    (h : MatchInv t code d e j k n st) : MatchInv t code d e j k (n + 1) (matchBody.run st).1 := by
  obtain ⟨h8, h9, h10, h11, h20, h21, h23, h22⟩ := h
  obtain ⟨hnext, hi⟩ := matchBody_step st
  refine ⟨(run_regs_frame matchBody 8 (by decide) st).trans h8,
    (run_regs_frame matchBody 9 (by decide) st).trans h9,
    (run_regs_frame matchBody 10 (by decide) st).trans h10,
    (run_regs_frame matchBody 11 (by decide) st).trans h11,
    (run_regs_frame matchBody 20 (by decide) st).trans h20,
    (run_regs_frame matchBody 21 (by decide) st).trans h21,
    hi.trans (by rw [h23]), ?_⟩
  rw [hnext, h8, h9, h10, h11, h20, h21, h23, h22]
  simp only [matchesPrefix_succ]
  split_ifs <;> simp_all

/-- Check the full product, returning zero or one in register `22`. -/
def matchProduct : Stmt 24 2 :=
  .seq (.assign 22 (.const 1)) (.seq (.assign 23 (.const 0))
    (.seq (.assign 15 (.const 1)) (.seq (.assign 7 (.add 20 15)) (.loop 7 matchBody))))

set_option maxHeartbeats 800000 in
-- Transporting the full nested loop invariant requires additional elaboration budget.
theorem matches_run (st : State 24 2) :
    (matchProduct.run st).1.regs 22 =
      if MatchesPrefix (st.regs 20) (st.regs 21) (st.regs 8) (st.regs 9)
        (st.regs 10) (st.regs 11) (st.regs 20 + 1) then 1 else 0 := by
  let t := st.regs 20
  let s := setReg (setReg (setReg (setReg st 22 1) 23 0) 15 1) 7 (t + 1)
  have hinit : MatchInv t (st.regs 21) (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) 0 s :=
    by simp [MatchInv, MatchesPrefix, s, t, Function.update]
  have h := iterate_inv matchBody.run (Nat.size (t + 1) + 1) (t + 1)
    (MatchInv t (st.regs 21) (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11))
    (fun n u _ hu => matchBody_inv _ _ _ _ _ _ n u hu) s hinit
  have hfinal := h.2.2.2.2.2.2.2
  simp only [matchProduct, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false]
  exact hfinal

theorem matchesPrefix_iff (t : ℕ) (code : Fin (2 ^ t)) (d : ℕ)
    (j : Fin (2 ^ d)) (k : Fin (2 ^ (t - d))) :
    MatchesPrefix t code.val d (t - d) j.val k.val (t + 1) ↔
      BinaryIrreduciblePolynomial.ProductMatches t code d j k := by
  constructor
  · intro h n
    apply ZMod.val_injective 2
    rw [← convolution_value, coefficient_value]
    exact (h n.val (Finset.mem_range.mpr n.isLt)).symm
  · intro h n hn
    have hn' : n < t + 1 := Finset.mem_range.mp hn
    have hc := congrArg ZMod.val (h ⟨n, hn'⟩)
    rw [← convolution_value, coefficient_value] at hc
    exact hc.symm

end PCP.Lang.BinaryPolynomialFactor
