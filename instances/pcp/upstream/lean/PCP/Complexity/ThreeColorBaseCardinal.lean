/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ThreeColorBaseSetup

/-! # Actual construction of the six production proof-table cardinalities -/

namespace PCP.Lang.ThreeColorBaseCardinal

open PCP.Algebraic ThreeColorBaseSetup

/-- All calls use only the prefix workspace and retain permanent metadata. -/
def power : Stmt 400 128 := call (by decide) (by decide) PowerTwo.program

def count (r : ℕ) : Stmt 400 128 := call (by decide) (by decide) (HadamardSeed.count r)

def tupleLoad (c : ℕ) : Stmt 400 128 := .seq (.assign 0 (.const c))
  (.seq (.assign 1 (.mul 322 0)) (.assign 2 (.mul 324 1)))

def tuple (c : ℕ) (dst : Fin 400) : Stmt 400 128 :=
  .seq (tupleLoad c) (.seq power (.assign dst (.var 5)))

def labelLoad : Stmt 400 128 := .seq (.assign 20 (.var 324)) (.copy 122 7)

def label (r : ℕ) (dst : Fin 400) : Stmt 400 128 :=
  .seq labelLoad (.seq (count r) (.assign dst (.var 73)))

def program : Stmt 400 128 := .seq (tuple 1 328) (.seq (tuple 2 329)
  (.seq (tuple 4 330) (.seq (tuple 4 331) (.seq (label 1 332) (label 3 333)))))

attribute [local irreducible] PowerTwo.program HadamardSeed.count

theorem power_run (st : State 400 128) :
    (power.run st).1.regs 5 = 2 ^ st.regs 2 := by
  have h := PowerTwo.program_run
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← call_result (by decide) (by decide) PowerTwo.program st] at h
  exact h

theorem count_run (r t : ℕ) (st : State 400 128)
    (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    ((count r).run st).1.regs 73 = 2 ^ BooleanCoefficientIndex.dimension t r := by
  have h := (HadamardSeed.count_run r
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht he).2
  rw [← call_result (by decide) (by decide) (HadamardSeed.count r) st] at h
  exact h

theorem tuple_run (c t n : ℕ) (dst : Fin 400) (st : State 400 128)
    (ht : st.regs 324 = t) (hn : st.regs 322 = n) :
    ((tuple c dst).run st).1.regs dst = (2 ^ t) ^ (c * n) := by
  have h := power_run ((tupleLoad c).run st).1
  simp only [tuple, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self, h]
  simp [tupleLoad, Stmt.run, Expr.eval, Function.update, ht, hn, pow_mul, Nat.mul_comm]

theorem label_run (r t : ℕ) (dst : Fin 400) (st : State 400 128)
    (ht : st.regs 324 = t) (he : st.lists 122 = []) :
    ((label r dst).run st).1.regs dst = 2 ^ BooleanCoefficientIndex.dimension t r := by
  have h := count_run r t (labelLoad.run st).1
    (by simpa [labelLoad, Stmt.run, Expr.eval, Function.update] using ht)
    (by simpa [labelLoad, Stmt.run, Expr.eval, Function.update] using he)
  simpa only [label, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self] using h

theorem tuple_reg (c : ℕ) (dst i : Fin 400) (hi : 100 ≤ i.val) (hn : i ≠ dst)
    (st : State 400 128) : ((tuple c dst).run st).1.regs i = st.regs i := by
  simp only [tuple, run_seq_fst, run_assign_fst, setReg_regs, Function.update_of_ne hn]
  rw [show (power.run ((tupleLoad c).run st).1).1.regs i =
    ((tupleLoad c).run st).1.regs i from call_reg (by decide) (by decide)
      PowerTwo.program _ i (by omega)]
  exact run_regs_frame (tupleLoad c) i (by simp [tupleLoad, Stmt.regWrites]; omega) st

theorem label_reg (r : ℕ) (dst i : Fin 400) (hi : 100 ≤ i.val) (hn : i ≠ dst)
    (st : State 400 128) : ((label r dst).run st).1.regs i = st.regs i := by
  simp only [label, run_seq_fst, run_assign_fst, setReg_regs, Function.update_of_ne hn]
  rw [show ((count r).run (labelLoad.run st).1).1.regs i = (labelLoad.run st).1.regs i from
    call_reg (by decide) (by decide) (HadamardSeed.count r) _ i hi]
  exact run_regs_frame labelLoad i (by simp [labelLoad, Stmt.regWrites]; omega) st

theorem tuple_list (c : ℕ) (dst : Fin 400) (L : Fin 128) (hL : 100 ≤ L.val)
    (st : State 400 128) : ((tuple c dst).run st).1.lists L = st.lists L := by
  simp only [tuple, run_seq_fst, run_assign_fst, setReg_lists]
  rw [show (power.run ((tupleLoad c).run st).1).1.lists L =
    ((tupleLoad c).run st).1.lists L from call_list (by decide) (by decide)
      PowerTwo.program _ L (by omega)]
  rfl

theorem label_list (r : ℕ) (dst : Fin 400) (L : Fin 128) (hL : 100 ≤ L.val)
    (st : State 400 128) : ((label r dst).run st).1.lists L = st.lists L := by
  simp only [label, run_seq_fst, run_assign_fst, setReg_lists]
  rw [show ((count r).run (labelLoad.run st).1).1.lists L = (labelLoad.run st).1.lists L from
    call_list (by decide) (by decide) (HadamardSeed.count r) _ L (by omega)]
  apply Function.update_of_ne
  intro h
  have := congrArg Fin.val h
  omega

structure Cardinal (t n : ℕ) (st : State 400 128) : Prop where
  vertices : st.regs 328 = (2^t)^n
  pairs : st.regs 329 = (2^t)^(n+n)
  proper : st.regs 330 = (2^t)^((n+n)+(n+n))
  inner : st.regs 331 = (2^t)^(4*n)
  affine : st.regs 332 = 2^BooleanCoefficientIndex.dimension t 1
  cubic : st.regs 333 = 2^BooleanCoefficientIndex.dimension t 3

theorem program_run (t n : ℕ) (st : State 400 128)
    (ht : st.regs 324 = t) (hn : st.regs 322 = n) (he : st.lists 122 = []) :
    Cardinal t n (program.run st).1 := by
  have h0 := tuple_run 1 t n 328 st ht hn
  have ht0 := (tuple_reg 1 328 324 (by decide) (by decide) st).trans ht
  have hn0 := (tuple_reg 1 328 322 (by decide) (by decide) st).trans hn
  have he0 := (tuple_list 1 328 122 (by decide) st).trans he
  generalize hst0 : ((tuple 1 328).run st).1 = s0 at *
  have h1 := tuple_run 2 t n 329 s0 ht0 hn0
  have ht1 := (tuple_reg 2 329 324 (by decide) (by decide) s0).trans ht0
  have hn1 := (tuple_reg 2 329 322 (by decide) (by decide) s0).trans hn0
  have he1 := (tuple_list 2 329 122 (by decide) s0).trans he0
  generalize hst1 : ((tuple 2 329).run s0).1 = s1 at *
  have h2 := tuple_run 4 t n 330 s1 ht1 hn1
  have ht2 := (tuple_reg 4 330 324 (by decide) (by decide) s1).trans ht1
  have hn2 := (tuple_reg 4 330 322 (by decide) (by decide) s1).trans hn1
  have he2 := (tuple_list 4 330 122 (by decide) s1).trans he1
  generalize hst2 : ((tuple 4 330).run s1).1 = s2 at *
  have h3 := tuple_run 4 t n 331 s2 ht2 hn2
  have ht3 := (tuple_reg 4 331 324 (by decide) (by decide) s2).trans ht2
  have he3 := (tuple_list 4 331 122 (by decide) s2).trans he2
  generalize hst3 : ((tuple 4 331).run s2).1 = s3 at *
  have h4 := label_run 1 t 332 s3 ht3 he3
  have ht4 := (label_reg 1 332 324 (by decide) (by decide) s3).trans ht3
  have he4 := (label_list 1 332 122 (by decide) s3).trans he3
  generalize hst4 : ((label 1 332).run s3).1 = s4 at *
  have h5 := label_run 3 t 333 s4 ht4 he4
  simp only [program, run_seq_fst, hst0, hst1, hst2, hst3, hst4]
  constructor
  · rw [label_reg 3 333 328 (by decide) (by decide), ← hst4,
      label_reg 1 332 328 (by decide) (by decide), ← hst3,
      tuple_reg 4 331 328 (by decide) (by decide), ← hst2,
      tuple_reg 4 330 328 (by decide) (by decide), ← hst1,
      tuple_reg 2 329 328 (by decide) (by decide), h0, one_mul]
  · rw [label_reg 3 333 329 (by decide) (by decide), ← hst4,
      label_reg 1 332 329 (by decide) (by decide), ← hst3,
      tuple_reg 4 331 329 (by decide) (by decide), ← hst2,
      tuple_reg 4 330 329 (by decide) (by decide), h1, two_mul]
  · rw [label_reg 3 333 330 (by decide) (by decide), ← hst4,
      label_reg 1 332 330 (by decide) (by decide), ← hst3,
      tuple_reg 4 331 330 (by decide) (by decide), h2]
    congr 1
    omega
  · rw [label_reg 3 333 331 (by decide) (by decide), ← hst4,
      label_reg 1 332 331 (by decide) (by decide), h3]
  · rw [label_reg 3 333 332 (by decide) (by decide), h4]
  · exact h5

theorem program_reg (i : Fin 400) (hi : 100 ≤ i.val)
    (h0 : i ≠ 328) (h1 : i ≠ 329) (h2 : i ≠ 330)
    (h3 : i ≠ 331) (h4 : i ≠ 332) (h5 : i ≠ 333) (st : State 400 128) :
    (program.run st).1.regs i = st.regs i := by
  simp only [program, run_seq_fst, label_reg _ _ i hi h5, label_reg _ _ i hi h4,
    tuple_reg _ _ i hi h3, tuple_reg _ _ i hi h2, tuple_reg _ _ i hi h1,
    tuple_reg _ _ i hi h0]

theorem program_list (L : Fin 128) (hL : 100 ≤ L.val) (st : State 400 128) :
    (program.run st).1.lists L = st.lists L := by
  simp only [program, run_seq_fst, tuple_list _ _ L hL, label_list _ _ L hL]

theorem program_data (N : ℕ) (st : State 400 128) (h : Data N st) :
    Data N (program.run st).1 := by
  constructor
  all_goals first
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.order
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.exponent
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.dimension
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.volume
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.width
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.card
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.cube
    | exact (program_reg _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) st).trans h.generatorCode
    | exact (program_list _ (by decide) st).trans h.modulus
    | exact (program_list _ (by decide) st).trans h.nodes
    | exact (program_list _ (by decide) st).trans h.empty

theorem program_sources (x bits answers : List Bool) (st : State 400 128)
    (h : Sources x bits answers st) : Sources x bits answers (program.run st).1 :=
  ⟨(program_list 100 (by decide) st).trans h.graph,
    (program_list 101 (by decide) st).trans h.bits,
    (program_list 102 (by decide) st).trans h.answers,
    (program_list 122 (by decide) st).trans h.empty⟩

end PCP.Lang.ThreeColorBaseCardinal
