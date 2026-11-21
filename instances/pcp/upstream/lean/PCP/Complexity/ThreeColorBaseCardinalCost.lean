/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ThreeColorBaseCardinal
import PCP.Complexity.HadamardSeedRadicesCost

/-! # Charged polynomial cost of the production table cardinalities -/

namespace PCP.Lang.ThreeColorBaseCardinal

open PCP.Algebraic ThreeColorBaseSetup

attribute [local irreducible] PowerTwo.program HadamardSeed.count

def loadConstant (c : ℕ) : ℕ :=
  (tupleLoad c).C * ((tupleLoad c).width + (tupleLoad c).csize + 1)

theorem tupleLoad_cost (c t n : ℕ) (st : State 400 128)
    (ht : st.regs 324 = t) (hn : st.regs 322 = n) :
    ((tupleLoad c).run st).2 ≤ loadConstant c * (t+n+1) := by
  apply loopFree_cost_le (tupleLoad c) (by simp [tupleLoad, Stmt.loopFree]) st (t+n)
  · intro i hi
    have he : i = 322 ∨ i = 324 := by
      simp [tupleLoad, Stmt.uses, Expr.uses, Stmt.mustW] at hi
      tauto
    rcases he with rfl | rfl
    · rw [hn]
      exact (size_le_self n).trans (Nat.le_add_left _ _)
    · rw [ht]
      exact (size_le_self t).trans (Nat.le_add_right _ _)
  · simp [tupleLoad, Stmt.lUses]

theorem power_cost (st : State 400 128) :
    (power.run st).2 ≤ 20 * (st.regs 2 + 1)^2 := by
  have h := PowerTwo.program_cost
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← call_result (by decide) (by decide) PowerTwo.program st] at h
  exact h

def tupleCost (c t n : ℕ) : ℕ := loadConstant c * (t+n+1) +
  20*(t*(c*n)+1)^2 + 2*(t*(c*n)+1) + 3

theorem tuple_cost (c t n : ℕ) (dst : Fin 400) (st : State 400 128)
    (ht : st.regs 324 = t) (hn : st.regs 322 = n) :
    ((tuple c dst).run st).2 ≤ tupleCost c t n := by
  have hl := tupleLoad_cost c t n st ht hn
  have he : ((tupleLoad c).run st).1.regs 2 = t*(c*n) := by
    simp [tupleLoad, Stmt.run, Expr.eval, Function.update, ht, hn, Nat.mul_comm]
  have hp := power_cost ((tupleLoad c).run st).1
  have ho := power_run ((tupleLoad c).run st).1
  rw [he] at hp ho
  simp only [tuple, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ho,
    Nat.size_pow]
  unfold tupleCost
  omega

theorem count_cost (r t : ℕ) (st : State 400 128)
    (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    ((count r).run st).2 ≤ 600000*(2^t+Nat.size r+3)^4 := by
  have h := HadamardSeed.count_cost r
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht he
  rw [← call_result (by decide) (by decide) (HadamardSeed.count r) st] at h
  exact h

def labelCost (r t : ℕ) : ℕ := 2*t+3+600000*(2^t+Nat.size r+3)^4+2*(2^t+1)+3

theorem label_cost (r t : ℕ) (dst : Fin 400) (st : State 400 128)
    (ht : st.regs 324 = t) (he : st.lists 122 = []) :
    ((label r dst).run st).2 ≤ labelCost r t := by
  have ht' : (labelLoad.run st).1.regs 20 = t := by
    simpa [labelLoad, Stmt.run, Expr.eval, Function.update] using ht
  have he' : (labelLoad.run st).1.lists 7 = [] := by
    simpa [labelLoad, Stmt.run, Function.update] using he
  have hc := count_cost r t (labelLoad.run st).1 ht' he'
  have ho := count_run r t (labelLoad.run st).1 ht' he'
  have hs : Nat.size (2^BooleanCoefficientIndex.dimension t r) ≤ 2^t+1 :=
    HadamardSeed.cardinal_size t r
  have hl : (labelLoad.run st).2 ≤ 2*t+3 := by
    simp only [labelLoad, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
      setReg_lists, ht, he,
      show listSize ([] : List ℕ) = 0 from rfl]
    have h := size_le_self t
    omega
  simp only [label, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ho]
  unfold labelCost
  omega

def programCost (t n : ℕ) : ℕ := tupleCost 1 t n + tupleCost 2 t n +
  2*tupleCost 4 t n + labelCost 1 t + labelCost 3 t + 5

/-- Polynomial in dimension, field width and field cardinality; no source-size premise. -/
theorem program_cost (t n : ℕ) (st : State 400 128)
    (ht : st.regs 324 = t) (hn : st.regs 322 = n) (he : st.lists 122 = []) :
    (program.run st).2 ≤ programCost t n := by
  have h0 := tuple_cost 1 t n 328 st ht hn
  have ht0 := (tuple_reg 1 328 324 (by decide) (by decide) st).trans ht
  have hn0 := (tuple_reg 1 328 322 (by decide) (by decide) st).trans hn
  have he0 := (tuple_list 1 328 122 (by decide) st).trans he
  generalize hst0 : ((tuple 1 328).run st).1 = s0 at *
  have h1 := tuple_cost 2 t n 329 s0 ht0 hn0
  have ht1 := (tuple_reg 2 329 324 (by decide) (by decide) s0).trans ht0
  have hn1 := (tuple_reg 2 329 322 (by decide) (by decide) s0).trans hn0
  have he1 := (tuple_list 2 329 122 (by decide) s0).trans he0
  generalize hst1 : ((tuple 2 329).run s0).1 = s1 at *
  have h2 := tuple_cost 4 t n 330 s1 ht1 hn1
  have ht2 := (tuple_reg 4 330 324 (by decide) (by decide) s1).trans ht1
  have hn2 := (tuple_reg 4 330 322 (by decide) (by decide) s1).trans hn1
  have he2 := (tuple_list 4 330 122 (by decide) s1).trans he1
  generalize hst2 : ((tuple 4 330).run s1).1 = s2 at *
  have h3 := tuple_cost 4 t n 331 s2 ht2 hn2
  have ht3 := (tuple_reg 4 331 324 (by decide) (by decide) s2).trans ht2
  have he3 := (tuple_list 4 331 122 (by decide) s2).trans he2
  generalize hst3 : ((tuple 4 331).run s2).1 = s3 at *
  have h4 := label_cost 1 t 332 s3 ht3 he3
  have ht4 := (label_reg 1 332 324 (by decide) (by decide) s3).trans ht3
  have he4 := (label_list 1 332 122 (by decide) s3).trans he3
  generalize hst4 : ((label 1 332).run s3).1 = s4 at *
  have h5 := label_cost 3 t 333 s4 ht4 he4
  simp only [program, run_seq_snd, hst0, hst1, hst2, hst3, hst4]
  unfold programCost
  omega

end PCP.Lang.ThreeColorBaseCardinal
