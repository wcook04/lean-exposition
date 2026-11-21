/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedSplitCost
import PCP.Complexity.DerivedSeedVectorCost
import PCP.Complexity.HadamardSeedMaterializeCost

/-! # Charged cost of decoding and storing the raw derived seed -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid BinaryPolynomialSpace
variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] vector maskLoad HadamardSeed.loadTo

def maskCost (t : ℕ) : ℕ := 710000*(2^t+5)^4+3*2^t+2*t+10

omit [NeZero t] in
theorem mask_cost (p : Coefficients t 3) (st : State 300 112)
    (ht : st.regs 240 = t) (he : st.lists 100 = [])
    (hp : st.regs 277 = ((coefficientCodec t 3).equiv p).val) :
    (mask.run st).2 ≤ maskCost t := by
  have hp' : st.regs 277 = HadamardLabel.code p := hp
  have hprep : (maskPrepare.run st).2 ≤ 2^t+2*t+7 := by
    have hc := HadamardLabel.code_size p
    have hs := size_le_self t
    simp only [maskPrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
      setList_lists, Function.update_self, Function.update_of_ne (by decide : (100 : Fin 112) ≠ 7),
      setList_regs, hp', he, ht,
      show listSize ([] : List ℕ) = 0 from rfl]
    omega
  have hwidth : (DerivedCall.view (by decide) (by decide) (maskPrepare.run st).1 :
      State 100 32).regs 20 = t := by
    simp [DerivedCall.view, State.restrict, maskPrepare, Stmt.run, Expr.eval, Function.update, ht]
  have hempty : (DerivedCall.view (by decide) (by decide) (maskPrepare.run st).1 :
      State 100 32).lists 7 = [] := by
    simp [DerivedCall.view, State.restrict, maskPrepare, Stmt.run, Function.update, he]
  have hcodes : (DerivedCall.view (by decide) (by decide) (maskPrepare.run st).1 :
      State 100 32).lists 25 = [HadamardLabel.code p] := by
    simp [DerivedCall.view, State.restrict, maskPrepare, Stmt.run, Function.update, he, hp']
  have hc := HadamardSeed.loadTo_cost p [] 18 _ hwidth hempty hcodes
  have ho := (HadamardSeed.loadTo_run p [] 18 (by decide) (by decide) _
    hwidth hempty hcodes).1
  rw [← DerivedCall.call_result (by decide) (by decide) (HadamardSeed.loadTo 3 18)] at hc ho
  rw [show DerivedCall.call (by decide) (by decide) (HadamardSeed.loadTo 3 18) = maskLoad by
    unfold maskLoad; rfl] at hc ho
  change (maskLoad.run (maskPrepare.run st).1).1.lists 18 = BooleanCoefficientList.encode p at ho
  have hs := HadamardLabel.encode_size p
  simp only [mask, run_seq_snd, run_copy_snd, ho]
  change (maskLoad.run (maskPrepare.run st).1).2 ≤ 710000*(2^t+2+3)^4 at hc
  simp only [Nat.add_assoc] at hc
  change (maskLoad.run (maskPrepare.run st).1).2 ≤ 710000*(2^t+5)^4 at hc
  unfold maskCost
  omega

def wordsCost (d t W : ℕ) : ℕ :=
  vectorConstant true 259 256*(d+t+W+3)^4 +
    vectorConstant false 258 240*(t+t+W+3)^4 + maskCost t + 2

theorem words_cost (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (W : ℕ) (st : State 300 112) (hi : Input k s st) (hd : Data k s st)
    (hcode : Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
      (baseDimension k n) m 4 3).equiv s).val ≤ W) :
    (words.run st).2 ≤ wordsCost (baseDimension k n) t W := by
  have hdb := hd.bound W hcode
  have hp := vector_cost true t (baseDimension k n) W 259 256 109 (by decide) st
    hi.dimension hi.card (hdb 4) hi.empty
  have hip := hi.of_regs (fun i h => vector_reg 259 256 i (.var 243) 109 h st)
    (vector_list 259 256 (.var 243) 109 100 (by decide) (by decide) st)
  have hdp := hd.of_regs (fun i h => vector_reg 259 256 i (.var 243) 109 h st)
  generalize hu : ((vector 259 256 (.var 243) 109).run st).1 = u at *
  have hb := vector_cost false t t W 258 240 105 (by decide) u
    hip.width hip.card (hdp.bound W hcode 3) hip.empty
  have hib := hip.of_regs (fun i h => vector_reg 258 240 i (.const 2) 105 h u)
    (vector_list 258 240 (.const 2) 105 100 (by decide) (by decide) u)
  have hdb' := hdp.of_regs (fun i h => vector_reg 258 240 i (.const 2) 105 h u)
  generalize hv : ((vector 258 240 (.const 2) 105).run u).1 = v at *
  have hm := mask_cost s.2.2 v hib.width hib.empty hdb'.mask
  simp only [words, run_seq_snd, hu, hv]
  simp only [Bool.false_eq_true, ↓reduceIte] at hp hb
  unfold wordsCost
  omega

def materializeCost (d m t W : ℕ) : ℕ :=
  splitConstant*(radixBound d m t+W+5)^2+wordsCost d t W+1

theorem materialize_cost (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (W : ℕ) (st : State 300 112) (hi : Input k s st) (hb : InputBound W st) :
    (materialize.run st).2 ≤ materializeCost (baseDimension k n) m t W := by
  have hs := split_cost k s W st hi hb
  have hout := split_run k s st hi
  have hcode : Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
      (baseDimension k n) m 4 3).equiv s).val ≤ W := hi.seed ▸ hb 3
  have hw := words_cost k s W _ hi.split hout hcode
  simp only [materialize, run_seq_snd]
  unfold materializeCost
  omega

end PCP.Lang.DerivedSeed
