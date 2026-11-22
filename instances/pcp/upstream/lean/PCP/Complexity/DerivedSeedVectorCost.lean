/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedResources
import PCP.Complexity.InnerSeedWordCost

/-! # Polynomial charged cost of materializing correction direction vectors -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

def vectorConstant (field : Bool) (src len : Fin 300) : ℕ :=
  (vectorPrepare src len (if field then .var 243 else .const 2)).C *
    ((vectorPrepare src len (if field then .var 243 else .const 2)).width +
    (vectorPrepare src len (if field then .var 243 else .const 2)).csize + 1) +
      InnerSeed.coordinateConstant

attribute [local irreducible] vectorDecode

theorem vector_cost (field : Bool) (t N W : ℕ) (src len : Fin 300) (dst : Fin 112) (hlen : 220 ≤
  len.val)
    (st : State 300 112) (hn : st.regs len = N) (hq : st.regs 243 = 2 ^ t)
    (hc : Nat.size (st.regs src) ≤ W) (he : st.lists 100 = []) :
    ((vector src len (if field then .var 243 else .const 2) dst).run st).2 ≤ vectorConstant
      field src len * (N + t + W + 3) ^ 4 := by
  have hlen0 : len ≠ 0 := by intro h; subst len; norm_num at hlen
  have hprep := loopFree_cost_le
    (vectorPrepare src len (if field then .var 243 else .const 2))
    (by simp [vectorPrepare, Stmt.loopFree]) st (N + t + W + 2)
    (by
      intro i hi
      have he : i = src ∨ i = len ∨ i = 243 := by
        cases field <;> simp [vectorPrepare, Stmt.uses, Stmt.mustW, Expr.uses] at hi <;> tauto
      rcases he with rfl | rfl | rfl
      · omega
      · rw [hn]
        exact (size_le_self N).trans (by omega)
      · rw [hq, Nat.size_pow]
        omega)
    (by
      intro L hL
      change L ∈ [100] at hL
      simp only [List.mem_singleton] at hL
      subst L
      simp [he, listSize])
  have h0 : ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 0 =
    st.regs src := by
    simp [vectorPrepare, Stmt.run, Expr.eval, Function.update]
  have h5 : ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 5 = N
    := by
    simp [vectorPrepare, Stmt.run, Expr.eval, Function.update, hlen0, hn]
  have h6 : ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 6 = 2
    ^ (if field then t else 1) := by
    cases field <;> simp [vectorPrepare, Stmt.run, Expr.eval, Function.update, hq]
  have h2 : ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.lists 2 =
    [] := by
    simp [vectorPrepare, Stmt.run, Function.update, he]
  have hd := UniformDecode.program_cost
    (DerivedCall.view (by decide : 7 ≤ 300) (by decide : 3 ≤ 112)
      ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1) (by exact h2)
  have hout := (UniformDecode.program_run
    (DerivedCall.view (by decide : 7 ≤ 300) (by decide : 3 ≤ 112)
      ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1) (by exact h2)).1
  rw [← DerivedCall.call_result (by decide) (by decide) UniformDecode.program] at hd hout
  rw [show DerivedCall.call (by decide) (by decide) UniformDecode.program = vectorDecode by
    unfold vectorDecode; rfl] at hd hout
  change (vectorDecode.run ((vectorPrepare src len (if field then .var 243 else .const 2)).run
    st).1).2 ≤
    (MixedRadixDecode.passConstant + 24) *
      (((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 5 *
        (Nat.size (((vectorPrepare src len (if field then .var 243 else .const 2)).run
          st).1.regs 6) + 1) +
        ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 5 +
        Nat.size (((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs
          0) + 3) ^ 2 at hd
  change (vectorDecode.run ((vectorPrepare src len (if field then .var 243 else .const 2)).run
    st).1).1.lists 1 =
    (MixedRadixDecode.split (((vectorPrepare src len (if field then .var 243 else .const 2)).run
      st).1.regs 0)
      (List.replicate (((vectorPrepare src len (if field then .var 243 else .const 2)).run
        st).1.regs 5)
        (((vectorPrepare src len (if field then .var 243 else .const 2)).run st).1.regs 6))).1
          at hout
  rw [h0, h5, h6] at hd hout
  have hls := MixedRadixDecode.split_listSize (st.regs src) (List.replicate N (2 ^ (if field
    then t else 1)))
  rw [List.length_replicate] at hls
  have hsum : ((vector src len (if field then .var 243 else .const 2) dst).run st).2 ≤
      ((vectorPrepare src len (if field then .var 243 else .const 2)).run st).2 +
        (MixedRadixDecode.passConstant + 24) *
        (N * (Nat.size (2 ^ (if field then t else 1)) + 1) + N + Nat.size (st.regs src) + 3) ^ 2 +
          N * (Nat.size (st.regs src) + 1) + 3 := by
    simp only [vector, run_seq_snd, run_copy_snd, hout]
    omega
  have hlin : N + t + W + 2 + 1 = N + t + W + 3 := by omega
  rw [hlin] at hprep
  have hp := hprep.trans (Nat.mul_le_mul_left _ (Nat.le_pow (by decide : 0 < 4)))
  exact hsum.trans (InnerSeed.coordinate_bound _ _ _ _ _ _ (by omega) (by omega)
    (by cases field <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.size_pow] <;> omega)
      (hc.trans (by omega)) hp)

end PCP.Lang.DerivedSeed
