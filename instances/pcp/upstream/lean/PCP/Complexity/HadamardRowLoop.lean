/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowFactor

/-!
# A stored factor loop for the Hadamard row

Each iteration consumes one numeric factor code and emits its product and padded
factor labels. The invariant retains the exact seed and the entire ordered trace.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def factorLabels (s : TestRandomness t r) (k : Fin (r - 1)) : List ℕ :=
  [code (ComputableHadamardTest.productQuery s k + s.base),
    code (ComputableHadamardTest.factorQuery s k + s.base)]

def factorPrefix (s : TestRandomness t r) (j : ℕ) : List ℕ :=
  ((List.finRange (r - 1)).take j).flatMap (factorLabels s)

theorem factorPrefix_succ (s : TestRandomness t r) (j : ℕ) (hj : j < r - 1) :
    factorPrefix s (j + 1) = factorPrefix s j ++ factorLabels s ⟨j, hj⟩ := by
  have hl : j < (List.finRange (r - 1)).length := by simpa using hj
  simp only [factorPrefix, List.take_succ_eq_append_getElem hl,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.getElem_finRange]
  congr 2

theorem factorCodes_drop (s : TestRandomness t r) (j : ℕ) (hj : j < r - 1) :
    (factorCodes s).drop j = code (s.factor ⟨j, hj⟩) :: (factorCodes s).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa [factorCodes] using hj)]
  simp only [factorCodes, List.getElem_ofFn]

def factorBody : Stmt 80 32 :=
  .seq (.assign 60 (.add 59 61))
    (.seq HadamardFactorLoad.load (.seq pair (.assign 59 (.add 59 61))))

theorem factorBody_step (s : TestRandomness t r) (k : Fin (r - 1)) (cs : List ℕ)
    (st : State 80 32) (hc : Context s st) (hk : st.regs 59 = k.val)
    (hone : st.regs 61 = 1) (hcs : st.lists 25 = code (s.factor k) :: cs) :
    Context s (factorBody.run st).1 ∧
      (factorBody.run st).1.regs 59 = k.val + 1 ∧
      (factorBody.run st).1.regs 61 = 1 ∧
      (factorBody.run st).1.lists 25 = cs ∧
      (factorBody.run st).1.lists 24 = (factorLabels s k).reverse ++ st.lists 24 := by
  let u := setReg st 60 (st.regs 59 + st.regs 61)
  have hu : Context s u := by simpa [Context, u, Function.update] using hc
  have hua : u.regs 60 = k.val + 1 := by simp [u, hk, hone]
  have hl := HadamardFactorLoad.load_run (s.factor k) cs u hu.1 hua hu.2.2.1 hcs
  have hctx := HadamardFactorLoad.load_context s (s.factor k) cs u hu hua hcs
  have h60 := run_regs_frame HadamardFactorLoad.load 60 (by decide) u
  have h59 := run_regs_frame HadamardFactorLoad.load 59 (by decide) u
  have h61 := run_regs_frame HadamardFactorLoad.load 61 (by decide) u
  have h24 := run_lists_frame HadamardFactorLoad.load 24 (by decide) u
  dsimp only [u] at hl hctx h60 h59 h61 h24
  simp only [factorBody, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hv : (HadamardFactorLoad.load.run
    (setReg st 60 (st.regs 59 + st.regs 61))).1 = v at *
  have hp := pair_run (TestRandomness.productDegree_le k) s (s.factor k) v hctx
    (h60.trans hua) hl.1
  have hpctx := context_frame pair pair_stable s v hctx
  have hp59 := run_regs_frame pair 59 (by decide) v
  have hp61 := run_regs_frame pair 61 (by decide) v
  have hp25 := run_lists_frame pair 25 (by decide) v
  generalize hw : (pair.run v).1 = w at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Context, Function.update] using hpctx
  · simp [Function.update, hp59, hp61, h59, h61, hk, hone]
  · simpa [Function.update] using hp61.trans (h61.trans hone)
  · simpa using hp25.trans hl.2.2
  · simp only [setReg_lists, hp, h24, setReg_lists, factorLabels,
      ComputableHadamardTest.productQuery, ComputableHadamardTest.factorQuery,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

/-- The work cursor and output prefix after exactly `j` iterations. -/
def FactorInvariant (s : TestRandomness t r) (old : List ℕ) (j : ℕ)
    (st : State 80 32) : Prop :=
  Context s st ∧ st.regs 59 = j ∧ st.regs 61 = 1 ∧
    st.lists 25 = (factorCodes s).drop j ∧
    st.lists 24 = (factorPrefix s j).reverse ++ old

theorem factorBody_invariant (s : TestRandomness t r) (old : List ℕ) (j : ℕ)
    (st : State 80 32) (hj : j < r - 1) (hi : FactorInvariant s old j st) :
    FactorInvariant s old (j + 1) (factorBody.run st).1 := by
  have hcs : st.lists 25 =
      code (s.factor ⟨j, hj⟩) :: (factorCodes s).drop (j + 1) := by
    rw [hi.2.2.2.1, factorCodes_drop s j hj]
  have hs := factorBody_step s ⟨j, hj⟩ ((factorCodes s).drop (j + 1)) st
    hi.1 hi.2.1 hi.2.2.1 hcs
  generalize hu : (factorBody.run st).1 = u at *
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  rw [hs.2.2.2.2, hi.2.2.2.2, factorPrefix_succ s j hj,
    List.reverse_append, List.append_assoc]

def factorInit : Stmt 80 32 :=
  .seq (.copy 23 25) (.seq (.assign 59 (.const 0))
    (.seq (.assign 61 (.const 1)) (.assign 58 (.sub 56 61))))

theorem factorInit_run (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    FactorInvariant s (st.lists 24) 0 (factorInit.run st).1 ∧
      (factorInit.run st).1.regs 58 = r - 1 := by
  have hctx := context_frame factorInit (by decide) s st hc
  refine ⟨⟨hctx, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [factorInit, Stmt.run, Expr.eval, Function.update, factorPrefix, hc.2.1,
      hc.2.2.2.2.2.2]

def factorLoop : Stmt 80 32 := .seq factorInit (.loop 58 factorBody)

theorem factorLoop_run (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    Context s (factorLoop.run st).1 ∧
      (factorLoop.run st).1.lists 24 =
        (factorPrefix s (r - 1)).reverse ++ st.lists 24 := by
  have hi := factorInit_run s st hc
  simp only [factorLoop, run_seq_fst, run_loop_fst]
  generalize hu : (factorInit.run st).1 = u at *
  rw [hi.2]
  have hout := iterate_inv factorBody.run (Nat.size (r - 1) + 1) (r - 1)
    (FactorInvariant s (st.lists 24)) (fun j v hj hv => factorBody_invariant s _ j v hj hv)
    u hi.1
  exact ⟨hout.1, hout.2.2.2.2⟩

end PCP.Lang.HadamardRow
