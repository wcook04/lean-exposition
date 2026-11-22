/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelTransformCost
import PCP.Complexity.BooleanAffineList

/-!
# Constant and homogeneous labels at arbitrary degree bounds

Small source words are constructed directly and padded by the concrete embedding
program. Every output uses the exact production coefficient order.
-/

namespace PCP.Lang.BooleanLabelConstructors

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList

variable {t r : ℕ}

theorem embed_homogeneous (hr : 1 ≤ r) (w : Fin t → ZMod 2) :
    BooleanCoefficientArithmetic.embed hr
      (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 1) w) =
    BooleanCoefficientArithmetic.homogeneousIndex hr w := by
  rw [← BooleanCoefficientRecovery.recover_evaluate
    (BooleanCoefficientArithmetic.embed hr
      (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 1) w)),
    ← BooleanCoefficientRecovery.recover_evaluate
      (BooleanCoefficientArithmetic.homogeneousIndex hr w)]
  congr 1
  funext x
  simp only [BooleanCoefficientArithmetic.evaluate_embed,
    BooleanCoefficientArithmetic.evaluate_homogeneousIndex]

theorem encode_constant_zero (z : ZMod 2) :
    encode (BooleanCoefficientArithmetic.constant (t := t) (r := 0) z) = [z.val] := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    have hn0 : n = 0 := by simpa using hn'
    subst n
    simp only [encode, List.getElem_ofFn, BooleanCoefficientIndex.wordEquiv_apply]
    have hs : (((BooleanCoefficientIndex.monomialEquiv t 0).symm
      ⟨0, by simp⟩).val) = ∅ := by
      apply Finset.card_eq_zero.mp
      exact Nat.eq_zero_of_le_zero ((BooleanCoefficientIndex.monomialEquiv t 0).symm
        ⟨0, by simp⟩).property
    simp only [BooleanCoefficientArithmetic.constant, hs, ite_true, List.getElem_cons_zero]

theorem embed_constant (z : ZMod 2) :
    BooleanCoefficientArithmetic.embed (Nat.zero_le r)
      (BooleanCoefficientArithmetic.constant (t := t) (r := 0) z) =
    BooleanCoefficientArithmetic.constant (r := r) z := by
  rw [← BooleanCoefficientRecovery.recover_evaluate
    (BooleanCoefficientArithmetic.embed (Nat.zero_le r)
      (BooleanCoefficientArithmetic.constant (t := t) (r := 0) z)),
    ← BooleanCoefficientRecovery.recover_evaluate
      (BooleanCoefficientArithmetic.constant (t := t) (r := r) z)]
  congr 1
  funext x
  simp

def homogeneousPrepare : Stmt 57 20 :=
  .seq (.copy 17 13) (.seq (.assign 53 (.const 0))
    (.seq (.push 13 53) (.assign 54 (.const 1))))

theorem homogeneousPrepare_run (w : Fin t → ZMod 2) (st : State 57 20)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneousPrepare.run st).1.lists 13 =
      encode (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 1) w) ∧
    (homogeneousPrepare.run st).1.regs 54 = 1 := by
  rw [BooleanAffineList.encode_homogeneous]
  simp [homogeneousPrepare, Stmt.run, Expr.eval, Function.update, hw]

/-- Inputs: width `20`, target degree `56`, coordinate bits `17`, and empty `7`.
Output list `5` is the homogeneous label in the requested coefficient space. -/
def homogeneous : Stmt 57 20 := .seq homogeneousPrepare BooleanLabelTransform.embed

theorem homogeneous_run (hr : 1 ≤ r) (w : Fin t → ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).1.lists 5 =
      encode (BooleanCoefficientArithmetic.homogeneousIndex hr w) := by
  have hp := homogeneousPrepare_run w st hw
  have hs20 := run_regs_frame homogeneousPrepare 20 (by decide) st
  have hs56 := run_regs_frame homogeneousPrepare 56 (by decide) st
  have hs7 := run_lists_frame homogeneousPrepare 7 (by decide) st
  simp only [homogeneous, run_seq_fst]
  generalize hs : (homogeneousPrepare.run st).1 = s at *
  rw [BooleanLabelTransform.embed_run hr _ s (hs20.trans ht) hp.2
    (hs56.trans hd) (hs7.trans he) hp.1, embed_homogeneous]

def constantPrepare : Stmt 57 20 :=
  .seq (.copy 7 13) (.seq (.push 13 51) (.assign 54 (.const 0)))

theorem constantPrepare_run (z : ZMod 2) (st : State 57 20)
    (hz : st.regs 51 = z.val) (he : st.lists 7 = []) :
    (constantPrepare.run st).1.lists 13 =
      encode (BooleanCoefficientArithmetic.constant (t := t) (r := 0) z) ∧
    (constantPrepare.run st).1.regs 54 = 0 := by
  rw [encode_constant_zero]
  simp [constantPrepare, Stmt.run, Expr.eval, Function.update, hz, he]

/-- Inputs: width `20`, target degree `56`, bit `51`, and empty list `7`.
Output list `5` is the constant coefficient label. -/
def constant : Stmt 57 20 := .seq constantPrepare BooleanLabelTransform.embed

theorem constant_run (z : ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (hz : st.regs 51 = z.val)
    (he : st.lists 7 = []) :
    (constant.run st).1.lists 5 =
      encode (BooleanCoefficientArithmetic.constant (t := t) (r := r) z) := by
  have hp := constantPrepare_run (t := t) z st hz he
  have hs20 := run_regs_frame constantPrepare 20 (by decide) st
  have hs56 := run_regs_frame constantPrepare 56 (by decide) st
  have hs7 := run_lists_frame constantPrepare 7 (by decide) st
  simp only [constant, run_seq_fst]
  generalize hs : (constantPrepare.run st).1 = s at *
  rw [BooleanLabelTransform.embed_run (Nat.zero_le r) _ s (hs20.trans ht) hp.2
    (hs56.trans hd) (hs7.trans he) hp.1, embed_constant]

theorem homogeneous_frame (st : State 57 20) :
    (homogeneous.run st).1.regs 20 = st.regs 20 ∧
    (homogeneous.run st).1.regs 56 = st.regs 56 ∧
    (homogeneous.run st).1.lists 7 = st.lists 7 ∧
    (homogeneous.run st).1.lists 17 = st.lists 17 := by
  exact ⟨run_regs_frame homogeneous 20 (by decide) st,
    run_regs_frame homogeneous 56 (by decide) st,
    run_lists_frame homogeneous 7 (by decide) st,
    run_lists_frame homogeneous 17 (by decide) st⟩

theorem constant_frame (st : State 57 20) :
    (constant.run st).1.regs 20 = st.regs 20 ∧
    (constant.run st).1.regs 56 = st.regs 56 ∧
    (constant.run st).1.regs 51 = st.regs 51 ∧
    (constant.run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_regs_frame constant 20 (by decide) st,
    run_regs_frame constant 56 (by decide) st,
    run_regs_frame constant 51 (by decide) st,
    run_lists_frame constant 7 (by decide) st⟩

end PCP.Lang.BooleanLabelConstructors
