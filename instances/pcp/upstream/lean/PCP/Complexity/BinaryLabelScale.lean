/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanAffineList
import PCP.Complexity.BinaryCubicQueryCost
import PCP.Algebraic.FieldQueryArithmetic

/-!
# Concrete transpose of binary field multiplication

The program visits the binary basis vectors, multiplies each by the supplied
scalar, and evaluates the stored homogeneous label. Output bits are materialized
in coordinate order. Field arithmetic and coefficient observations use the
already proved fixed-register kernels.
-/

namespace PCP.Lang.BinaryLabelScale

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode
open BinaryCubicObservation

variable {t : ℕ} [NeZero t]

def basis (i : Fin t) : BinaryMaterializedField.Element t :=
  (BinaryMaterializedField.coordinates t).symm (Pi.single i 1)

theorem basis_code (i : Fin t) : (fieldEquiv t (basis i)).val = 2 ^ i.val := by
  let n := BooleanCoefficientIndex.subsetCodeEquiv t {i}
  have hp : point t n = Pi.single i 1 := by
    funext j
    simp [point, n, BooleanCoefficientRecovery.indicator, Pi.single_apply, eq_comm]
  have he : basis i = (fieldEquiv t).symm n := by
    apply (BinaryMaterializedField.coordinates t).injective
    rw [basis, LinearEquiv.apply_symm_apply, ← point_fieldEquiv, Equiv.apply_symm_apply, hp]
  rw [he, Equiv.apply_symm_apply]
  exact BooleanAffineList.subsetCode_singleton i

def observeProduct : Stmt 52 16 := .seq mul52 observe

theorem observeProduct_run (a b : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hb : st.regs 25 = (fieldEquiv t b).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hw : st.lists 13 = encode (BooleanCoefficientArithmetic.homogeneousIndex
      (by decide : 1 ≤ 1) w)) :
    (observeProduct.run st).1.regs 46 =
      (BooleanCoefficientArithmetic.linearEncode (BinaryMaterializedField.coordinates t
        (a * b)) w).val := by
  have hp := mul52_run a b st ht ha hb hmod he
  have hs20 := run_regs_frame mul52 20 (by decide) st
  have hs12 := run_lists_frame mul52 12 (by decide) st
  have hs13 := run_lists_frame mul52 13 (by decide) st
  simp only [observeProduct, run_seq_fst]
  generalize hs : (mul52.run st).1 = s at *
  have h := observe_run (a * b) (BooleanCoefficientArithmetic.homogeneousIndex
    (by decide : 1 ≤ 1) w) s (hs20.trans ht) hp (hs12.trans hm) (hs13.trans hw)
  rw [BooleanCoefficientArithmetic.evaluate_homogeneousIndex] at h
  exact h

def kernelRegs : Fin 52 → Fin 54 := Fin.castLE (by decide)
def kernelLists : Fin 16 → Fin 18 := Fin.castLE (by decide)
def kernel : Stmt 54 18 := observeProduct.rename kernelRegs kernelLists

def Context (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) : Prop :=
  st.regs 20 = t ∧ st.regs 24 = (fieldEquiv t a).val ∧
    st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = [] ∧
    st.lists 12 = BooleanMask.masks t 1 ∧
    st.lists 13 = encode (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 1) w)

def bit (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2) (j : ℕ) : ℕ :=
  if hj : j < t then
    (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) a w ⟨j, hj⟩).val
  else 0

theorem bit_lt_two (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2) (j : ℕ) :
    bit a w j < 2 := by
  unfold bit
  split_ifs
  · exact ZMod.val_lt _
  · decide

theorem kernel_run (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) (j : ℕ) (hj : j < t)
    (hi : st.regs 25 = 2 ^ j) :
    (kernel.run st).1.regs 46 = bit a w j := by
  have h := congrArg (fun z : State 52 16 × ℕ => z.1.regs 46)
    (observeProduct.run_rename kernelRegs kernelLists (Fin.castLE_injective _)
      (Fin.castLE_injective _) st)
  have hh := h.trans (observeProduct_run a (basis ⟨j, hj⟩) w
    (st.restrict kernelRegs kernelLists) hc.1 hc.2.1
    (by rw [basis_code]; exact hi) hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  unfold kernel
  simpa only [State.restrict_regs, show kernelRegs 46 = (46 : Fin 54) from rfl,
    bit, dite_eq_left hj, FieldQueryArithmetic.scaleLabel, BooleanCoefficientArithmetic.linearEncode,
    basis] using hh

theorem kernel_reg (st : State 54 18) (i : Fin 54)
    (hi : i ∈ ([20, 24, 25, 52, 53] : List (Fin 54))) :
    (kernel.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem kernel_list (st : State 54 18) (i : Fin 18)
    (hi : i ∈ ([3, 7, 12, 13, 16, 17] : List (Fin 18))) :
    (kernel.run st).1.lists i = st.lists i := by
  apply run_lists_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def body : Stmt 54 18 :=
  .seq kernel (.seq (.push 16 46) (.assign 25 (.add 25 25)))

theorem body_step (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) (j : ℕ) (hj : j < t)
    (hi : st.regs 25 = 2 ^ j) :
    (body.run st).1.regs 25 = 2 ^ (j + 1) ∧
      (body.run st).1.lists 16 = bit a w j :: st.lists 16 := by
  have hr := kernel_run a w st hc j hj hi
  have hs25 := kernel_reg st 25 (by decide)
  have hs16 := kernel_list st 16 (by decide)
  simp only [body, run_seq_fst]
  generalize hs : (kernel.run st).1 = s at *
  simp [run_push_fst, run_assign_fst, Expr.eval, Function.update,
    hr, hs25, hs16, hi, pow_succ, Nat.mul_two]

theorem body_context (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) : Context a w (body.run st).1 := by
  unfold Context at hc ⊢
  have h20 := run_regs_frame body 20 (by decide) st
  have h24 := run_regs_frame body 24 (by decide) st
  have h3 := run_lists_frame body 3 (by decide) st
  have h7 := run_lists_frame body 7 (by decide) st
  have h12 := run_lists_frame body 12 (by decide) st
  have h13 := run_lists_frame body 13 (by decide) st
  rw [h20, h24, h3, h7, h12, h13]
  exact hc

/-- Traverse the binary basis in increasing coordinate order. -/
def tabulate : Stmt 54 18 :=
  .seq (.copy 7 16) (.seq (.assign 25 (.const 1)) (.seq (.loop 20 body) (.rev 16)))

theorem tabulate_run (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (hc : Context a w st) :
    (tabulate.run st).1.lists 16 = (List.range t).map (bit a w) := by
  let s := setReg (setList st 16 []) 25 1
  have hinit : Context a w s ∧ s.regs 25 = 2 ^ 0 ∧
      s.lists 16 = ((List.range 0).map (bit a w)).reverse := by
    simp [Context, s, Function.update, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
      hc.2.2.2.2.1, hc.2.2.2.2.2]
  have hout := iterate_inv body.run (Nat.size t + 1) t
    (fun j u => Context a w u ∧ u.regs 25 = 2 ^ j ∧
      u.lists 16 = ((List.range j).map (bit a w)).reverse)
    (by
      intro j u hj hu
      have hh := body_step a w u hu.1 j hj hu.2.1
      refine ⟨body_context a w u hu.1, hh.1, ?_⟩
      rw [hh.2, hu.2.2]
      simp [List.range_succ]) s hinit
  simp only [tabulate, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_fst, run_rev_fst, setReg_regs, setList_regs, Function.update,
    Fin.reduceEq, dite_false, hc.1, hc.2.2.2.1]
  change ((iterate body.run (Nat.size t + 1) t s).1.lists 16).reverse = _
  rw [hout.2.2, List.reverse_reverse]

theorem range_bits (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2) :
    (List.range t).map (bit a w) = List.ofFn fun i =>
      (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) a w i).val := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.length_ofFn] at hi'
    simp [bit, hi']

def masksLists : Fin 17 → Fin 18 := Fin.castLE (by decide)
def masks : Stmt 54 18 := BinaryCubicQueryLang.affineMasks.rename id masksLists

omit [NeZero t] in
theorem masks_run (st : State 54 18) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (masks.run st).1.lists 12 = BooleanMask.masks t 1 := by
  have h := congrArg (fun z : State 54 17 × ℕ => z.1.lists 12)
    (BinaryCubicQueryLang.affineMasks.run_rename id masksLists Function.injective_id
      (Fin.castLE_injective _) st)
  have hh := h.trans (BinaryCubicQueryLang.affineMasks_run
    (st.restrict id masksLists) ht he)
  unfold masks
  simpa only [State.restrict_lists, show masksLists 12 = (12 : Fin 18) from rfl] using hh

def prepare : Stmt 54 18 :=
  .seq masks (.seq (.copy 17 13) (.seq (.assign 53 (.const 0)) (.push 13 53)))

theorem prepare_context (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    Context a w (prepare.run st).1 := by
  have hm := masks_run st ht he
  have hs20 := run_regs_frame masks 20 (by decide) st
  have hs24 := run_regs_frame masks 24 (by decide) st
  have hs3 := run_lists_frame masks 3 (by decide) st
  have hs7 := run_lists_frame masks 7 (by decide) st
  have hs17 := run_lists_frame masks 17 (by decide) st
  simp only [prepare, run_seq_fst]
  generalize hs : (masks.run st).1 = s at *
  simp only [Context, BooleanAffineList.encode_homogeneous]
  simp [run_copy_fst, run_assign_fst, run_push_fst, Expr.eval, Function.update,
    hs20, ht, hs24, ha, hs3, hmod, hs7, he, hs17, hw, hm]

/-- Inputs: width `20`, scalar code `24`, modulus `3`, empty `7`, label bits `17`.
The materialized transposed label is returned in list `16`. -/
def scale : Stmt 54 18 := .seq prepare tabulate

theorem scale_run (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 54 18) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (scale.run st).1.lists 16 = List.ofFn fun i =>
      (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) a w i).val := by
  rw [scale, run_seq_fst, tabulate_run a w _ (prepare_context a w st ht ha hmod he hw)]
  exact range_bits a w

theorem scale_frame (st : State 54 18) :
    (scale.run st).1.regs 20 = st.regs 20 ∧
    (scale.run st).1.regs 24 = st.regs 24 ∧
    (scale.run st).1.lists 3 = st.lists 3 ∧
    (scale.run st).1.lists 7 = st.lists 7 ∧
    (scale.run st).1.lists 17 = st.lists 17 := by
  exact ⟨run_regs_frame scale 20 (by decide) st, run_regs_frame scale 24 (by decide) st,
    run_lists_frame scale 3 (by decide) st, run_lists_frame scale 7 (by decide) st,
    run_lists_frame scale 17 (by decide) st⟩

end PCP.Lang.BinaryLabelScale
