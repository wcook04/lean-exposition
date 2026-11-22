import PCP.Complexity.HadamardLabelCost
import PCP.Complexity.LangQueryTupleConcat

/-!
# Actual query construction for the difference-consistency branch

The common homogeneous label is computed from stored coordinate bits, packed
with the production coefficient codec, and used at all three physical addresses.
The paired point is computed arithmetically from the two sampled point codes.
-/

namespace PCP.Lang.DifferenceQueries

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex ThreeColorVerifier

variable {t : ℕ}

def homogeneous : Stmt 80 32 := BooleanLabelConstructors.homogeneous.rename
  (Fin.castLE (by decide)) (Fin.castLE (by decide))

def pack : Stmt 80 32 := .seq (.copy 5 0)
  (.seq HadamardLabel.decode (.assign 63 (.var 1)))

/-- Source registers: point codes 57/58, vertex/pair cardinalities 59/60,
coefficient cardinalities 61/62, and computed common label code 63. -/
def addresses : Stmt 80 32 :=
  .seq (.assign 0 (.mul 59 62)) (.seq (.assign 1 (.mul 60 61))
  (.seq (.assign 0 (.add 0 1)) (.seq (.assign 1 (.mul 59 58))
  (.seq (.assign 1 (.add 57 1)) (.seq (.assign 1 (.mul 62 1))
  (.seq (.assign 1 (.add 63 1)) (.seq (.assign 64 (.add 0 1))
  (.seq (.assign 65 (.mul 62 57)) (.seq (.assign 65 (.add 63 65))
  (.seq (.assign 66 (.mul 62 58)) (.assign 66 (.add 63 66))))))))))))

def emit : Stmt 80 32 := .seq addresses
  (.seq (.push 24 64) (.seq (.push 24 65) (.push 24 66)))

def program : Stmt 80 32 := .seq (.copy 7 24) (.seq (.assign 56 (.const 3))
  (.seq homogeneous (.seq pack (.seq emit (.rev 24)))))

def differenceAddress (A B C1 C3 x y z : ℕ) : ℕ := A * C3 + B * C1 + (z + C3 * (x + A * y))

theorem emit_run (st : State 80 32) :
    (emit.run st).1.lists 24 =
      [st.regs 63 + st.regs 62 * st.regs 58, st.regs 63 + st.regs 62 * st.regs 57,
        differenceAddress (st.regs 59) (st.regs 60) (st.regs 61) (st.regs 62)
          (st.regs 57) (st.regs 58) (st.regs 63)] ++ st.lists 24 := by
  simp [emit, addresses, Stmt.run, Expr.eval, Function.update, differenceAddress]

theorem homogeneous_result (st : State 80 32) :
    ((homogeneous.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      (homogeneous.run st).2) = BooleanLabelConstructors.homogeneous.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  unfold homogeneous
  exact BooleanLabelConstructors.homogeneous.run_rename
    (Fin.castLE (by decide : 57 ≤ 80)) (Fin.castLE (by decide : 20 ≤ 32))
    (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem homogeneous_run (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = 3) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).1.lists 5 = BooleanCoefficientList.encode
      (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 3) w) := by
  have h := BooleanLabelConstructors.homogeneous_run (by decide : 1 ≤ 3) w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht hd he hw
  rw [← homogeneous_result st] at h
  simpa only [State.restrict_lists,
    show Fin.castLE (by decide : 20 ≤ 32) (5 : Fin 20) = (5 : Fin 32) from rfl] using h

theorem homogeneous_reg (i : Fin 80) (hi : 57 ≤ i.val) (st : State 80 32) :
    (homogeneous.run st).1.regs i = st.regs i := by
  unfold homogeneous
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem homogeneous_list (L : Fin 32) (hL : 20 ≤ L.val) (st : State 80 32) :
    (homogeneous.run st).1.lists L = st.lists L := by
  unfold homogeneous
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem pack_run {r : ℕ} (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists 5 = BooleanCoefficientList.encode p) :
    (pack.run st).1.regs 63 = HadamardLabel.code p := by
  have h := HadamardLabel.decode_run p (setList st 0 (st.lists 5)) (by simpa using hp)
  simp only [pack, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  exact h

theorem pack_reg (i : Fin 80) (hi : 57 ≤ i.val) (hi' : i.val ≤ 62) (st : State 80 32) :
    (pack.run st).1.regs i = st.regs i := by
  have h : i ∉ pack.regWrites := by
    simp only [pack, HadamardLabel.decode, Stmt.regWrites, Stmt.regWrites_rename,
      List.mem_append, List.not_mem_nil, false_or, List.mem_map, List.mem_singleton]
    rintro (⟨j, _, hj⟩ | hj)
    · have := congrArg Fin.val hj
      simp only [HadamardLabel.decodeRegs, Fin.val_castLE] at this
      omega
    · subst i
      norm_num at hi'
  exact run_regs_frame pack i h st

theorem pack_list (st : State 80 32) : (pack.run st).1.lists 24 = st.lists 24 := by
  apply run_lists_frame
  simp only [pack, HadamardLabel.decode, Stmt.listWrites, Stmt.listWrites_rename,
    List.mem_append, List.mem_singleton, List.mem_map, List.not_mem_nil, or_false]
  rintro (h | ⟨i, _, h⟩) <;> cases h

/-- The complete branch computes the label and all three numeric addresses itself. -/
theorem program_run (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    let z := HadamardLabel.code
      (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 3) w)
    (program.run st).1.lists 24 =
      [differenceAddress (st.regs 59) (st.regs 60) (st.regs 61) (st.regs 62)
        (st.regs 57) (st.regs 58) z,
        z + st.regs 62 * st.regs 57, z + st.regs 62 * st.regs 58] := by
  let s := setReg (setList st 24 []) 56 3
  have hh := homogeneous_run w s (by simpa [s, Function.update] using ht)
    (by simp [s, Function.update]) (by simpa [s, Function.update] using he)
    (by simpa [s, Function.update] using hw)
  have hsreg (i : Fin 80) (hi : 57 ≤ i.val) : (homogeneous.run s).1.regs i = st.regs i := by
    have hi56 : i ≠ 56 := by intro h; subst i; norm_num at hi
    simpa [s, hi56] using homogeneous_reg i hi s
  have hslist : (homogeneous.run s).1.lists 24 = [] := by
    simpa [s] using homogeneous_list 24 (by decide) s
  generalize hu : (homogeneous.run s).1 = u at *
  have hp := pack_run _ u hh
  have hplist := (pack_list u).trans hslist
  have hpreg (i : Fin 80) (hi : 57 ≤ i.val) (hi' : i.val ≤ 62) :
      (pack.run u).1.regs i = st.regs i := (pack_reg i hi hi' u).trans (hsreg i hi)
  generalize hv : (pack.run u).1 = v at *
  have hem := emit_run v
  rw [hp, hplist, hpreg 57 (by decide) (by decide), hpreg 58 (by decide) (by decide),
    hpreg 59 (by decide) (by decide), hpreg 60 (by decide) (by decide),
    hpreg 61 (by decide) (by decide), hpreg 62 (by decide) (by decide)] at hem
  simp only [program, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval, he]
  dsimp only [s] at hu
  rw [hu, hv, run_rev_fst]
  simpa [Function.update] using congrArg List.reverse hem

theorem color_address {F : Type*} {q n m c : ℕ} (eF : F ≃ Fin q)
    (a : Fin n → F) (p : Coefficients t 3) :
    (ThreeColorQueryIndex.equiv (n := n) (m := m) (c := c) eF
      (coefficientEquiv t 1) (coefficientEquiv t 3) (.color a p)).val =
      HadamardLabel.code p + 2 ^ dimension t 3 *
        (ThreeColorQueryIndex.vertexIndex eF n a).val := rfl

theorem difference_address {F : Type*} {q n m c : ℕ} (eF : F ≃ Fin q)
    (a b : Fin n → F) (p : Coefficients t 3) :
    (ThreeColorQueryIndex.equiv (n := n) (m := m) (c := c) eF
      (coefficientEquiv t 1) (coefficientEquiv t 3) (.difference (Sum.elim a b) p)).val =
      differenceAddress (q ^ n) (q ^ (n + n)) (2 ^ dimension t 1) (2 ^ dimension t 3)
        (ThreeColorQueryIndex.vertexIndex eF n a).val (ThreeColorQueryIndex.vertexIndex eF n b).val
        (HadamardLabel.code p) := by
  change q ^ n * 2 ^ dimension t 3 + q ^ (n + n) * 2 ^ dimension t 1 +
    (HadamardLabel.code p + 2 ^ dimension t 3 *
      (ThreeColorQueryIndex.pairIndex eF n (Sum.elim a b)).val) = _
  rw [QueryAddress.pairIndex_sum]
  rfl

/-- Exact production addresses in the original difference-check query order. -/
theorem program_queries {F : Type*} {q n m c : ℕ} (eF : F ≃ Fin q)
    (a b : Fin n → F) (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val))
    (ha : st.regs 57 = (ThreeColorQueryIndex.vertexIndex eF n a).val)
    (hb : st.regs 58 = (ThreeColorQueryIndex.vertexIndex eF n b).val)
    (hA : st.regs 59 = q ^ n) (hB : st.regs 60 = q ^ (n + n))
    (hC1 : st.regs 61 = 2 ^ dimension t 1) (hC3 : st.regs 62 = 2 ^ dimension t 3) :
    (program.run st).1.lists 24 =
      (ComputableBinaryDifferenceConsistency.queries (by decide : 1 ≤ 3) a b w).map
        (fun z => (ThreeColorQueryIndex.equiv (m := m) (c := c) eF
          (coefficientEquiv t 1) (coefficientEquiv t 3) (differenceCheckQuery z)).val) := by
  rw [program_run w st ht he hw]
  simp only [ha, hb, hA, hB, hC1, hC3, ComputableBinaryDifferenceConsistency.queries,
    List.map_cons, List.map_nil, differenceCheckQuery, color_address, difference_address]

end PCP.Lang.DifferenceQueries
