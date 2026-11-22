import PCP.Complexity.GridBasisCoordinateCost
import PCP.Complexity.GridBasisCoordinateSemantics

/-!
# A stored-vector program for tensor Lagrange basis evaluation

The program consumes working copies of the point and grid-node coordinate lists.
Every coordinate uses the uniform Lagrange loop, and actual field multiplications
accumulate their product. The original coordinate lists remain available.
-/

namespace PCP.Lang.GridTensor

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t h : ℕ} [NeZero t]

def basis : Stmt 50 16 :=
  GridBasisCoordinate.program.rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def multiply : Stmt 50 16 :=
  (binary .mul).rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def basisCall : Stmt 50 16 :=
  .seq (.assign 24 (.var 44)) (.seq (.assign 32 (.var 45)) basis)

def multiplyCall : Stmt 50 16 :=
  .seq (.assign 20 (.var 44)) (.seq (.assign 24 (.var 40))
    (.seq (.assign 25 (.var 2)) (.seq multiply (.assign 40 (.var 26)))))

def body : Stmt 50 16 :=
  .seq (.pop 14 0 42) (.seq (.pop 15 3 42) (.seq basisCall multiplyCall))

def program : Stmt 50 16 :=
  .seq (.copy 12 14) (.seq (.copy 13 15)
    (.seq (.len 12 41) (.seq (.assign 40 (.const 1)) (.loop 41 body))))

def Context (t h : ℕ) [NeZero t] (st : State 50 16) : Prop :=
  st.regs 44 = t ∧ st.regs 45 = h ∧
  st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

def pointCodes (xs : List (BinaryMaterializedField.Element t × Fin h)) : List ℕ :=
  xs.map (fun p => (fieldEquiv t p.1).val)

def nodeCodes (xs : List (BinaryMaterializedField.Element t × Fin h)) : List ℕ :=
  xs.map (fun p => p.2.val)

def value (xs : List (BinaryMaterializedField.Element t × Fin h)) :
    BinaryMaterializedField.Element t :=
  (xs.map (fun p => GridBasisCoordinate.value p.1 p.2.val h)).prod

def Inv (xs : List (BinaryMaterializedField.Element t × Fin h))
    (acc : BinaryMaterializedField.Element t) (st : State 50 16) : Prop :=
  Context t h st ∧ st.regs 40 = (fieldEquiv t acc).val ∧
  st.lists 14 = pointCodes xs ∧ st.lists 15 = nodeCodes xs

theorem basis_result (st : State 50 16) :
    (((basis.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))),
      (basis.run st).2) = GridBasisCoordinate.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  GridBasisCoordinate.program.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem multiply_result (st : State 50 16) :
    (((multiply.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))),
      (multiply.run st).2) = (binary .mul).run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  (binary .mul).run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem basisCall_run (z : BinaryMaterializedField.Element t) (k : Fin h) (hh : h ≤ 2 ^ t)
    (st : State 50 16) (hc : Context t h st)
    (h0 : st.regs 0 = (fieldEquiv t z).val) (h3 : st.regs 3 = k.val) :
    (basisCall.run st).1.regs 2 = (fieldEquiv t (GridBasisCoordinate.value z k.val h)).val := by
  let s := setReg (setReg st 24 (st.regs 44)) 32 (st.regs 45)
  have hr := basis_result s
  have hp := GridBasisCoordinate.program_run z k.val h hh (lt_of_lt_of_le k.isLt hh)
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [s, Function.update] using h0) (by simpa [s, Function.update] using h3)
    (by simpa [s, Function.update] using hc.1) (by simpa [s] using hc.2.1)
    hc.2.2.1 hc.2.2.2
  have ho := congrArg (fun p : State 40 12 × ℕ => p.1.regs 2) hr
  change (basis.run s).1.regs 2 = _ at ho
  rw [basisCall, run_seq_fst, run_assign_fst, run_seq_fst, run_assign_fst]
  exact ho.trans hp.2.2.1

theorem multiplyCall_run (a b : BinaryMaterializedField.Element t)
    (st : State 50 16) (hc : Context t h st)
    (ha : st.regs 40 = (fieldEquiv t a).val) (hb : st.regs 2 = (fieldEquiv t b).val) :
    (multiplyCall.run st).1.regs 40 = (fieldEquiv t (a * b)).val := by
  let s := setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 40)) 25 (st.regs 2)
  have hr := multiply_result s
  have hp := binary_run_field .mul
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) a b
    (by simpa [s, Function.update] using hc.1) (by simpa [s, Function.update] using ha)
    (by simpa [s] using hb) hc.2.2.1 hc.2.2.2
  have ho := congrArg (fun p : State 36 11 × ℕ => p.1.regs 26) hr
  simp only [State.restrict_regs,
    show Fin.castLE (by decide : 36 ≤ 50) (26 : Fin 36) = (26 : Fin 50) from rfl] at ho
  simp only [multiplyCall, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, dite_true]
  dsimp only [s] at ho hp
  rw [ho, hp]
  rfl

theorem basisCall_context (st : State 50 16) (hc : Context t h st) :
    Context t h (basisCall.run st).1 := by
  exact ⟨(run_regs_frame _ _ (by decide) _).trans hc.1,
    (run_regs_frame _ _ (by decide) _).trans hc.2.1,
    (run_lists_frame _ _ (by decide) _).trans hc.2.2.1,
    (run_lists_frame _ _ (by decide) _).trans hc.2.2.2⟩

theorem multiplyCall_context (st : State 50 16) (hc : Context t h st) :
    Context t h (multiplyCall.run st).1 := by
  exact ⟨(run_regs_frame _ _ (by decide) _).trans hc.1,
    (run_regs_frame _ _ (by decide) _).trans hc.2.1,
    (run_lists_frame _ _ (by decide) _).trans hc.2.2.1,
    (run_lists_frame _ _ (by decide) _).trans hc.2.2.2⟩

set_option maxHeartbeats 500000 in
-- The kernel checks two nested arithmetic subprogram transports in one body trace.
theorem body_inv (p : BinaryMaterializedField.Element t × Fin h)
    (xs : List (BinaryMaterializedField.Element t × Fin h))
    (acc : BinaryMaterializedField.Element t)
    (hh : h ≤ 2 ^ t) (st : State 50 16) (hi : Inv (p :: xs) acc st) :
    Inv xs (acc * GridBasisCoordinate.value p.1 p.2.val h) (body.run st).1 := by
  let s := setReg (setReg (setList st 14 (pointCodes xs)) 0 (fieldEquiv t p.1).val) 42 1
  let u := setReg (setReg (setList s 15 (nodeCodes xs)) 3 p.2.val) 42 1
  have hs : ((Stmt.pop 14 0 42).run st).1 = s := by
    simp [Stmt.run, hi.2.2.1, pointCodes, s]
  have hu : ((Stmt.pop 15 3 42).run s).1 = u := by
    simp [Stmt.run, s, hi.2.2.2, nodeCodes, Function.update, u]
  have huc : Context t h u := by simpa [Context, u, s, Function.update] using hi.1
  have hu0 : u.regs 0 = (fieldEquiv t p.1).val := by simp [u, s, Function.update]
  have hu3 : u.regs 3 = p.2.val := by simp [u, Function.update]
  have hv2 := basisCall_run p.1 p.2 hh u huc hu0 hu3
  have hvc := basisCall_context u huc
  have hv40 := run_regs_frame basisCall 40 (by decide) u
  have hv14 := run_lists_frame basisCall 14 (by decide) u
  have hv15 := run_lists_frame basisCall 15 (by decide) u
  simp only [body, run_seq_fst, hs, hu]
  generalize hv : (basisCall.run u).1 = v at *
  have hvacc : v.regs 40 = (fieldEquiv t acc).val := by
    rw [hv40]
    simpa [u, s, Function.update] using hi.2.1
  refine ⟨multiplyCall_context v hvc, multiplyCall_run acc _ v hvc hvacc hv2, ?_, ?_⟩
  · rw [run_lists_frame multiplyCall 14 (by decide), hv14]
    simp [u, s, Function.update]
  · rw [run_lists_frame multiplyCall 15 (by decide), hv15]
    simp [u]

/-- The actual counted loop multiplies exactly the supplied coordinate factors. -/
theorem iterate_run (xs : List (BinaryMaterializedField.Element t × Fin h))
    (acc : BinaryMaterializedField.Element t) (hh : h ≤ 2 ^ t) (c : ℕ)
    (st : State 50 16) (hi : Inv xs acc st) :
    Inv (h := h) [] (acc * value xs) (iterate body.run c xs.length st).1 := by
  induction xs generalizing acc st with
  | nil => simpa [value, iterate] using hi
  | cons p xs ih =>
    rw [List.length_cons, iterate_succ_fst]
    have hh' := ih _ _ (body_inv p xs acc hh st hi)
    simpa [value, mul_assoc] using hh'

theorem program_run (xs : List (BinaryMaterializedField.Element t × Fin h))
    (hh : h ≤ 2 ^ t) (st : State 50 16) (hc : Context t h st)
    (hx : st.lists 12 = pointCodes xs) (hk : st.lists 13 = nodeCodes xs) :
    (program.run st).1.regs 40 = (fieldEquiv t (value xs)).val ∧
      Context t h (program.run st).1 := by
  let s := setReg (setReg (setList (setList st 14 (st.lists 12)) 15 (st.lists 13))
    41 (st.lists 12).length) 40 1
  have hi : Inv xs 1 s := by
    refine ⟨by simpa [Context, s, Function.update] using hc, ?_, ?_, ?_⟩
    · change 1 = (fieldEquiv t (1 : BinaryMaterializedField.Element t)).val
      rw [code_one]
    · simpa [s, Function.update] using hx
    · simpa [s] using hk
  have hl : s.regs 41 = xs.length := by simp [s, Function.update, hx, pointCodes]
  have hout := iterate_run xs 1 hh (Nat.size xs.length + 1) s hi
  have hr : (program.run st).1 = (iterate body.run (Nat.size xs.length + 1) xs.length s).1 := by
    simp only [program, run_seq_fst, run_copy_fst, run_len_fst, run_assign_fst,
      Expr.eval, run_loop_fst]
    change (iterate body.run (Nat.size (s.regs 41) + 1) (s.regs 41) s).1 = _
    rw [hl]
  rw [hr]
  exact ⟨by simpa only [one_mul] using hout.2.1, hout.1⟩

end PCP.Lang.GridTensor
