import PCP.Complexity.BinaryFieldCodeCost
import PCP.Complexity.BinaryFieldCodeSemantics

/-!
# The cubic colour constraint on natural field codes

Two concrete multiplications and one addition compute `x^3-1`. In the binary
field the final subtraction is addition. The source code is saved and restored.
-/

namespace PCP.Lang.BinaryFieldCode

open PCP.Algebraic BinaryField

/-- Square the current input while retaining its original code in register 24. -/
def square : Stmt 36 11 := .seq (.assign 25 (.var 24)) (binary .mul)

theorem square_run {t : ℕ} [NeZero t] (st : State 36 11)
    (a : BinaryMaterializedField.Element t) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (square.run st).1.regs 26 = (fieldEquiv t (a * a)).val := by
  rw [square, run_seq_fst, run_assign_fst]
  apply binary_run_field .mul _ a a
  · simpa [Function.update] using h20
  · simpa [Function.update] using h24
  · simpa [Expr.eval] using h24
  · exact hm
  · exact he

/-- Multiply the square by the retained source value. -/
def cube : Stmt 36 11 :=
  .seq square (.seq (.assign 25 (.var 26)) (binary .mul))

theorem cube_run {t : ℕ} [NeZero t] (st : State 36 11)
    (a : BinaryMaterializedField.Element t) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (cube.run st).1.regs 26 = (fieldEquiv t (a ^ 3)).val := by
  have hs26 := square_run st a h20 h24 hm he
  have hs20 := run_regs_frame square 20 (by decide) st
  have hs24 := run_regs_frame square 24 (by decide) st
  have hs3 := run_lists_frame square 3 (by decide) st
  have hs7 := run_lists_frame square 7 (by decide) st
  rw [cube, run_seq_fst, run_seq_fst, run_assign_fst]
  generalize hu : (square.run st).1 = u at *
  have h := binary_run_field .mul (setReg u 25 (u.regs 26))
    a (a * a) (by simpa [Function.update] using hs20.trans h20)
    (by simpa [Function.update] using hs24.trans h24) (by simpa using hs26)
    (hs3.trans hm) (hs7.trans he)
  have heq : Op.fieldEval .mul a (a * a) = a ^ 3 := by
    change a * (a * a) = a ^ 3
    ring
  rw [heq] at h
  exact h

/-- Code one is added after the cubic computation, then the input register is restored. -/
def cubicTail : Stmt 36 11 :=
  .seq (.assign 24 (.var 26)) (.seq (.assign 25 (.const 1))
    (.seq (binary .add) (.assign 24 (.var 27))))

def cubeMinusOne : Stmt 36 11 :=
  .seq (.assign 27 (.var 24)) (.seq cube cubicTail)

theorem cubeMinusOne_run {t : ℕ} [NeZero t] (st : State 36 11)
    (a : BinaryMaterializedField.Element t) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (cubeMinusOne.run st).1.regs 26 = (fieldEquiv t (a ^ 3 - 1)).val := by
  let s := setReg st 27 (st.regs 24)
  have hs20 : s.regs 20 = t := by simp [s, Function.update, h20]
  have hs24 : s.regs 24 = (fieldEquiv t a).val := by simp [s, Function.update, h24]
  have hc := cube_run s a hs20 hs24 hm he
  have hu20 := (run_regs_frame cube 20 (by decide) s).trans hs20
  have hu3 := (run_lists_frame cube 3 (by decide) s).trans hm
  have hu7 := (run_lists_frame cube 7 (by decide) s).trans he
  simp only [cubeMinusOne, run_seq_fst, run_assign_fst, Expr.eval]
  dsimp only [s] at hc hu20 hu3 hu7
  generalize hu : (cube.run (setReg st 27 (st.regs 24))).1 = u at *
  let v := setReg (setReg u 24 (u.regs 26)) 25 1
  have h := binary_run_field .add v (a ^ 3) 1
    (by change u.regs 20 = t; exact hu20)
    (by change u.regs 26 = _; exact hc)
    (by change 1 = WordCodec.value (encode (BinaryWordMaterialization.one t))
        exact (BinaryFieldWordCode.value_encode_one t
          (Nat.pos_of_ne_zero (NeZero.ne t))).symm)
    hu3 hu7
  simp only [cubicTail, run_seq_fst, run_assign_fst, Expr.eval]
  change (setReg ((binary .add).run v).1 24 (((binary .add).run v).1.regs 27)).regs 26 = _
  simpa only [setReg_regs, Function.update_of_ne (by decide : (26 : Fin 36) ≠ 24),
    Op.fieldEval, sub_eq_add_neg, show -(1 : BinaryMaterializedField.Element t) = 1 from rfl]
    using h

theorem cubeMinusOne_frame (st : State 36 11) :
    (cubeMinusOne.run st).1.regs 20 = st.regs 20 ∧
    (cubeMinusOne.run st).1.regs 24 = st.regs 24 ∧
    (cubeMinusOne.run st).1.lists 3 = st.lists 3 ∧
    (cubeMinusOne.run st).1.lists 7 = st.lists 7 := by
  refine ⟨run_regs_frame _ _ (by decide) _, ?_,
    run_lists_frame _ _ (by decide) _, run_lists_frame _ _ (by decide) _⟩
  have hc := run_regs_frame cube 27 (by decide) (setReg st 27 (st.regs 24))
  have hb := run_regs_frame (binary .add) 27 (by decide)
    (setReg (setReg (cube.run (setReg st 27 (st.regs 24))).1 24
      ((cube.run (setReg st 27 (st.regs 24))).1.regs 26)) 25 1)
  simp only [cubeMinusOne, cubicTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  rw [hb]
  simpa [Function.update] using hc

end PCP.Lang.BinaryFieldCode
