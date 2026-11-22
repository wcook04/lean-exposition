import PCP.Complexity.BinaryCubicCodeLang

/-!
# Charged cost of the cubic field constraint

All three arithmetic calls, source preservation, and inter-call assignments are
included. The complete `x^3-1` routine has quartic cost in the field bit width.
-/

namespace PCP.Lang.BinaryFieldCode

open PCP.Algebraic BinaryField

variable {t : ℕ} [NeZero t]

omit [NeZero t] in
private theorem size_code (a : BinaryMaterializedField.Element t) :
    Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt

omit [NeZero t] in
private theorem linear_quartic : t + 1 ≤ (t + 1) ^ 4 := by
  simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)

theorem square_cost (st : State 36 11) (a : BinaryMaterializedField.Element t)
    (h20 : st.regs 20 = t) (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (square.run st).2 ≤ 21000000 * (t + 1) ^ 4 := by
  let s := setReg st 25 (st.regs 24)
  have hc := binary_cost .mul (Nat.pos_of_ne_zero (NeZero.ne t)) s
    (fieldEquiv t a) (fieldEquiv t a) (by change st.regs 20 = t; exact h20)
    (by change st.regs 24 = _; exact h24) (by change st.regs 24 = _; exact h24) hm he
  have hs := size_code a
  have hlin := linear_quartic (t := t)
  rw [square, run_seq_snd]
  change Nat.size (st.regs 24) + Nat.size (st.regs 24) + 1 + (binary .mul |>.run s).2 + 1 ≤ _
  rw [h24]
  omega

theorem cube_cost (st : State 36 11) (a : BinaryMaterializedField.Element t)
    (h20 : st.regs 20 = t) (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (cube.run st).2 ≤ 43000000 * (t + 1) ^ 4 := by
  have hc1 := square_cost st a h20 h24 hm he
  have hs26 := square_run st a h20 h24 hm he
  have hs20 := (run_regs_frame square 20 (by decide) st).trans h20
  have hs24 := (run_regs_frame square 24 (by decide) st).trans h24
  have hs3 := (run_lists_frame square 3 (by decide) st).trans hm
  have hs7 := (run_lists_frame square 7 (by decide) st).trans he
  simp only [cube, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hu : (square.run st).1 = w at *
  let u := setReg w 25 (w.regs 26)
  have hc2 := binary_cost .mul (Nat.pos_of_ne_zero (NeZero.ne t)) u
    (fieldEquiv t a) (fieldEquiv t (a * a)) (by change w.regs 20 = t; exact hs20)
    (by change w.regs 24 = _; exact hs24)
    (by change w.regs 26 = _; exact hs26) hs3 hs7
  have hs := size_code (a * a)
  have hlin := linear_quartic (t := t)
  change (square.run st).2 + (Nat.size (w.regs 26) +
    Nat.size (w.regs 26) + 1 + ((binary .mul).run u).2 + 1) + 1 ≤ _
  rw [hs26]
  omega

theorem cubicTail_cost (st : State 36 11) (a saved : BinaryMaterializedField.Element t)
    (h20 : st.regs 20 = t) (h26 : st.regs 26 = (fieldEquiv t a).val)
    (h27 : st.regs 27 = (fieldEquiv t saved).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (cubicTail.run st).2 ≤ 21000000 * (t + 1) ^ 4 := by
  let u := setReg (setReg st 24 (st.regs 26)) 25 1
  have hu25 : u.regs 25 = (fieldEquiv t (1 : BinaryMaterializedField.Element t)).val := by
    change 1 = WordCodec.value (encode (BinaryWordMaterialization.one t))
    exact (BinaryFieldWordCode.value_encode_one t (Nat.pos_of_ne_zero (NeZero.ne t))).symm
  have hc := binary_cost .add (Nat.pos_of_ne_zero (NeZero.ne t)) u
    (fieldEquiv t a) (fieldEquiv t 1) (by change st.regs 20 = t; exact h20)
    (by change st.regs 26 = _; exact h26) hu25 hm he
  have hu27 : u.regs 27 = (fieldEquiv t saved).val := by
    simpa only [u, setReg_regs, Function.update_of_ne (by decide : (27 : Fin 36) ≠ 25),
      Function.update_of_ne (by decide : (27 : Fin 36) ≠ 24)] using h27
  have hr := (run_regs_frame (binary .add) 27 (by decide) u).trans hu27
  have hsa := size_code a
  have hss := size_code saved
  have hlin := linear_quartic (t := t)
  simp only [cubicTail, run_seq_snd, run_assign_fst, Expr.eval]
  dsimp only [u] at hc hr
  generalize hv : (binary .add).run (setReg (setReg st 24 (st.regs 26)) 25 1) = v at *
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Nat.size_one]
  rw [h26, hr]
  omega

/-- A complete concrete cubic constraint evaluator, with source-code restoration. -/
theorem cubeMinusOne_cost (st : State 36 11) (a : BinaryMaterializedField.Element t)
    (h20 : st.regs 20 = t) (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (cubeMinusOne.run st).2 ≤ 80000000 * (t + 1) ^ 4 := by
  let s := setReg st 27 (st.regs 24)
  have hs20 : s.regs 20 = t := by change st.regs 20 = t; exact h20
  have hs24 : s.regs 24 = (fieldEquiv t a).val := by change st.regs 24 = _; exact h24
  have hc := cube_cost s a hs20 hs24 hm he
  have hu26 := cube_run s a hs20 hs24 hm he
  have hu20 := (run_regs_frame cube 20 (by decide) s).trans hs20
  have hu27 : (cube.run s).1.regs 27 = (fieldEquiv t a).val :=
    (run_regs_frame cube 27 (by decide) s).trans (by simpa [s] using h24)
  have hu3 := (run_lists_frame cube 3 (by decide) s).trans hm
  have hu7 := (run_lists_frame cube 7 (by decide) s).trans he
  simp only [cubeMinusOne, run_seq_snd, run_assign_fst, Expr.eval]
  dsimp only [s] at hc hu26 hu20 hu27 hu3 hu7
  generalize hv : cube.run (setReg st 27 (st.regs 24)) = v at *
  have hf := cubicTail_cost v.1 (a ^ 3) a hu20 hu26 hu27 hu3 hu7
  have hsize := size_code a
  have hlin := linear_quartic (t := t)
  change Nat.size (st.regs 24) + Nat.size (st.regs 24) + 1 +
    (v.2 + (cubicTail.run v.1).2 + 1) + 1 ≤ _
  rw [h24]
  omega

end PCP.Lang.BinaryFieldCode
