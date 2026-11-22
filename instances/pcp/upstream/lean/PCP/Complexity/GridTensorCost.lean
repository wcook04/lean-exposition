import PCP.Complexity.GridTensorLang

/-!
# Charged polynomial cost of tensor interpolation basis evaluation
-/

namespace PCP.Lang.GridTensor

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t h : ℕ} [NeZero t]

theorem basisCall_cost (z : BinaryMaterializedField.Element t) (k : Fin h) (hh : h ≤ 2 ^ t)
    (st : State 50 16) (hc : Context t h st)
    (h0 : st.regs 0 = (fieldEquiv t z).val) (h3 : st.regs 3 = k.val) :
    (basisCall.run st).2 ≤ 131000000 * (h + t + 1) ^ 5 := by
  let s := setReg (setReg st 24 (st.regs 44)) 32 (st.regs 45)
  have hr := congrArg Prod.snd (basis_result s)
  have hp := GridBasisCoordinate.program_cost z k.val h hh (lt_of_lt_of_le k.isLt hh)
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [s, Function.update] using h0) (by simpa [s, Function.update] using h3)
    (by simpa [s, Function.update] using hc.1) (by simpa [s] using hc.2.1)
    hc.2.2.1 hc.2.2.2
  rw [← hr] at hp
  have ht := size_le_self t
  have hh' := size_le_self h
  have hlin : h + t + 1 ≤ (h + t + 1) ^ 5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ h + t + 1) (by decide : 1 ≤ 5)
  simp only [basisCall, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 44).cost st.regs +
    ((Expr.var 45).cost (setReg st 24 (st.regs 44)).regs + (basis.run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.1, hc.2.1]
  omega

theorem multiplyCall_cost (a b : BinaryMaterializedField.Element t)
    (st : State 50 16) (hc : Context t h st)
    (ha : st.regs 40 = (fieldEquiv t a).val) (hb : st.regs 2 = (fieldEquiv t b).val) :
    (multiplyCall.run st).2 ≤ 21000000 * (t + 1) ^ 4 := by
  let s := setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 40)) 25 (st.regs 2)
  have hr := multiply_result s
  have hp := binary_cost .mul (Nat.pos_of_ne_zero (NeZero.ne t))
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (fieldEquiv t a) (fieldEquiv t b)
    (by simpa [s, Function.update] using hc.1) (by simpa [s, Function.update] using ha)
    (by simpa [s] using hb) hc.2.2.1 hc.2.2.2
  rw [← congrArg Prod.snd hr] at hp
  have hout := binary_run_field .mul
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) a b
    (by simpa [s, Function.update] using hc.1) (by simpa [s, Function.update] using ha)
    (by simpa [s] using hb) hc.2.2.1 hc.2.2.2
  have ho := (congrArg (fun p : State 36 11 × ℕ => p.1.regs 26) hr).trans hout
  simp only [State.restrict_regs,
    show Fin.castLE (by decide : 36 ≤ 50) (26 : Fin 36) = (26 : Fin 50) from rfl,
    Op.fieldEval] at ho
  have hsa : Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt
  have hsb : Nat.size (fieldEquiv t b).val ≤ t := Nat.size_le.mpr (fieldEquiv t b).isLt
  have hso : Nat.size (fieldEquiv t (a * b)).val ≤ t := Nat.size_le.mpr (fieldEquiv t (a*b)).isLt
  have hst := size_le_self t
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [multiplyCall, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  dsimp only [s] at hp ho
  generalize hu : multiply.run
    (setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 40)) 25 (st.regs 2)) = u at *
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, hc.1, ha, hb, ho]
  omega

theorem body_cost (p : BinaryMaterializedField.Element t × Fin h)
    (xs : List (BinaryMaterializedField.Element t × Fin h))
    (acc : BinaryMaterializedField.Element t) (hh : h ≤ 2 ^ t)
    (st : State 50 16) (hi : Inv (p :: xs) acc st) :
    (body.run st).2 ≤ 160000000 * (h + t + 1) ^ 5 := by
  let s := setReg (setReg (setList st 14 (pointCodes xs)) 0 (fieldEquiv t p.1).val) 42 1
  let u := setReg (setReg (setList s 15 (nodeCodes xs)) 3 p.2.val) 42 1
  have hs : ((Stmt.pop 14 0 42).run st).1 = s := by
    simp [Stmt.run, hi.2.2.1, pointCodes, s]
  have hu : ((Stmt.pop 15 3 42).run s).1 = u := by
    simp [Stmt.run, s, hi.2.2.2, nodeCodes, Function.update, u]
  have huc : Context t h u := by simpa [Context, u, s, Function.update] using hi.1
  have hu0 : u.regs 0 = (fieldEquiv t p.1).val := by simp [u, s, Function.update]
  have hu3 : u.regs 3 = p.2.val := by simp [u, Function.update]
  have hbc := basisCall_cost p.1 p.2 hh u huc hu0 hu3
  have hv2 := basisCall_run p.1 p.2 hh u huc hu0 hu3
  have hvc := basisCall_context u huc
  have hv40 := run_regs_frame basisCall 40 (by decide) u
  simp only [body, run_seq_snd, hs, hu]
  generalize hv : (basisCall.run u).1 = v at *
  have hvacc : v.regs 40 = (fieldEquiv t acc).val := by
    rw [hv40]
    simpa [u, s, Function.update] using hi.2.1
  have hmc := multiplyCall_cost acc _ v hvc hvacc hv2
  have hc1 : ((Stmt.pop 14 0 42).run st).2 = Nat.size (fieldEquiv t p.1).val + 1 := by
    simp [Stmt.run, hi.2.2.1, pointCodes]
  have hc2 : ((Stmt.pop 15 3 42).run s).2 = Nat.size p.2.val + 1 := by
    simp [Stmt.run, s, hi.2.2.2, nodeCodes, Function.update]
  rw [hc1, hc2]
  have hsp : Nat.size (fieldEquiv t p.1).val ≤ t := Nat.size_le.mpr (fieldEquiv t p.1).isLt
  have hsk : Nat.size p.2.val ≤ t := Nat.size_le.mpr (lt_of_lt_of_le p.2.isLt hh)
  have hlin : h + t + 1 ≤ (h + t + 1) ^ 5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ h + t + 1) (by decide : 1 ≤ 5)
  have hp : (t + 1) ^ 4 ≤ (h + t + 1) ^ 5 :=
    (Nat.pow_le_pow_left (by omega : t + 1 ≤ h + t + 1) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 4 ≤ 5))
  have hmc' := hmc.trans (Nat.mul_le_mul_left 21000000 hp)
  omega

/-- Every consumed coordinate pays its full interpolation and multiplication cost. -/
theorem iterate_cost (xs : List (BinaryMaterializedField.Element t × Fin h))
    (acc : BinaryMaterializedField.Element t) (hh : h ≤ 2 ^ t) (c : ℕ)
    (st : State 50 16) (hi : Inv xs acc st) :
    (iterate body.run c xs.length st).2 ≤ xs.length * (c + 160000000 * (h + t + 1) ^ 5) := by
  induction xs generalizing acc st with
  | nil => simp [iterate]
  | cons p xs ih =>
    have hc := body_cost p xs acc hh st hi
    have ht := ih _ _ (body_inv p xs acc hh st hi)
    simp only [List.length_cons, iterate]
    nlinarith

omit [NeZero t] in
theorem pointCodes_size (xs : List (BinaryMaterializedField.Element t × Fin h)) :
    listSize (pointCodes xs) ≤ xs.length * (t + 1) := by
  induction xs with
  | nil => simp [pointCodes, listSize]
  | cons p xs ih =>
    have hp : Nat.size (fieldEquiv t p.1).val ≤ t := Nat.size_le.mpr (fieldEquiv t p.1).isLt
    simp only [pointCodes, List.map_cons, listSize, List.sum_cons, List.length_cons] at *
    nlinarith

omit [NeZero t] in
theorem nodeCodes_size (xs : List (BinaryMaterializedField.Element t × Fin h))
    (hh : h ≤ 2 ^ t) : listSize (nodeCodes xs) ≤ xs.length * (t + 1) := by
  induction xs with
  | nil => simp [nodeCodes, listSize]
  | cons p xs ih =>
    have hp : Nat.size p.2.val ≤ t := Nat.size_le.mpr (lt_of_lt_of_le p.2.isLt hh)
    simp only [nodeCodes, List.map_cons, listSize, List.sum_cons, List.length_cons] at *
    nlinarith

/-- Full cost including both source copies, length calculation, setup and loop. -/
theorem program_cost (xs : List (BinaryMaterializedField.Element t × Fin h))
    (hh : h ≤ 2 ^ t) (st : State 50 16) (hc : Context t h st)
    (hx : st.lists 12 = pointCodes xs) (hk : st.lists 13 = nodeCodes xs) :
    (program.run st).2 ≤ 200000000 * (xs.length + h + t + 1) ^ 6 := by
  let s := setReg (setReg (setList (setList st 14 (st.lists 12)) 15 (st.lists 13))
    41 (st.lists 12).length) 40 1
  have hi : Inv xs 1 s := by
    refine ⟨by simpa [Context, s, Function.update] using hc, ?_, ?_, ?_⟩
    · change 1 = (fieldEquiv t (1 : BinaryMaterializedField.Element t)).val
      rw [code_one]
    · simpa [s, Function.update] using hx
    · simpa [s] using hk
  have hl : s.regs 41 = xs.length := by simp [s, Function.update, hx, pointCodes]
  have hit := iterate_cost xs 1 hh (Nat.size xs.length + 1) s hi
  have hp := pointCodes_size xs
  have hn := nodeCodes_size xs hh
  have hs := size_le_self xs.length
  let B := xs.length + h + t + 1
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hnB : xs.length ≤ B := by dsimp [B]; omega
  have htB : t + 1 ≤ B := by dsimp [B]; omega
  have hbase : h + t + 1 ≤ B := by dsimp [B]; omega
  have hb5 : B ≤ B ^ 5 := by
    simpa using Nat.pow_le_pow_right hb (by decide : 1 ≤ 5)
  have hb6 : B ≤ B ^ 6 := by
    simpa using Nat.pow_le_pow_right hb (by decide : 1 ≤ 6)
  have h56 : B ^ 5 ≤ B ^ 6 := Nat.pow_le_pow_right hb (by decide : 5 ≤ 6)
  have hpow : (h + t + 1) ^ 5 ≤ B ^ 5 := Nat.pow_le_pow_left hbase 5
  have hpass : Nat.size xs.length + 1 + 160000000 * (h + t + 1) ^ 5 ≤
      160000002 * B ^ 5 := by omega
  have hloop : (iterate body.run (Nat.size xs.length + 1) xs.length s).2 ≤
      160000002 * B ^ 6 := by
    calc
      _ ≤ xs.length * (Nat.size xs.length + 1 + 160000000 * (h + t + 1) ^ 5) := hit
      _ ≤ B * (160000002 * B ^ 5) := Nat.mul_le_mul hnB hpass
      _ = _ := by ring
  have hwords : xs.length * (t + 1) ≤ B ^ 6 := by
    calc
      _ ≤ B * B ^ 5 := Nat.mul_le_mul hnB (htB.trans hb5)
      _ = _ := by ring
  have hl12 : (st.lists 12).length = xs.length := by simp [hx, pointCodes]
  simp only [program, run_seq_snd, run_copy_fst, run_copy_snd, run_len_snd,
    run_len_fst, run_assign_fst, Expr.eval, run_loop_snd]
  change listSize (st.lists 12) + 1 + (listSize (st.lists 13) + 1 +
    (listSize (st.lists 12) + Nat.size (st.lists 12).length + 1 +
      (((Stmt.assign 40 (.const 1)).run
        (setReg (setList (setList st 14 (st.lists 12)) 15 (st.lists 13))
          41 (st.lists 12).length)).2 +
        ((iterate body.run (Nat.size (s.regs 41) + 1) (s.regs 41) s).2 +
          Nat.size (s.regs 41) + 1) + 1) + 1) + 1) + 1 ≤ _
  have hassign : ∀ u : State 50 16, ((Stmt.assign 40 (.const 1)).run u).2 = 3 := by
    intro u
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  rw [hassign, hl, hx, hk]
  rw [show (pointCodes xs).length = xs.length from by simp [pointCodes]]
  change _ ≤ 200000000 * B ^ 6
  omega

end PCP.Lang.GridTensor
