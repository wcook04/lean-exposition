import PCP.Complexity.BinaryFieldCodePower

/-!
# Polynomial charged cost of numeric-code binary powering
-/

namespace PCP.Lang.BinaryFieldCodePower

open PCP.Algebraic BinaryField BinaryFieldCode BinaryRootPredicate

theorem encodeExponent_cost (st : State 42 11) (n W : ℕ)
    (h36 : st.regs 36 = n) (h37 : st.regs 37 = W) (hn : Nat.size n ≤ W)
    (he : st.lists 7 = []) :
    (encodeExponent.run st).2 ≤ 10000000 * (W + 1) ^ 2 := by
  let s := setReg (setReg (setList st 9 []) 38 n) 39 W
  have hb := BinaryEncode.program_cost (s.restrict digitRegs digitLists)
    (by simpa [s, digitRegs, Function.update] using hn)
  have hd : ((BinaryEncode.program.rename digitRegs digitLists).run s).2 ≤
      (BinaryEncode.passConstant + 10) * (W + Nat.size n + 3) ^ 2 := by
    rw [Stmt.run_rename_cost _ digitRegs digitLists (Fin.natAdd_injective 4 38)
      (Function.injective_of_subsingleton _)]
    simpa [s, digitRegs, digitLists, Function.update, listSize] using hb
  have hp : BinaryEncode.passConstant + 10 ≤ 1000000 := by decide
  have hd' := hd.trans (Nat.mul_le_mul hp (Nat.pow_le_pow_left
    (show W + Nat.size n + 3 ≤ 2 * W + 3 by omega) 2))
  have hsize := size_le_self W
  have ha : ((Stmt.assign 38 (.var 36) : Stmt 42 11).run (setList st 9 [])).2 =
      Nat.size n + Nat.size n + 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h36]
  have hb' : ((Stmt.assign 39 (.var 37) : Stmt 42 11).run
      (setReg (setList st 9 []) 38 n)).2 = Nat.size W + Nat.size W + 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update, h37]
  simp only [encodeExponent, run_seq_snd, run_copy_snd, run_copy_fst,
    run_assign_fst, Expr.eval, he, setList_regs, setReg_regs,
    Function.update_of_ne (by decide : (37 : Fin 42) ≠ 38), h36, h37]
  rw [ha, hb']
  change 1 + (Nat.size n + Nat.size n + 1 + (Nat.size W + Nat.size W + 1 +
    ((BinaryEncode.program.rename digitRegs digitLists).run s).2 + 1) + 1) + 1 ≤ _
  nlinarith

variable {t : ℕ} [NeZero t]

/-- Binary multiplication count and exponent serialization are both polynomial in bit width. -/
theorem program_cost (st : State 42 11) (a : BinaryMaterializedField.Element t) (n W : ℕ)
    (h20 : st.regs 20 = t) (h24 : st.regs 24 = (fieldEquiv t a).val)
    (h36 : st.regs 36 = n) (h37 : st.regs 37 = W) (hn : Nat.size n ≤ W)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).2 ≤ 30000000 * (t + W + 1) ^ 4 := by
  have hc1 := encodeExponent_cost st n W h36 h37 hn he
  have hd := encodeExponent_run st (by simpa [h36, h37] using hn) he
  rw [h36] at hd
  have h20' := run_regs_frame encodeExponent 20 (by decide) st
  have h24' := run_regs_frame encodeExponent 24 (by decide) st
  have h3' := run_lists_frame encodeExponent 3 (by decide) st
  have h7' := run_lists_frame encodeExponent 7 (by decide) st
  generalize hs : (encodeExponent.run st).1 = s at *
  have hload := loadCode_run 24 8 (s.restrict regs id) (h7'.trans he)
  change _ = BinaryPolynomialSelector.digits (s.regs 20) (s.regs 24) at hload
  rw [h20', h20, h24', h24, ← BinaryFieldWordCode.encode_word] at hload
  change _ = encode (BinaryFieldWordCode.word t ⟨code a.coefficients, code_lt _⟩) at hload
  rw [word_code] at hload
  have hw := (congrArg (fun v : State 36 11 => v.lists 8)
    (embed_state (loadCode 24 8) s)).trans hload
  have hc2 : ((embed (loadCode 24 8)).run s).2 ≤ 1000 * (t + 1) ^ 2 := by
    rw [embed, Stmt.run_rename_cost _ regs id (Fin.castAdd_injective 36 6) Function.injective_id]
    exact loadCode_cost 24 8 (s.restrict regs id) t (h20'.trans h20)
      (by change s.regs 24 < _; rw [h24', h24]; exact (fieldEquiv t a).isLt) (h7'.trans he)
  have hu3 := run_lists_frame (embed (loadCode 24 8)) 3 (by decide) s
  have hu7 := run_lists_frame (embed (loadCode 24 8)) 7 (by decide) s
  have hu9 := run_lists_frame (embed (loadCode 24 8)) 9 (by decide) s
  generalize hu : ((embed (loadCode 24 8)).run s).1 = u at *
  have hp := power36_run (u.restrict regs id) a.coefficients n
    (hu3.trans (h3'.trans hm)) hw (hu9.trans hd) (hu7.trans (h7'.trans he))
  have ho := (congrArg (fun v : State 36 11 => v.lists 1) (embed_state power36 u)).trans hp
  have hc3 : ((embed power36).run u).2 ≤ 15000 * (t + Nat.size n + 1) ^ 4 := by
    rw [embed, Stmt.run_rename_cost _ regs id (Fin.castAdd_injective 36 6) Function.injective_id]
    simpa only [Nat.size_eq_bits_len] using power36_cost (u.restrict regs id) a.coefficients n
      (hu3.trans (h3'.trans hm)) hw (hu9.trans hd) (hu7.trans (h7'.trans he))
  generalize hv : ((embed power36).run u).1 = v at *
  have hc4 : ((embed finish).run v).2 ≤ 10000010 * (t + 1) ^ 2 := by
    rw [embed, Stmt.run_rename_cost _ regs id (Fin.castAdd_injective 36 6) Function.injective_id]
    exact finish_cost (v.restrict regs id) _ ho
  let N := t + W + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have h2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
  have hW : (W + 1) ^ 2 ≤ N ^ 4 :=
    (Nat.pow_le_pow_left (by dsimp [N]; omega) 2).trans h2
  have ht : (t + 1) ^ 2 ≤ N ^ 4 :=
    (Nat.pow_le_pow_left (by dsimp [N]; omega) 2).trans h2
  have hn' : (t + Nat.size n + 1) ^ 4 ≤ N ^ 4 :=
    Nat.pow_le_pow_left (by dsimp [N]; omega) 4
  have hp1 : 1 ≤ N ^ 4 := one_le_pow₀ hN
  have h1' := hc1.trans (Nat.mul_le_mul_left 10000000 hW)
  have h2' := hc2.trans (Nat.mul_le_mul_left 1000 ht)
  have h3'' := hc3.trans (Nat.mul_le_mul_left 15000 hn')
  have h4' := hc4.trans (Nat.mul_le_mul_left 10000010 ht)
  simp only [program, run_seq_snd, hs, hu, hv]
  change _ ≤ 30000000 * N ^ 4
  omega

end PCP.Lang.BinaryFieldCodePower
