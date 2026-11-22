import PCP.Complexity.BinaryFieldCodeLang

/-!
# Polynomial charged costs for arithmetic on binary field codes

The bounds include operand serialization, all list copies, coefficient arithmetic,
and result decoding. They depend on the bit width of the field, not its order.
-/

namespace PCP.Lang.BinaryFieldCode

open PCP.Algebraic BinaryField BinaryFieldWordCode BinaryRootPredicate

/-- Fixed-width serialization of any in-range code has a quadratic allowance. -/
theorem loadCode_cost (x : Fin 36) (L : Fin 11) (st : State 36 11) (t : ℕ)
    (h20 : st.regs 20 = t) (hx : st.regs x < 2 ^ t) (he : st.lists 7 = []) :
    ((loadCode x L).run st).2 ≤ 1000 * (t + 1) ^ 2 := by
  let s := setReg st 33 (st.regs x)
  have hs := serialize_cost s (by simpa [s] using he)
  have hh := serialize_run s (by simpa [s] using he)
  have hs20 : s.regs 20 = t := by simp [s, Function.update, h20]
  have hs33 : s.regs 33 = st.regs x := by simp [s]
  rw [hs20, hs33] at hs hh
  have hsize : Nat.size (st.regs x) ≤ t := Nat.size_le.mpr hx
  have hlist : listSize ((serialize.run s).1.lists 8) ≤ 2 * t := by
    rw [hh]
    simpa using listSize_bits (BinaryPolynomialSelector.digits_bits t (st.regs x))
  simp only [loadCode, run_seq_snd, run_assign_fst, run_copy_snd, Expr.eval]
  change Nat.size (st.regs x) + Nat.size (st.regs x) + 1 +
    ((serialize.run s).2 + (listSize ((serialize.run s).1.lists 8) + 1) + 1) + 1 ≤ _
  have hs' := hs.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega :
    t + Nat.size (st.regs x) + 1 ≤ 2 * t + 1) 2))
  nlinarith

theorem add36_cost {t : ℕ} [NeZero t] (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hv : st.lists 0 = encode v) (hw : st.lists 2 = encode w) (he : st.lists 1 = []) :
    (add36.run st).2 ≤ 50 * (t + 1) ^ 2 := by
  rw [add36, Stmt.run_rename_cost BinaryField.add powerRegs BinaryFieldPower.listEmbedding
    (Fin.castLE_injective _) BinaryFieldPower.listEmbedding_injective]
  simpa only [encode_length] using BinaryField.add_cost _ (encode v) (encode w) hv hw he
    (by simp) (encode_bits v) (encode_bits w)

theorem mul36_cost {t : ℕ} [NeZero t] (ht : 0 < t) (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 4 = encode v) (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (mul36.run st).2 ≤ 6500 * (t + 1) ^ 3 := by
  rw [mul36, Stmt.run_rename_cost BinaryFieldPower.multiplication powerRegs id
    (Fin.castLE_injective _) Function.injective_id]
  exact BinaryFieldPower.multiplication_cost ht _ _ v w hm hv hw he

theorem inverse36_cost {t : ℕ} [NeZero t] (ht : 0 < t) (st : State 36 11)
    (v : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 8 = encode v) (he : st.lists 7 = []) :
    (inverse36.run st).2 ≤ 250000 * (t + 1) ^ 4 := by
  rw [inverse36, Stmt.run_rename_cost BinaryFieldInverse.inverse powerRegs id
    (Fin.castLE_injective _) Function.injective_id]
  exact BinaryFieldInverse.inverse_cost ht _ _ v hm hv he

theorem operate_cost {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 4 = encode v) (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    ((operate op).run st).2 ≤ 10000 * (t + 1) ^ 3 := by
  cases op with
  | mul => exact (mul36_cost ht st v w hm hv hw he).trans (by omega)
  | add =>
      let s := setList (setList (setList st 0 (st.lists 4)) 2 (st.lists 5)) 1 []
      have hs := add36_cost s v w (by simp [s, hv, Function.update])
        (by simp [s, hw, Function.update]) (by simp [s])
      have hvsize := listSize_bits (encode_bits v)
      have hwsize := listSize_bits (encode_bits w)
      simp only [encode_length] at hvsize hwsize
      simp only [operate, addSaved, run_seq_snd, run_copy_fst, run_copy_snd,
        setList_lists, Function.update, Fin.reduceEq, dite_false, he]
      change (listSize (st.lists 4) + 1) + ((listSize (st.lists 5) + 1) +
        ((listSize ([] : List ℕ) + 1) + (add36.run s).2 + 1) + 1) + 1 ≤ _
      rw [hv, hw]
      simp only [show listSize ([] : List ℕ) = 0 from rfl]
      nlinarith [Nat.zero_le (t ^ 3)]

theorem binaryWords_cost {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (i j : Fin (2 ^ t)) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = i.val) (h25 : st.regs 25 = j.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((binaryWords op).run st).2 ≤ 13000 * (t + 1) ^ 3 := by
  have hc1 := loadCode_cost 24 4 st t h20 (by rw [h24]; exact i.isLt) he
  have hs4 := loadCode_run 24 4 st he
  rw [h20, h24, ← encode_word] at hs4
  have hs20 := run_regs_frame (loadCode 24 4) 20 (by decide) st
  have hs25 := run_regs_frame (loadCode 24 4) 25 (by decide) st
  have hs3 := run_lists_frame (loadCode 24 4) 3 (by decide) st
  have hs7 := run_lists_frame (loadCode 24 4) 7 (by decide) st
  simp only [binaryWords, run_seq_snd]
  generalize hs : ((loadCode 24 4).run st).1 = s at *
  have hc2 := loadCode_cost 25 5 s t (hs20.trans h20)
    (by rw [hs25, h25]; exact j.isLt) (hs7.trans he)
  have hu5 := loadCode_run 25 5 s (hs7.trans he)
  rw [hs20, h20, hs25, h25, ← encode_word] at hu5
  have hu4 := run_lists_frame (loadCode 25 5) 4 (by decide) s
  have hu3 := run_lists_frame (loadCode 25 5) 3 (by decide) s
  have hu7 := run_lists_frame (loadCode 25 5) 7 (by decide) s
  generalize hu : ((loadCode 25 5).run s).1 = u at *
  have hc3 := operate_cost op ht u _ _ (hu3.trans (hs3.trans hm)) (hu4.trans hs4) hu5
    (hu7.trans (hs7.trans he))
  nlinarith [Nat.zero_le (t ^ 3)]

theorem finish_cost {t : ℕ} [NeZero t] (st : State 36 11) (v : BinaryWordMaterialization.Word t)
    (hv : st.lists 1 = encode v) :
    (finish.run st).2 ≤ 10000010 * (t + 1) ^ 2 := by
  have hd := decode36_cost st (by rw [hv]; exact encode_bits v)
  rw [hv, encode_length] at hd
  have hc : WordCodec.passConstant * 3 + 20 ≤ 10000000 := by decide
  have hd' := hd.trans (Nat.mul_le_mul_right _ hc)
  have hs := decode36_run st
  rw [hv] at hs
  have hsize : Nat.size ((decode36.run st).1.regs 1) ≤ t := by
    rw [hs]
    apply Nat.size_le.mpr
    simpa using WordCodec.value_lt (encode_bits v)
  simp only [finish, run_seq_snd]
  change (decode36.run st).2 +
    (Nat.size ((decode36.run st).1.regs 1) + Nat.size ((decode36.run st).1.regs 1) + 1) + 1 ≤ _
  nlinarith

/-- The complete binary-code interface is polynomial in field bit width. -/
theorem binary_cost {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (i j : Fin (2 ^ t)) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = i.val) (h25 : st.regs 25 = j.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((binary op).run st).2 ≤ 20000000 * (t + 1) ^ 4 := by
  have hw := binaryWords_cost op ht st i j h20 h24 h25 hm he
  have hr := binaryWords_run op ht st i j h20 h24 h25 hm he
  have hf := finish_cost _ _ hr
  rw [binary, run_seq_snd]
  nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3)]

/-- Inversion includes the zero case and the field-size-minus-two exponent. -/
theorem inverse_cost {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h24 : st.regs 24 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (inverse.run st).2 ≤ 20000000 * (t + 1) ^ 4 := by
  have hc := loadCode_cost 24 8 st t h20 (by rw [h24]; exact i.isLt) he
  have hs8 := loadCode_run 24 8 st he
  rw [h20, h24, ← encode_word] at hs8
  have hs3 := run_lists_frame (loadCode 24 8) 3 (by decide) st
  have hs7 := run_lists_frame (loadCode 24 8) 7 (by decide) st
  have hi := inverse36_cost (Nat.pos_of_ne_zero (NeZero.ne t)) _ _ (hs3.trans hm) hs8
    (hs7.trans he)
  have hr := inverseWords_run st i h20 h24 hm he
  have hf := finish_cost _ _ hr
  simp only [inverse, inverseWords, run_seq_snd]
  change ((loadCode 24 8).run st).2 + (inverse36.run ((loadCode 24 8).run st).1).2 + 1 +
    (finish.run (inverseWords.run st).1).2 + 1 ≤ _
  nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3)]

end PCP.Lang.BinaryFieldCode
