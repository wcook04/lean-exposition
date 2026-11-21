/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryFieldLang
import PCP.Complexity.LangRenaming

/-!
# Binary powering with stored language registers

The multiplication program is embedded in a larger list-register file. Base,
exponent digits and accumulator occupy distinct stored lists. Each exponent digit
performs one squaring and at most one accumulator multiplication.
-/

namespace PCP.Lang.BinaryFieldPower

open PCP.Algebraic
open BinaryField

abbrev Word := BinaryWordMaterialization.Word

/-- Reserve three additional list registers for base, digits and accumulator. -/
def listEmbedding : Fin 8 → Fin 11 := Fin.castLE (by decide)

theorem listEmbedding_injective : Function.Injective listEmbedding := Fin.castLE_injective _

/-- The proved multiplication subprogram embedded without changing its cost. -/
def multiplication : Stmt 8 11 := BinaryField.mul.rename id listEmbedding

theorem multiplication_run {t : ℕ} (ht : 0 < t) (st : State 8 11) (m v w : Word t)
    (hm : st.lists 3 = encode m) (hv : st.lists 4 = encode v)
    (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (multiplication.run st).1.lists 1 = encode (BinaryWordMaterialization.mul ht m v w) := by
  have h := congrArg (fun z : State 8 8 × ℕ => z.1.lists 1)
    (BinaryField.mul.run_rename id listEmbedding Function.injective_id listEmbedding_injective st)
  exact h.trans (mul_run_encode ht _ m v w hm hv hw he)

theorem multiplication_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (m v w : Word t)
    (hm : st.lists 3 = encode m) (hv : st.lists 4 = encode v)
    (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (multiplication.run st).2 ≤ 6500 * (t + 1) ^ 3 := by
  rw [multiplication, Stmt.run_rename_cost _ _ _ Function.injective_id listEmbedding_injective]
  exact mul_cost_encode ht _ m v w hm hv hw he

/-- Multiply saved words, writing to a caller-selected saved list. -/
def multiplySaved (out left right : Fin 11) : Stmt 8 11 :=
  .seq (.copy left 4) (.seq (.copy right 5) (.seq multiplication (.copy 1 out)))

theorem multiplySaved_run {t : ℕ} (ht : 0 < t) (st : State 8 11) (m v w : Word t)
    (out left right : Fin 11) (hr : right ≠ 4)
    (hm : st.lists 3 = encode m) (hv : st.lists left = encode v)
    (hw : st.lists right = encode w) (he : st.lists 7 = []) :
    ((multiplySaved out left right).run st).1.lists out =
      encode (BinaryWordMaterialization.mul ht m v w) := by
  simp only [multiplySaved, run_seq_fst, run_copy_fst, setList_lists, Function.update_self]
  apply multiplication_run ht _ m v w
  · simp [Function.update, hm]
  · simp [Function.update, hv]
  · simp [Function.update, hr, hw]
  · simp [Function.update, he]

theorem multiplySaved_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (m v w : Word t)
    (out left right : Fin 11) (hr : right ≠ 4)
    (hm : st.lists 3 = encode m) (hv : st.lists left = encode v)
    (hw : st.lists right = encode w) (he : st.lists 7 = []) :
    ((multiplySaved out left right).run st).2 ≤ 6600 * (t + 1) ^ 3 := by
  let s := setList (setList st 4 (encode v)) 5 (encode w)
  have hm' : s.lists 3 = encode m := by simp [s, Function.update, hm]
  have hv' : s.lists 4 = encode v := by simp [s, Function.update]
  have hw' : s.lists 5 = encode w := by simp [s]
  have he' : s.lists 7 = [] := by simp [s, Function.update, he]
  have hc := multiplication_cost ht s m v w hm' hv' hw' he'
  have ho := multiplication_run ht s m v w hm' hv' hw' he'
  have hs1 := listSize_bits (encode_bits v)
  have hs2 := listSize_bits (encode_bits w)
  have hs3 := listSize_bits (encode_bits (BinaryWordMaterialization.mul ht m v w))
  simp only [encode_length] at hs1 hs2 hs3
  simp only [multiplySaved, run_seq_snd, run_copy_snd, run_copy_fst, setList_lists,
    Function.update_of_ne hr, hv, hw]
  change listSize (encode v) + 1 + (listSize (encode w) + 1 +
    ((multiplication.run s).2 + (listSize ((multiplication.run s).1.lists 1) + 1) + 1) + 1) + 1 ≤ _
  rw [ho]
  nlinarith [Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

/-- A little-endian exponent digit is consumed before the base is squared. -/
def body : Stmt 8 11 :=
  .seq (.pop 9 6 3) (.seq (.ite 6 (multiplySaved 10 10 8) .skip) (multiplySaved 8 8 8))

/-- The updated accumulator for one binary exponent digit. -/
def nextAccumulator {t : ℕ} (ht : 0 < t) (m a w : Word t) (b : Bool) : Word t :=
  if b then BinaryWordMaterialization.mul ht m a w else a

theorem body_step {t : ℕ} (ht : 0 < t) (st : State 8 11) (m a w : Word t)
    (b : Bool) (bs : List Bool) (hm : st.lists 3 = encode m)
    (hw : st.lists 8 = encode w) (ha : st.lists 10 = encode a)
    (hb : st.lists 9 = (b :: bs).map Bool.toNat) (he : st.lists 7 = []) :
    (body.run st).1.lists 3 = encode m ∧
    (body.run st).1.lists 8 = encode (BinaryWordMaterialization.mul ht m w w) ∧
    (body.run st).1.lists 10 = encode (nextAccumulator ht m a w b) ∧
    (body.run st).1.lists 9 = bs.map Bool.toNat ∧ (body.run st).1.lists 7 = [] := by
  let s := (Stmt.pop 9 6 3).run st |>.1
  have hs3 : s.lists 3 = encode m := by simp [s, Stmt.run, hb, Function.update, hm]
  have hs8 : s.lists 8 = encode w := by simp [s, Stmt.run, hb, Function.update, hw]
  have hs10 : s.lists 10 = encode a := by simp [s, Stmt.run, hb, Function.update, ha]
  have hs9 : s.lists 9 = bs.map Bool.toNat := by simp [s, Stmt.run, hb]
  have hs7 : s.lists 7 = [] := by simp [s, Stmt.run, hb, Function.update, he]
  have hs6 : s.regs 6 = b.toNat := by simp [s, Stmt.run, hb, Function.update]
  let u := ((Stmt.ite 6 (multiplySaved 10 10 8) .skip).run s).1
  have hu3 : u.lists 3 = encode m :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 3 (by decide) s).trans hs3
  have hu8 : u.lists 8 = encode w :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 8 (by decide) s).trans hs8
  have hu9 : u.lists 9 = bs.map Bool.toNat :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 9 (by decide) s).trans hs9
  have hu7 : u.lists 7 = [] :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 7 (by decide) s).trans hs7
  have hu10 : u.lists 10 = encode (nextAccumulator ht m a w b) := by
    cases b with
    | false => simpa [u, run_ite_fst, hs6, Stmt.run, nextAccumulator] using hs10
    | true =>
      simpa [u, run_ite_fst, hs6, nextAccumulator] using
        multiplySaved_run ht s m a w 10 10 8
          (by decide) hs3 hs10 hs8 hs7
  change ((multiplySaved 8 8 8).run u).1.lists 3 = encode m ∧ _
  exact ⟨(run_lists_frame (multiplySaved 8 8 8) 3 (by decide) u).trans hu3,
    multiplySaved_run ht u m w w 8 8 8 (by decide) hu3 hu8 hu8 hu7,
    (run_lists_frame (multiplySaved 8 8 8) 10 (by decide) u).trans hu10,
    (run_lists_frame (multiplySaved 8 8 8) 9 (by decide) u).trans hu9,
    (run_lists_frame (multiplySaved 8 8 8) 7 (by decide) u).trans hu7⟩

/-- Binary powering as a stored accumulator recurrence. -/
def powerWords {t : ℕ} (ht : 0 < t) (m : Word t) : List Bool → Word t → Word t → Word t
  | [], _, a => a
  | b :: bs, w, a => powerWords ht m bs (BinaryWordMaterialization.mul ht m w w)
      (nextAccumulator ht m a w b)

theorem iterate_run {t : ℕ} (ht : 0 < t) (c : ℕ) (st : State 8 11) (m a w : Word t)
    (bs : List Bool) (hm : st.lists 3 = encode m)
    (hw : st.lists 8 = encode w) (ha : st.lists 10 = encode a)
    (hb : st.lists 9 = bs.map Bool.toNat) (he : st.lists 7 = []) :
    (iterate body.run c bs.length st).1.lists 10 = encode (powerWords ht m bs w a) := by
  induction bs generalizing st a w with
  | nil => simpa [iterate, powerWords] using ha
  | cons b bs ih =>
    obtain ⟨h3, h8, h10, h9, h7⟩ := body_step ht st m a w b bs hm hw ha hb he
    rw [List.length_cons, iterate_succ_fst]
    exact ih _ _ _ h3 h8 h10 h9 h7

theorem toField_powerWords {t : ℕ} [NeZero t] (ht : 0 < t) (m a w : Word t)
    (hm : BinaryWordMaterialization.toWord m = BinaryQuotientModel.lowerCoefficients t ht)
    (bs : List Bool) :
    BinaryWordMaterialization.toField (powerWords ht m bs w a) =
      BinaryWordMaterialization.toField a *
        BinaryWordMaterialization.toField w ^ BinaryWordMaterialization.bitsValue bs := by
  induction bs generalizing a w with
  | nil => simp [powerWords, BinaryWordMaterialization.bitsValue]
  | cons b bs ih =>
    cases b <;> simp only [powerWords, nextAccumulator, Bool.false_eq_true, ite_false, ite_true,
      ih, BinaryWordMaterialization.toField_mul_modulus ht m _ _ hm,
      BinaryWordMaterialization.bitsValue]
    · simp [Nat.bit_val, pow_mul, pow_two, mul_pow]
    · simp [Nat.bit_val, pow_add, pow_mul, pow_two, mul_pow]
      ring

theorem body_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (m a w : Word t)
    (b : Bool) (bs : List Bool) (hm : st.lists 3 = encode m)
    (hw : st.lists 8 = encode w) (ha : st.lists 10 = encode a)
    (hb : st.lists 9 = (b :: bs).map Bool.toNat) (he : st.lists 7 = []) :
    (body.run st).2 ≤ 14000 * (t + 1) ^ 3 := by
  let s := (Stmt.pop 9 6 3).run st |>.1
  have hs3 : s.lists 3 = encode m := by simp [s, Stmt.run, hb, Function.update, hm]
  have hs8 : s.lists 8 = encode w := by simp [s, Stmt.run, hb, Function.update, hw]
  have hs10 : s.lists 10 = encode a := by simp [s, Stmt.run, hb, Function.update, ha]
  have hs7 : s.lists 7 = [] := by simp [s, Stmt.run, hb, Function.update, he]
  have hs6 : s.regs 6 = b.toNat := by simp [s, Stmt.run, hb, Function.update]
  let u := ((Stmt.ite 6 (multiplySaved 10 10 8) .skip).run s).1
  have hu3 : u.lists 3 = encode m :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 3 (by decide) s).trans hs3
  have hu8 : u.lists 8 = encode w :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 8 (by decide) s).trans hs8
  have hu7 : u.lists 7 = [] :=
    (run_lists_frame (.ite 6 (multiplySaved 10 10 8) .skip) 7 (by decide) s).trans hs7
  have hacc := multiplySaved_cost ht s m a w 10 10 8 (by decide) hs3 hs10 hs8 hs7
  have hsqr := multiplySaved_cost ht u m w w 8 8 8 (by decide) hu3 hu8 hu8 hu7
  have hsz : Nat.size b.toNat ≤ 1 := by cases b <;> decide
  have hpop : ((Stmt.pop (9 : Fin 11) (6 : Fin 8) 3).run st).2 ≤ 2 := by
    simpa only [Stmt.run, hb, List.map_cons] using Nat.add_le_add_right hsz 1
  have hite : ((Stmt.ite 6 (multiplySaved 10 10 8) .skip).run s).2 ≤
      6600 * (t + 1) ^ 3 + 2 := by
    rw [run_ite_snd, hs6]
    split_ifs
    · omega
    · change 1 + Nat.size b.toNat + 1 ≤ _
      nlinarith [Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]
  change ((Stmt.pop (9 : Fin 11) (6 : Fin 8) 3).run st).2 +
    (((Stmt.ite 6 (multiplySaved 10 10 8) .skip).run s).2 +
      ((multiplySaved 8 8 8).run u).2 + 1) + 1 ≤ _
  nlinarith [Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

/-- Cost includes the two complete stored multiplications and the captured loop counter. -/
theorem iterate_cost {t : ℕ} (ht : 0 < t) (c : ℕ) (st : State 8 11) (m a w : Word t)
    (bs : List Bool) (hm : st.lists 3 = encode m)
    (hw : st.lists 8 = encode w) (ha : st.lists 10 = encode a)
    (hb : st.lists 9 = bs.map Bool.toNat) (he : st.lists 7 = []) :
    (iterate body.run c bs.length st).2 ≤ bs.length * (c + 14000 * (t + 1) ^ 3) := by
  induction bs generalizing st a w with
  | nil => simp [iterate]
  | cons b bs ih =>
    obtain ⟨h3, h8, h10, h9, h7⟩ := body_step ht st m a w b bs hm hw ha hb he
    have hi := ih _ _ _ h3 h8 h10 h9 h7
    have hc := body_cost ht st m a w b bs hm hw ha hb he
    change c + (body.run st).2 + (iterate body.run c bs.length (body.run st).1).2 ≤
      (bs.length + 1) * (c + 14000 * (t + 1) ^ 3)
    rw [Nat.succ_mul]
    omega

theorem pushConstant_iterate {R Q : ℕ} (L : Fin Q) (x : Fin R) (v c n : ℕ)
    (st : State R Q) (h : st.regs x = v) :
    (iterate (Stmt.push L x).run c n st).1.lists L =
      List.replicate n v ++ st.lists L := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate_succ_fst, ih _ (by simp [run_push_fst, h]), run_push_fst]
    simp only [setList_lists, Function.update_self, h, List.replicate_succ',
      List.append_assoc, List.singleton_append]

/-- Write the constant one with the same coefficient length as the saved base. -/
def initializeOne : Stmt 8 11 :=
  .seq (.copy 7 10) (.seq (.len 8 7) (.seq (.assign 1 (.const 0))
    (.seq (.loop 7 (.push 10 1)) (.seq (.pop 10 1 3)
      (.seq (.assign 1 (.const 1)) (.push 10 1))))))

theorem initializeOne_run (st : State 8 11) (t : ℕ) (ht : 0 < t)
    (hw : (st.lists 8).length = t) (he : st.lists 7 = []) :
    (initializeOne.run st).1.lists 10 = 1 :: List.replicate (t - 1) 0 := by
  let s := setReg (setReg (setList st 10 []) 7 t) 1 0
  have hz := pushConstant_iterate (10 : Fin 11) (1 : Fin 8) 0 (Nat.size t + 1) t s
    (by simp [s])
  have hzs : (iterate (Stmt.push 10 1).run (Nat.size t + 1) t s).1.lists 10 =
      List.replicate t 0 := by simpa [s] using hz
  have ht' : t = (t - 1) + 1 := by omega
  rw [ht', List.replicate_succ] at hzs
  simp only [initializeOne, run_seq_fst, run_copy_fst, he, run_len_fst, setList_lists,
    Function.update_of_ne (by decide : (8 : Fin 11) ≠ 10), hw, run_assign_fst,
    Expr.eval, run_loop_fst, setReg_regs,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1), Function.update_self]
  change ((Stmt.push (10 : Fin 11) (1 : Fin 8)).run
    ((Stmt.assign 1 (.const 1)).run ((Stmt.pop 10 1 3).run
      (iterate (Stmt.push 10 1).run (Nat.size t + 1) t s).1).1).1).1.lists 10 = _
  rw [run_push_fst, run_assign_fst, run_pop_cons_fst _ _ _ _ (by simpa only [← ht'] using hzs)]
  simp [Expr.eval]

theorem encode_one {t : ℕ} (ht : 0 < t) :
    encode (BinaryWordMaterialization.one t) = 1 :: List.replicate (t - 1) 0 := by
  cases t with
  | zero => omega
  | succ n => simp [encode, BinaryWordArithmetic.one, List.ofFn_succ,
      show (1 : ZMod 2).val = 1 from rfl]

/-- Complete binary powering on the supplied little-endian exponent list. -/
def power : Stmt 8 11 :=
  .seq initializeOne (.seq (.len 9 7) (.seq (.loop 7 body) (.copy 10 1)))

theorem power_run {t : ℕ} (ht : 0 < t) (st : State 8 11) (m w : Word t) (bs : List Bool)
    (hm : st.lists 3 = encode m) (hw : st.lists 8 = encode w)
    (hb : st.lists 9 = bs.map Bool.toNat) (he : st.lists 7 = []) :
    (power.run st).1.lists 1 =
      encode (powerWords ht m bs w (BinaryWordMaterialization.one t)) := by
  let s := (initializeOne.run st).1
  have h3 : s.lists 3 = encode m := (run_lists_frame initializeOne 3 (by decide) st).trans hm
  have h8 : s.lists 8 = encode w := (run_lists_frame initializeOne 8 (by decide) st).trans hw
  have h9 : s.lists 9 = bs.map Bool.toNat :=
    (run_lists_frame initializeOne 9 (by decide) st).trans hb
  have h7 : s.lists 7 = [] := (run_lists_frame initializeOne 7 (by decide) st).trans he
  have h10 : s.lists 10 = encode (BinaryWordMaterialization.one t) := by
    rw [encode_one ht]
    exact initializeOne_run st t ht (by simp [hw]) he
  simp only [power, run_seq_fst, run_len_fst, run_copy_fst, run_loop_fst,
    setReg_regs, Function.update_self, setList_lists]
  change (iterate body.run (Nat.size (s.lists 9).length + 1) (s.lists 9).length
    (setReg s 7 (s.lists 9).length)).1.lists 10 = _
  rw [h9, List.length_map]
  exact iterate_run ht _ _ m _ w bs (by simpa using h3) (by simpa using h8)
    (by simpa using h10) (by simpa using h9) (by simpa using h7)

/-- The actual program computes the previously defined materialized binary power. -/
theorem power_run_encode {t : ℕ} [NeZero t] (ht : 0 < t) (st : State 8 11)
    (m w : Word t) (n : ℕ)
    (hmod : BinaryWordMaterialization.toWord m = BinaryQuotientModel.lowerCoefficients t ht)
    (hm : st.lists 3 = encode m) (hw : st.lists 8 = encode w)
    (hb : st.lists 9 = n.bits.map Bool.toNat) (he : st.lists 7 = []) :
    (power.run st).1.lists 1 = encode (BinaryWordMaterialization.power ht m w n) := by
  rw [power_run ht st m w n.bits hm hw hb he]
  congr 1
  apply BinaryWordMaterialization.toField_injective
  simp only [toField_powerWords ht m _ _ hmod, BinaryWordMaterialization.toField_one,
    BinaryWordMaterialization.bitsValue_bits, one_mul,
    BinaryWordMaterialization.toField_power ht m w hmod]

theorem initializeOne_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (w : Word t)
    (hw : st.lists 8 = encode w) (he : st.lists 7 = []) :
    (initializeOne.run st).2 ≤ 20 * (t + 1) ^ 2 := by
  let s := setReg (setReg (setList st 10 []) 7 t) 1 0
  let u := (iterate (Stmt.push (10 : Fin 11) (1 : Fin 8)).run (Nat.size t + 1) t s).1
  have hz : u.lists 10 = 0 :: List.replicate (t - 1) 0 := by
    rw [pushConstant_iterate _ _ 0 _ _ _ (by simp [s])]
    simp only [s, setReg_lists, setList_lists, Function.update_self, List.append_nil]
    rw [show t = (t - 1) + 1 by omega, List.replicate_succ]
    simp
  have hpost : ((Stmt.seq (.pop 10 1 3) (.seq (.assign 1 (.const 1)) (.push 10 1))).run u).2
      = 8 := by
    simp [Stmt.run, hz, Expr.cost, Expr.readSize, Expr.eval,
      show Nat.size 1 = 1 from rfl]
  have hit := iterate_cost_le (Stmt.push (10 : Fin 11) (1 : Fin 8)).run
    (Nat.size t + 1) 1 (fun s => s.regs 1 = 0)
    (fun s hs => by simpa [run_push_fst] using hs)
    (fun s hs => by simp [run_push_snd, hs]) t s (by simp [s])
  have hs := listSize_bits (encode_bits w)
  simp only [encode_length] at hs
  have hsz := size_le_self t
  change ((Stmt.seq (.copy 7 10) (.seq (.len 8 7) (.seq (.assign 1 (.const 0))
    (.seq (.loop 7 (.push 10 1)) (.seq (.pop 10 1 3)
      (.seq (.assign 1 (.const 1)) (.push 10 1))))))).run st).2 ≤ _
  rw [run_seq_snd, run_copy_snd, run_copy_fst, he, run_seq_snd,
    run_len_snd, run_len_fst]
  simp only [setList_lists, Function.update_of_ne (by decide : (8 : Fin 11) ≠ 10),
    hw, encode_length]
  rw [run_seq_snd, run_assign_fst, run_seq_snd, run_loop_snd, run_loop_fst]
  simp only [Expr.eval, setReg_regs,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1), Function.update_self]
  change listSize [] + 1 + (listSize (encode w) + Nat.size t + 1 +
    ((Expr.const 0).cost _ + ((iterate (Stmt.push 10 1).run (Nat.size t + 1) t s).2 +
      Nat.size t + 1 + _ + 1) + 1) + 1) + 1 ≤ _
  rw [hpost]
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero,
    show listSize ([] : List ℕ) = 0 from rfl]
  have hmul := Nat.mul_le_mul_left t hsz
  nlinarith

/-- Binary powering has polynomial charged cost in word length and digit-list length. -/
theorem power_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (m w : Word t) (bs : List Bool)
    (hm : st.lists 3 = encode m) (hw : st.lists 8 = encode w)
    (hb : st.lists 9 = bs.map Bool.toNat) (he : st.lists 7 = []) :
    (power.run st).2 ≤ 15000 * (t + bs.length + 1) ^ 4 := by
  let s := (initializeOne.run st).1
  have h3 : s.lists 3 = encode m := (run_lists_frame initializeOne 3 (by decide) st).trans hm
  have h8 : s.lists 8 = encode w := (run_lists_frame initializeOne 8 (by decide) st).trans hw
  have h9 : s.lists 9 = bs.map Bool.toNat :=
    (run_lists_frame initializeOne 9 (by decide) st).trans hb
  have h7 : s.lists 7 = [] := (run_lists_frame initializeOne 7 (by decide) st).trans he
  have h10 : s.lists 10 = encode (BinaryWordMaterialization.one t) := by
    rw [encode_one ht]
    exact initializeOne_run st t ht (by simp [hw]) he
  let u := setReg s 7 bs.length
  have hit := iterate_cost ht (Nat.size bs.length + 1) u m _ w bs
    (by simpa [u] using h3) (by simpa [u] using h8) (by simpa [u] using h10)
    (by simpa [u] using h9) (by simpa [u] using h7)
  have hout := iterate_run ht (Nat.size bs.length + 1) u m _ w bs
    (by simpa [u] using h3) (by simpa [u] using h8) (by simpa [u] using h10)
    (by simpa [u] using h9) (by simpa [u] using h7)
  have hinit := initializeOne_cost ht st w hw he
  have hbBit : Bits (bs.map Bool.toNat) := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  have hbsSize := listSize_bits hbBit
  simp only [List.length_map] at hbsSize
  have hoSize := listSize_bits
    (encode_bits (powerWords ht m bs w (BinaryWordMaterialization.one t)))
  simp only [encode_length] at hoSize
  have hsz := size_le_self bs.length
  simp only [power, run_seq_snd, run_len_snd, run_len_fst, run_loop_snd,
    run_copy_snd, run_loop_fst, setReg_regs, Function.update_self]
  change (initializeOne.run st).2 + (listSize (s.lists 9) + Nat.size (s.lists 9).length + 1 +
    ((iterate body.run (Nat.size (s.lists 9).length + 1) (s.lists 9).length
      (setReg s 7 (s.lists 9).length)).2 + Nat.size (s.lists 9).length + 1 +
      (listSize ((iterate body.run (Nat.size (s.lists 9).length + 1) (s.lists 9).length
        (setReg s 7 (s.lists 9).length)).1.lists 10) + 1) + 1) + 1) + 1 ≤ _
  rw [h9, List.length_map]
  change (initializeOne.run st).2 + (listSize (bs.map Bool.toNat) + Nat.size bs.length + 1 +
    ((iterate body.run (Nat.size bs.length + 1) bs.length u).2 + Nat.size bs.length + 1 +
      (listSize ((iterate body.run (Nat.size bs.length + 1) bs.length u).1.lists 10) + 1) + 1) + 1)
      + 1 ≤ _
  rw [hout]
  let N := t + bs.length + 1
  have hn1 : t + 1 ≤ N := by omega
  have hn2 : bs.length ≤ N := by omega
  have hn0 : 1 ≤ N := by omega
  have hn2' : bs.length + 1 ≤ N := by omega
  have hpow2 : (t + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn1 2
  have hpow3 : (t + 1) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hn1 3
  have hpow12 : N ≤ N ^ 2 := by nlinarith
  have hpow24 : N ^ 2 ≤ N ^ 4 := by nlinarith [Nat.zero_le ((N ^ 2 - 1) ^ 2)]
  have hpow14 : N ≤ N ^ 4 := hpow12.trans hpow24
  have hbig : bs.length * (Nat.size bs.length + 1 + 14000 * (t + 1) ^ 3) ≤
      N ^ 2 + 14000 * N ^ 4 := by
    have hleft : bs.length * (Nat.size bs.length + 1) ≤ N * N :=
      Nat.mul_le_mul hn2 (by omega)
    have hright : bs.length * (t + 1) ^ 3 ≤ N * N ^ 3 := Nat.mul_le_mul hn2 hpow3
    nlinarith
  change _ ≤ 15000 * N ^ 4
  nlinarith

end PCP.Lang.BinaryFieldPower
