/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryFieldPowerLang

/-!
# A zero-aware stored-word inversion program

The exponent `2^t - 2` is constructed as `t` binary digits directly from the word
length, including a harmless leading zero at degree one. A stored scan handles
the zero input before calling the proved binary-power routine.
-/

namespace PCP.Lang.BinaryFieldInverse

open PCP.Algebraic BinaryField BinaryFieldPower

/-- Add one stored coefficient to the scan accumulator. -/
def scanBody : Stmt 8 11 := .seq (.pop 9 2 3) (.assign 1 (.add 1 2))

theorem scanBody_step (st : State 8 11) (x : ℕ) (a : List ℕ) (h : st.lists 9 = x :: a) :
    (scanBody.run st).1.regs 1 = st.regs 1 + x ∧ (scanBody.run st).1.lists 9 = a := by
  simp [scanBody, Stmt.run, h, Expr.eval, Function.update]

theorem scan_iterate (c : ℕ) (a : List ℕ) (st : State 8 11) (h : st.lists 9 = a) :
    (iterate scanBody.run c a.length st).1.regs 1 = st.regs 1 + a.sum ∧
    (iterate scanBody.run c a.length st).1.lists 9 = [] := by
  induction a generalizing st with
  | nil => simp [iterate, h]
  | cons x a ih =>
    obtain ⟨h1, h9⟩ := scanBody_step st x a h
    obtain ⟨k1, k9⟩ := ih (scanBody.run st).1 h9
    rw [List.length_cons, iterate_succ_fst]
    exact ⟨by simpa [h1, Nat.add_assoc] using k1, k9⟩

/-- Sum the coefficients while preserving the saved input word in list `8`. -/
def scan : Stmt 8 11 :=
  .seq (.copy 8 9) (.seq (.len 9 7) (.seq (.assign 1 (.const 0)) (.loop 7 scanBody)))

theorem scan_run (st : State 8 11) :
    (scan.run st).1.regs 1 = (st.lists 8).sum ∧ (scan.run st).1.lists 9 = [] := by
  simp only [scan, run_seq_fst, run_copy_fst, run_len_fst, run_assign_fst, Expr.eval,
    run_loop_fst, setReg_regs,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1),
    setList_lists, Function.update_self]
  simpa using scan_iterate (Nat.size (st.lists 8).length + 1) (st.lists 8)
    (setReg (setReg (setList st 9 (st.lists 8)) 7 (st.lists 8).length) 1 0) (by simp)

/-- The explicit binary exponent for inversion. -/
def digits (t : ℕ) : List Bool := false :: List.replicate (t - 1) true

theorem bitsValue_ones (n : ℕ) :
    BinaryWordMaterialization.bitsValue (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => simp [BinaryWordMaterialization.bitsValue]
  | succ n ih =>
    rw [List.replicate_succ, BinaryWordMaterialization.bitsValue, ih]
    simp only [Nat.bit_val, Bool.toNat_true, pow_succ]
    have hp : 0 < 2 ^ n := by positivity
    omega

theorem digits_value (t : ℕ) (ht : 0 < t) :
    BinaryWordMaterialization.bitsValue (digits t) = 2 ^ t - 2 := by
  rw [digits, BinaryWordMaterialization.bitsValue, bitsValue_ones]
  simp only [Nat.bit_val, Bool.toNat_false, Nat.add_zero]
  have hp : 0 < 2 ^ (t - 1) := by positivity
  conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ]
  omega

@[simp] theorem digits_length (t : ℕ) (ht : 0 < t) : (digits t).length = t := by
  simp [digits]; omega

/-- Construct the exponent digits from the stored input length, without constructing `2^t`. -/
def prepareExponent : Stmt 8 11 :=
  .seq (.len 8 7) (.seq (.assign 2 (.const 1)) (.seq (.assign 7 (.sub 7 2))
    (.seq (.loop 7 (.push 9 2)) (.seq (.assign 2 (.const 0)) (.push 9 2)))))

theorem prepareExponent_run (st : State 8 11) (he : st.lists 9 = []) :
    (prepareExponent.run st).1.lists 9 = (digits (st.lists 8).length).map Bool.toNat := by
  simp only [prepareExponent, run_seq_fst, run_len_fst, run_assign_fst, Expr.eval,
    run_loop_fst, run_push_fst, setReg_regs, Function.update_self,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 2)]
  simp only [setList_lists, setReg_lists, Function.update_self]
  rw [pushConstant_iterate _ _ 1 _ _ _ (by simp [Function.update])]
  simp [digits, he]

/-- Invert a stored field word, using its supplied stored modulus. -/
def inverse : Stmt 8 11 :=
  .seq scan (.ite 1 (.seq prepareExponent power) (.copy 8 1))

theorem encode_injective {t : ℕ} : Function.Injective (encode (t := t)) := by
  intro v w h
  apply BinaryWordMaterialization.toField_injective
  apply BinaryConcreteField.Element.ext
  funext i
  apply ZMod.val_injective 2
  have he := congrArg (fun l : List ℕ => l[i.val]?) h
  simpa [encode, i.isLt, BinaryWordMaterialization.toField] using he

theorem sum_encode_eq_zero_iff {t : ℕ} (w : Word t) :
    (encode w).sum = 0 ↔ w = BinaryWordMaterialization.zero t := by
  constructor
  · intro h
    apply encode_injective
    rw [encode_zero]
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hv : (encode w)[i] = 0 := by
        have hx := List.le_sum_of_mem (List.getElem_mem hi)
        omega
      simpa using hv
  · rintro rfl
    simp

/-- Exact inversion semantics, including zero and the degree-one field. -/
theorem inverse_run_encode {t : ℕ} [NeZero t] (ht : 0 < t) (st : State 8 11)
    (m w : Word t)
    (hmod : BinaryWordMaterialization.toWord m = BinaryQuotientModel.lowerCoefficients t ht)
    (hm : st.lists 3 = encode m) (hw : st.lists 8 = encode w) (he : st.lists 7 = []) :
    (inverse.run st).1.lists 1 = encode (BinaryWordMaterialization.inverse w) := by
  let s := (scan.run st).1
  have h3 : s.lists 3 = encode m := (run_lists_frame scan 3 (by decide) st).trans hm
  have h8 : s.lists 8 = encode w := (run_lists_frame scan 8 (by decide) st).trans hw
  have h7 : s.lists 7 = [] := (run_lists_frame scan 7 (by decide) st).trans he
  have h1 : s.regs 1 = (encode w).sum := by simpa [hw] using (scan_run st).1
  have h9 : s.lists 9 = [] := (scan_run st).2
  change ((Stmt.ite 1 (.seq prepareExponent power) (.copy 8 1)).run s).1.lists 1 = _
  rw [run_ite_fst, h1]
  by_cases hz : (encode w).sum = 0
  · have hwz := (sum_encode_eq_zero_iff w).mp hz
    simp [run_copy_fst, h8, hwz, BinaryWordMaterialization.inverse]
  · rw [ite_eq_left hz, run_seq_fst]
    let u := (prepareExponent.run s).1
    have hu3 : u.lists 3 = encode m :=
      (run_lists_frame prepareExponent 3 (by decide) s).trans h3
    have hu8 : u.lists 8 = encode w :=
      (run_lists_frame prepareExponent 8 (by decide) s).trans h8
    have hu7 : u.lists 7 = [] := (run_lists_frame prepareExponent 7 (by decide) s).trans h7
    have hu9 : u.lists 9 = (digits t).map Bool.toNat := by
      simpa only [h8, encode_length] using prepareExponent_run s h9
    rw [power_run ht u m w (digits t) hu3 hu8 hu9 hu7]
    congr 1
    apply BinaryWordMaterialization.toField_injective
    rw [toField_powerWords ht m _ _ hmod, BinaryWordMaterialization.toField_one,
      one_mul, digits_value t ht, BinaryWordMaterialization.toField_inverse]
    apply FiniteFieldInverse.pow_card_sub_two_eq_inv
    · rw [Nat.card_eq_fintype_card, BinaryConcreteField.card_element]
    · intro hzero
      have hwzero : w = BinaryWordMaterialization.zero t :=
        BinaryWordMaterialization.toField_injective
          (hzero.trans BinaryWordMaterialization.toField_zero.symm)
      exact hz ((sum_encode_eq_zero_iff w).mpr hwzero)

theorem sum_bits_le {a : List ℕ} (ha : Bits a) : a.sum ≤ a.length := by
  induction a with
  | nil => simp
  | cons x a ih =>
    have hx := ha x (by simp)
    have ht := ih (fun y hy => ha y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons]
    omega

theorem scanBody_total (st : State 8 11) :
    (scanBody.run st).1.regs 1 + ((scanBody.run st).1.lists 9).sum =
      st.regs 1 + (st.lists 9).sum := by
  rcases h : st.lists 9 with _ | ⟨x, a⟩
  · simp [scanBody, Stmt.run, h, Expr.eval, Function.update]
  · simp [scanBody, Stmt.run, h, Expr.eval, Function.update, Nat.add_assoc]

theorem scanBody_cost (st : State 8 11) (t : ℕ)
    (ht : st.regs 1 + (st.lists 9).sum ≤ t) : (scanBody.run st).2 ≤ 4 * t + 10 := by
  rcases h : st.lists 9 with _ | ⟨x, a⟩
  · have hsz : Nat.size (st.regs 1) ≤ t := (size_le_self _).trans (by simpa [h] using ht)
    simpa [scanBody, Stmt.run, h, Expr.eval, Expr.cost, Expr.readSize, Function.update] using
      (show 1 + (Nat.size (st.regs 1) + (0 + Nat.size (st.regs 1)) + 1) + 1 ≤ 4 * t + 10
        by omega)
  · have hsum : st.regs 1 + x ≤ t := by
      have ht' : st.regs 1 + (x + a.sum) ≤ t := by simpa only [h, List.sum_cons] using ht
      omega
    have hs1 : Nat.size (st.regs 1) ≤ t := (size_le_self _).trans (by omega)
    have hs2 : Nat.size x ≤ t := (size_le_self _).trans (by omega)
    have hs3 : Nat.size (st.regs 1 + x) ≤ t := (size_le_self _).trans hsum
    simpa [scanBody, Stmt.run, h, Expr.eval, Expr.cost, Expr.readSize, Function.update] using
      (show Nat.size x + 1 +
        (Nat.size (st.regs 1) + Nat.size x + Nat.size (st.regs 1 + x) + 1) + 1 ≤ 4 * t + 10
        by omega)

theorem scan_cost {t : ℕ} (st : State 8 11) (w : Word t) (hw : st.lists 8 = encode w) :
    (scan.run st).2 ≤ 20 * (t + 1) ^ 2 := by
  let s := setReg (setReg (setList st 9 (encode w)) 7 t) 1 0
  have hi : s.regs 1 + (s.lists 9).sum ≤ t := by
    simpa [s] using sum_bits_le (encode_bits w)
  have hit := iterate_cost_le scanBody.run (Nat.size t + 1) (4 * t + 10)
    (fun s => s.regs 1 + (s.lists 9).sum ≤ t)
    (fun s hs => by rwa [scanBody_total]) (fun s hs => scanBody_cost s t hs) t s hi
  have hsize := listSize_bits (encode_bits w)
  simp only [encode_length] at hsize
  have hsz := size_le_self t
  simp only [scan, run_seq_snd, run_copy_snd, hw, run_copy_fst, run_len_snd,
    run_len_fst, setList_lists, Function.update_self, encode_length, run_assign_fst,
    Expr.eval, run_loop_snd, setReg_regs,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1)]
  change listSize (encode w) + 1 + (listSize (encode w) + Nat.size t + 1 +
    ((Expr.const 0).cost _ + ((iterate scanBody.run (Nat.size t + 1) t s).2 +
      Nat.size t + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero]
  have hmul := Nat.mul_le_mul_left t hsz
  nlinarith

theorem prepareExponent_cost {t : ℕ} (st : State 8 11) (w : Word t)
    (hw : st.lists 8 = encode w) :
    (prepareExponent.run st).2 ≤ 20 * (t + 1) ^ 2 := by
  let n := t - 1
  let s := setReg (setReg (setReg st 7 t) 2 1) 7 n
  have hit := iterate_cost_le (Stmt.push (9 : Fin 11) (2 : Fin 8)).run
    (Nat.size n + 1) 2 (fun s => s.regs 2 = 1)
    (fun s hs => by simpa [run_push_fst] using hs)
    (fun s hs => by simp [run_push_snd, hs, show Nat.size 1 = 1 from rfl]) n s
    (by simp [s, Function.update])
  have hsize := listSize_bits (encode_bits w)
  simp only [encode_length] at hsize
  have hsz := size_le_self t
  have hn : n ≤ t := Nat.sub_le _ _
  have hnsz : Nat.size n ≤ t := (size_le_self _).trans hn
  simp only [prepareExponent, run_seq_snd, run_len_snd, hw, encode_length,
    run_len_fst, run_assign_fst, Expr.eval, run_loop_snd, run_assign_fst,
    run_push_snd, setReg_regs,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 2), Function.update_self]
  change listSize (encode w) + Nat.size t + 1 + ((Expr.const 1).cost _ +
    ((Expr.sub 7 2).cost (setReg (setReg st 7 t) 2 1).regs +
      ((iterate (Stmt.push 9 2).run (Nat.size n + 1) n s).2 + Nat.size n + 1 +
        ((Expr.const 0).cost _ + (Nat.size 0 + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update_self,
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 2), Nat.size_zero,
    show Nat.size 1 = 1 from rfl]
  have hmul : n * (Nat.size n + 1 + 2) ≤ t * (t + 3) := Nat.mul_le_mul hn (by omega)
  nlinarith

/-- The complete zero-aware inversion program has a quartic charged bound in word length. -/
theorem inverse_cost {t : ℕ} (ht : 0 < t) (st : State 8 11) (m w : Word t)
    (hm : st.lists 3 = encode m) (hw : st.lists 8 = encode w) (he : st.lists 7 = []) :
    (inverse.run st).2 ≤ 250000 * (t + 1) ^ 4 := by
  let s := (scan.run st).1
  have h3 : s.lists 3 = encode m := (run_lists_frame scan 3 (by decide) st).trans hm
  have h8 : s.lists 8 = encode w := (run_lists_frame scan 8 (by decide) st).trans hw
  have h7 : s.lists 7 = [] := (run_lists_frame scan 7 (by decide) st).trans he
  have h1 : s.regs 1 = (encode w).sum := by simpa [hw] using (scan_run st).1
  have h9 : s.lists 9 = [] := (scan_run st).2
  have hscan := scan_cost st w hw
  have hsum : Nat.size (s.regs 1) ≤ t := (size_le_self _).trans (by
    rw [h1]
    simpa only [encode_length] using sum_bits_le (encode_bits w))
  have hwSize := listSize_bits (encode_bits w)
  simp only [encode_length] at hwSize
  rw [inverse, run_seq_snd, run_ite_snd]
  change (scan.run st).2 + ((if s.regs 1 ≠ 0 then ((Stmt.seq prepareExponent power).run s).2
    else ((Stmt.copy 8 1).run s).2) + Nat.size (s.regs 1) + 1) + 1 ≤ _
  split_ifs
  · let u := (prepareExponent.run s).1
    have hu3 : u.lists 3 = encode m :=
      (run_lists_frame prepareExponent 3 (by decide) s).trans h3
    have hu8 : u.lists 8 = encode w :=
      (run_lists_frame prepareExponent 8 (by decide) s).trans h8
    have hu7 : u.lists 7 = [] := (run_lists_frame prepareExponent 7 (by decide) s).trans h7
    have hu9 : u.lists 9 = (digits t).map Bool.toNat := by
      simpa only [h8, encode_length] using prepareExponent_run s h9
    have hp := power_cost ht u m w (digits t) hu3 hu8 hu9 hu7
    rw [digits_length t ht] at hp
    have he := prepareExponent_cost s w h8
    rw [run_seq_snd]
    change (scan.run st).2 + ((prepareExponent.run s).2 + (power.run u).2 + 1 +
      Nat.size (s.regs 1) + 1) + 1 ≤ _
    have hpow : (t + t + 1) ^ 4 ≤ 16 * (t + 1) ^ 4 := by
      calc
        _ ≤ (2 * (t + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        _ = _ := by ring
    have hsquare : (t + 1) ^ 2 ≤ (t + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hlinear : t + 1 ≤ (t + 1) ^ 4 := by
      simpa using (Nat.pow_le_pow_right (n := t + 1) (by omega) (by decide : 1 ≤ 4))
    nlinarith
  · rw [run_copy_snd, h8]
    have hsquare : (t + 1) ^ 2 ≤ (t + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hlinear : t + 1 ≤ (t + 1) ^ 4 := by
      simpa using (Nat.pow_le_pow_right (n := t + 1) (by omega) (by decide : 1 ≤ 4))
    nlinarith

end PCP.Lang.BinaryFieldInverse
