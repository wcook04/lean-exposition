/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialMaterialization

/-!
# Cost of stored fixed-width binary serialization and modulus construction

The serializer bound is polynomial in the requested width and the bit size of
the input number. It is reusable for finite seed words as well as field words.
-/

namespace PCP.Lang.BinaryPolynomialSelector

open PCP.Algebraic

theorem extractBody_cost (st : State 36 2) (b : ℕ)
    (h0 : st.regs 0 = 2) (hb : Nat.size (st.regs 34) ≤ b) :
    (extractBody.run st).2 ≤ 20 * (b + 1) := by
  have hm : Nat.size (st.regs 34 % 2) ≤ 1 :=
    size_le_one_of_le_one (by have := Nat.mod_lt (st.regs 34) (by decide : 0 < 2); omega)
  have hd : Nat.size (st.regs 34 / 2) ≤ b :=
    (Nat.size_le_size (Nat.div_le_self _ _)).trans hb
  simp only [extractBody, Expr.eval,
    Stmt.run, setReg_regs, setList_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    Expr.cost, Expr.readSize, h0, show Nat.size 2 = 2 from rfl]
  omega

/-- An arbitrary natural is serialized with its high zero bits retained. -/
theorem materialize_cost (st : State 36 2) (h0 : st.lists 0 = []) :
    (materialize.run st).2 ≤ 100 * (st.regs 20 + Nat.size (st.regs 33) + 1) ^ 2 := by
  let t := st.regs 20
  let b := Nat.size (st.regs 33)
  let s := setReg (setReg (setList st 1 []) 34 (st.regs 33)) 0 2
  have hit := iterate_cost_le extractBody.run (Nat.size t + 1) (20 * (b + 1))
    (fun u => u.regs 0 = 2 ∧ Nat.size (u.regs 34) ≤ b)
    (by
      intro u hu
      obtain ⟨_, hr, htwo⟩ := extractBody_step u hu.1
      refine ⟨htwo, ?_⟩
      rw [hr]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hu.2)
    (fun u hu => extractBody_cost u b hu.1 hu.2) t s
    (by simp [s, b, Function.update])
  have hout : (iterate extractBody.run (Nat.size t + 1) t s).1.lists 1 =
      (digits t (st.regs 33)).reverse := by
    simpa using extract_iterate (Nat.size t + 1) t s (st.regs 33) []
      (by simp [s]) (by simp [s, Function.update]) (by simp [s])
  have hlist : listSize ((iterate extractBody.run (Nat.size t + 1) t s).1.lists 1) ≤ 2 * t := by
    rw [hout, listSize_reverse]
    simpa using BinaryField.listSize_bits (digits_bits t (st.regs 33))
  have hsz : Nat.size t ≤ t := size_le_self _
  simp only [materialize, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    run_loop_fst, run_rev_snd, run_copy_fst, run_copy_snd, h0, setReg_regs,
    setList_regs, Function.update, Fin.reduceEq, dite_false]
  change (listSize ([] : List ℕ) + 1) + ((Expr.var 33).cost (setList st 1 []).regs +
    ((Expr.const 2).cost _ + (((iterate extractBody.run (Nat.size t + 1) t s).2 +
      Nat.size t + 1) + (listSize ((iterate extractBody.run (Nat.size t + 1) t s).1.lists 1) + 1)
        + 1) + 1) + 1) + 1 ≤ _
  simp only [show listSize ([] : List ℕ) = 0 from rfl, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, show Nat.size 2 = 2 from rfl]
  change _ ≤ 100 * (t + b + 1) ^ 2
  have hb : t * (Nat.size t + 1 + 20 * (b + 1)) ≤ t * (t + 1 + 20 * (b + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hb' := hit.trans hb
  have hbdef : Nat.size (st.regs 33) = b := rfl
  nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le (b ^ 2)]

/-- Selecting and materializing the production modulus has polynomial charged cost. -/
theorem fieldModulus_cost (t : ℕ) (ht : 0 < t) (st : State 36 2)
    (h20 : st.regs 20 = t) (h0 : st.lists 0 = []) :
    (fieldModulus.run st).2 ≤ 7000000 * (2 ^ t + 1) ^ 7 := by
  have hselect := selectPolynomial_cost t st h20
  have hs20 := run_regs_frame selectPolynomial 20 (by decide) st
  have hs0 := run_lists_frame selectPolynomial 0 (by decide) st
  have hs33 := selectPolynomial_run t ht st h20
  simp only [fieldModulus, run_seq_snd]
  generalize hs : (selectPolynomial.run st).1 = s at *
  have hm := materialize_cost s (hs0.trans h0)
  rw [hs20, h20, hs33] at hm
  have hsize : Nat.size (BinaryIrreduciblePolynomial.selectedCode t ht).val ≤ 2 ^ t :=
    (size_le_self _).trans (BinaryIrreduciblePolynomial.selectedCode t ht).isLt.le
  have htq : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have hm' : (materialize.run s).2 ≤ 100 * (2 * 2 ^ t + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  nlinarith [Nat.zero_le ((2 ^ t) ^ 7), Nat.zero_le ((2 ^ t) ^ 6),
    Nat.zero_le ((2 ^ t) ^ 5), Nat.zero_le ((2 ^ t) ^ 4),
    Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

end PCP.Lang.BinaryPolynomialSelector
