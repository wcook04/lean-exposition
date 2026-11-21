/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanMaskEnumeration

/-!
# Cost of increasing coefficient-mask enumeration

The bound is polynomial in the full mask domain and the bit size of the degree
bound. Stored-list reversal and every population-count call are included.
-/

namespace PCP.Lang.BooleanMask

open BinaryPolynomialSelector

theorem digits_sum_le (t n : ℕ) : (digits t n).sum ≤ t := by
  induction t generalizing n with
  | zero => simp [digits]
  | succ t ih =>
    simp only [digits, List.sum_cons]
    have hm := Nat.mod_lt n (by decide : 0 < 2)
    have hh := ih (n / 2)
    omega

theorem listSize_masksBelow (t r n : ℕ) : listSize (masksBelow t r n) ≤ n * (n + 1) := by
  have hb : ∀ x ∈ masksBelow t r n, Nat.size x + 1 ≤ n + 1 := by
    intro x hx
    have hx' : x < n := List.mem_range.mp (List.mem_of_mem_filter hx)
    exact Nat.add_le_add_right ((size_le_self _).trans hx'.le) 1
  have hgeneral : ∀ xs : List ℕ, (∀ x ∈ xs, Nat.size x + 1 ≤ n + 1) →
      listSize xs ≤ xs.length * (n + 1) := by
    intro xs
    induction xs with
    | nil => simp [listSize]
    | cons x xs ih =>
      intro hx
      have hhead := hx x (by simp)
      have htail := ih (fun y hy => hx y (by simp [hy]))
      simp only [listSize, List.map_cons, List.sum_cons, List.length_cons] at htail ⊢
      nlinarith
  have hs := hgeneral (masksBelow t r n) hb
  have hl : (masksBelow t r n).length ≤ n := by
    exact (List.length_filter_le _ _).trans (by simp)
  exact hs.trans (Nat.mul_le_mul_right _ hl)

theorem countMask_cost (st : State 36 2) (t : ℕ)
    (ht : st.regs 20 = t) (hi : st.regs 32 < 2 ^ t) :
    (countMask.run st).2 ≤ 200 * (2 * t + 1) ^ 2 := by
  let s := setReg (setReg st 0 t) 1 (st.regs 32)
  have hsz : Nat.size (st.regs 32) ≤ t := Nat.size_le.mpr hi
  have hc : (count36.run s).2 ≤ 100 * (t + Nat.size (st.regs 32) + 1) ^ 2 := by
    rw [count36, Stmt.run_rename_cost popcount countRegs countLists
      (show Function.Injective countRegs from Fin.castLE_injective _)
      (show Function.Injective countLists from Fin.castLE_injective _)]
    simpa [s, State.restrict, Function.update, countRegs] using
      popcount_cost (s.restrict countRegs countLists)
  have hc' : (count36.run s).2 ≤ 100 * (2 * t + 1) ^ 2 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hst : Nat.size t ≤ t := size_le_self _
  simp only [countMask, run_seq_snd, run_assign_fst, Expr.eval, ht]
  change (Expr.var 20).cost st.regs + ((Expr.var 32).cost (setReg st 0 t).regs +
    (count36.run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, ht]
  nlinarith

theorem appendTail_cost (st : State 36 2) (t r : ℕ)
    (h2 : st.regs 2 ≤ t) (h22 : st.regs 22 = r + 1)
    (hi : st.regs 32 < 2 ^ t) (h35 : st.regs 35 = 1) :
    (appendTail.run st).2 ≤ 100000 * (t + Nat.size r + 3) := by
  have hrsize : Nat.size (r + 1) ≤ Nat.size r + 2 := by
    simpa only [show Nat.size 1 = 1 from rfl, Nat.add_assoc] using size_add_le r 1
  have hc := loopFree_cost_le appendTail (by decide) st (t + Nat.size r + 2)
    (by
      intro x hx
      have hu : appendTail.uses = [2, 22, 32, 32, 35] := rfl
      rw [hu] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact (size_le_self _).trans (h2.trans (by omega))
      · rw [h22]; omega
      · exact (Nat.size_le.mpr hi).trans (by omega)
      · exact (Nat.size_le.mpr hi).trans (by omega)
      · rw [h35]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega))
    (by simp [appendTail, Stmt.lUses])
  have hC : appendTail.C * (appendTail.width + appendTail.csize + 1) ≤ 100000 := by decide
  exact hc.trans (by simpa only [Nat.add_assoc] using
    Nat.mul_le_mul_right (t + Nat.size r + 2 + 1) hC)

theorem enumerationBody_cost (t r : ℕ) (st : State 36 2)
    (hc : EnumContext t r (2 ^ t) st) (hi : st.regs 32 < 2 ^ t) :
    (enumerationBody.run st).2 ≤ 200000 * (t + Nat.size r + 3) ^ 2 := by
  have hcount := countMask_cost st t hc.1 hi
  have hs2 := countMask_run st
  rw [hc.1] at hs2
  have hs22 := run_regs_frame countMask 22 (by decide) st
  have hs32 := run_regs_frame countMask 32 (by decide) st
  have hs35 := run_regs_frame countMask 35 (by decide) st
  simp only [enumerationBody, run_seq_snd]
  generalize hs : (countMask.run st).1 = s at *
  have htail := appendTail_cost s t r (by rw [hs2]; exact digits_sum_le _ _)
    (hs22.trans hc.2.2.1) (by simpa only [hs32] using hi) (hs35.trans hc.2.2.2.2)
  nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le ((Nat.size r) ^ 2)]

theorem gatherMasks_cost (t r : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = r) (h28 : st.regs 28 = 2 ^ t)
    (he : st.lists 0 = []) :
    (gatherMasks.run st).2 ≤ 300000 * (2 ^ t + Nat.size r + 3) ^ 4 := by
  let q := 2 ^ t
  let b := Nat.size r
  let s := setReg (setReg (setReg (setList st 1 []) 35 1) 22 (r + 1)) 32 0
  have hinit : EnumContext t r q s ∧ s.regs 32 = 0 ∧
      s.lists 1 = (masksBelow t r 0).reverse := by
    simp [EnumContext, s, Function.update, h20, h21, h28, q, masksBelow]
  have hit := iterate_cost_idx enumerationBody.run (Nat.size q + 1)
    (200000 * (t + b + 3) ^ 2) q
    (fun n u => EnumContext t r q u ∧ u.regs 32 = n ∧
      u.lists 1 = (masksBelow t r n).reverse)
    (by
      intro n u hn hu
      exact ⟨enumerationBody_inv t r q n u hu.1 hu.2.1 hu.2.2,
        enumerationBody_cost t r u hu.1 (by rw [hu.2.1]; exact hn)⟩) s hinit
  have hout := iterate_inv enumerationBody.run (Nat.size q + 1) q
    (fun n u => EnumContext t r q u ∧ u.regs 32 = n ∧
      u.lists 1 = (masksBelow t r n).reverse)
    (fun n u _ hu => enumerationBody_inv t r q n u hu.1 hu.2.1 hu.2.2) s hinit
  have hlist : listSize ((iterate enumerationBody.run (Nat.size q + 1) q s).1.lists 1) ≤
      q * (q + 1) := by
    rw [hout.2.2, listSize_reverse]
    exact listSize_masksBelow t r q
  have hsz : Nat.size q ≤ q := size_le_self _
  have htq : t ≤ q := (Nat.lt_two_pow_self (n := t)).le
  have hrsize : Nat.size (r + 1) ≤ b + 2 := by
    simpa only [show Nat.size 1 = 1 from rfl, Nat.add_assoc] using size_add_le r 1
  have hit' : (iterate enumerationBody.run (Nat.size q + 1) q s).2 ≤
      q * (q + 1 + 200000 * (q + b + 3) ^ 2) := hit.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add (by omega)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))))
  simp only [gatherMasks, run_seq_snd, run_copy_snd, run_copy_fst,
    run_assign_fst, Expr.eval, run_loop_snd, run_loop_fst, run_rev_snd,
    setReg_regs, setList_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    he, h21, h28]
  change (listSize ([] : List ℕ) + 1) + ((Expr.const 1).cost _ +
    ((Expr.add 21 35).cost (setReg (setList st 1 []) 35 1).regs +
      ((Expr.const 0).cost _ + (((iterate enumerationBody.run (Nat.size q + 1) q s).2 +
        Nat.size q + 1) +
        (listSize ((iterate enumerationBody.run (Nat.size q + 1) q s).1.lists 1) + 1) + 1)
        + 1) + 1) + 1) + 1 ≤ _
  simp only [show listSize ([] : List ℕ) = 0 from rfl, Expr.cost, Expr.readSize,
    Expr.eval, setReg_regs, setList_regs, Function.update, Fin.reduceEq, dite_true,
    dite_false, h21, Nat.size_zero, Nat.size_one]
  change _ ≤ 300000 * (q + b + 3) ^ 4
  have hb : Nat.size r = b := rfl
  nlinarith [Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3), Nat.zero_le (b ^ 4),
    Nat.zero_le (b ^ 3), Nat.zero_le (q ^ 2 * b ^ 2)]

/-- A uniform polynomial bound includes computing the full mask-domain size. -/
theorem enumerateMasks_cost (t r : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = r) (he : st.lists 0 = []) :
    (enumerateMasks.run st).2 ≤ 400000 * (2 ^ t + Nat.size r + 3) ^ 4 := by
  have hc := cardinality_cost st t h20
  have hs20 := run_regs_frame cardinality 20 (by decide) st
  have hs21 := run_regs_frame cardinality 21 (by decide) st
  have hs0 := run_lists_frame cardinality 0 (by decide) st
  have hs28 := cardinality_run st
  rw [h20] at hs28
  simp only [enumerateMasks, run_seq_snd]
  generalize hs : (cardinality.run st).1 = s at *
  have hg := gatherMasks_cost t r s (hs20.trans h20) (hs21.trans h21) hs28 (hs0.trans he)
  have hbase : (2 ^ t + 1) ^ 2 ≤ (2 ^ t + Nat.size r + 3) ^ 4 := by
    calc
      _ ≤ (2 ^ t + Nat.size r + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (2 ^ t + Nat.size r + 3) ^ 4 :=
        Nat.pow_le_pow_right (by omega) (by decide)
  have hpositive : 1 ≤ (2 ^ t + Nat.size r + 3) ^ 4 :=
    Nat.one_le_pow _ _ (by omega)
  omega

end PCP.Lang.BooleanMask
