/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedRadices

/-! # Charged costs of constructing the Hadamard seed radices -/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic

variable {t : ℕ}

theorem cardinal_size (t a : ℕ) : Nat.size (cardinal t a) ≤ 2 ^ t + 1 := by
  have h := BooleanCoefficientTransform.masks_length_le t a
  rw [BooleanMask.masks_length] at h
  simp only [cardinal, Nat.size_pow]
  omega

theorem emit_cost (a A : ℕ) (ha : Nat.size a ≤ A) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    ((emit a).run st).2 ≤ 600010 * (2 ^ t + A + 3) ^ 4 := by
  have hc := count_cost a st ht he
  have ho := (count_run a st ht he).2
  have hc' := hc.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega : 2 ^ t + Nat.size a + 3 ≤ 2 ^ t + A + 3) 4))
  have hlow : 2 ^ t + A + 3 ≤ (2 ^ t + A + 3) ^ 4 := Nat.le_pow (by decide)
  simp only [emit, run_seq_snd, run_push_snd, ho]
  have hs := cardinal_size t a
  omega

theorem emitAll_cost (as : List ℕ) (A : ℕ) (ha : ∀ a ∈ as, Nat.size a ≤ A)
    (st : State 100 32) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    ((emitAll as).run st).2 ≤ (as.length + 1) * 600011 * (2 ^ t + A + 3) ^ 4 := by
  induction as generalizing st with
  | nil =>
      change 1 ≤ _
      have hpos : 1 ≤ (2 ^ t + A + 3) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith only [hpos]
  | cons a as ih =>
      have hc := emit_cost a A (ha a (by simp)) st ht he
      have ho := emit_run a st ht he
      have hh := ih (fun b hb => ha b (by simp [hb])) ((emit a).run st).1 ho.2.1 ho.2.2
      have hpos : 1 ≤ (2 ^ t + A + 3) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      simp only [emitAll, run_seq_snd, List.length_cons]
      nlinarith only [hc, hh, hpos]

theorem degrees_bound (r : ℕ) : ∀ a ∈ degrees r, Nat.size a ≤ r + 1 := by
  intro a ha
  apply (size_le_self a).trans
  simp only [degrees, List.mem_append, List.mem_ofFn, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with ⟨k, rfl⟩ | rfl | rfl | rfl <;> omega

theorem radices_size (t r : ℕ) : listSize (radices t r) ≤ (r + 3) * (2 ^ t + 2) := by
  rw [← degrees_map]
  have hb : ∀ a ∈ degrees r, Nat.size (cardinal t a) + 1 ≤ 2 ^ t + 2 := by
    intro a _
    have := cardinal_size t a
    omega
  have hsum := List.sum_le_length_nsmul
    ((degrees r).map fun a => Nat.size (cardinal t a) + 1) (2 ^ t + 2)
    (by simpa only [List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] using hb)
  have h' : listSize ((degrees r).map (cardinal t)) ≤
      (degrees r).length * (2 ^ t + 2) := by
    simpa [listSize, Function.comp_def] using hsum
  have hlen : (degrees r).length ≤ r + 3 := by
    simp only [degrees, List.length_append, List.length_ofFn,
      List.length_cons, List.length_nil]
    omega
  exact h'.trans (Nat.mul_le_mul_right _ hlen)

theorem radixProgram_cost (r : ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((radixProgram r).run st).2 ≤ 700000 * (2 ^ t + r + 4) ^ 5 := by
  let u := setList st 25 []
  have hue : u.lists 7 = [] := by simpa [u, Function.update] using he
  have hc := emitAll_cost (degrees r) (r + 1) (degrees_bound r) u ht hue
  have ho := emitAll_run (degrees r) u ht hue
  have hn : (degrees r).length + 1 ≤ 2 ^ t + r + 4 := by
    simp only [degrees, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    have hnat : r - 1 + (1 + (1 + (1 + 0))) + 1 ≤ r + 4 := by omega
    exact hnat.trans (by simpa only [Nat.add_assoc] using Nat.le_add_left (r + 4) (2 ^ t))
  have hc' : ((emitAll (degrees r)).run u).2 ≤ 600011 * (2 ^ t + r + 4) ^ 5 := by
    have hbase : 2 ^ t + (r + 1) + 3 = 2 ^ t + r + 4 := by omega
    rw [hbase] at hc
    calc
      _ ≤ ((2 ^ t + r + 4) * 600011) * (2 ^ t + r + 4) ^ 4 :=
        hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 600011 hn))
      _ = _ := by ring
  have hs : listSize (((emitAll (degrees r)).run u).1.lists 25) ≤
      (r + 3) * (2 ^ t + 2) := by
    rw [ho.1, show u.lists 25 = [] from rfl, List.append_nil, listSize_reverse, degrees_map]
    exact radices_size t r
  have h2 : (2 ^ t + r + 4) ^ 2 ≤ (2 ^ t + r + 4) ^ 5 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  simp only [radixProgram, run_seq_snd, run_copy_snd, run_copy_fst, he, run_rev_snd]
  change 1 + (((emitAll (degrees r)).run u).2 +
    (listSize (((emitAll (degrees r)).run u).1.lists 25) + 1) + 1) + 1 ≤ _
  nlinarith only [hc', hs, h2, Nat.zero_le ((2 ^ t) ^ 2), Nat.zero_le (r ^ 2)]

end PCP.Lang.HadamardSeed
