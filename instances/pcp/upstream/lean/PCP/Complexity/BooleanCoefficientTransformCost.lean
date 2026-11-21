/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientTransform

/-!
# Cost of complete Boolean coefficient recovery with generated masks

The bound is polynomial in the Boolean point-domain size and the binary size of
the degree bound, including both mask enumerations and the stored subset transform.
-/

namespace PCP.Lang.BooleanCoefficientTransform

open PCP.Algebraic BooleanCoefficientList BooleanMask

theorem full_cost (t : ℕ) (st : State 36 8) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (full.run st).2 ≤ 7000000 * (2 ^ t + 3) ^ 4 := by
  let s := setReg st 21 t
  have hc : ((enumerateMasks.rename id fullLists).run s).2 ≤
      400000 * (2 ^ t + Nat.size t + 3) ^ 4 := by
    rw [Stmt.run_rename_cost enumerateMasks id fullLists Function.injective_id fullLists_injective]
    apply enumerateMasks_cost t t
    · simpa [State.restrict, s, Function.update] using ht
    · simp [State.restrict, s]
    · simpa [State.restrict, s, fullLists] using he
  have hsize : Nat.size t ≤ 2 ^ t :=
    (size_le_self _).trans (Nat.lt_two_pow_self (n := t)).le
  have hc' : ((enumerateMasks.rename id fullLists).run s).2 ≤
      6400000 * (2 ^ t + 3) ^ 4 := by
    calc
      _ ≤ 400000 * (2 * (2 ^ t + 3)) ^ 4 :=
        hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
      _ = _ := by ring
  simp only [full, run_seq_snd, run_assign_fst, Expr.eval, ht]
  change (Expr.var 20).cost st.regs + ((enumerateMasks.rename id fullLists).run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, ht]
  nlinarith [Nat.zero_le ((2 ^ t) ^ 4), Nat.zero_le ((2 ^ t) ^ 3), Nat.zero_le ((2 ^ t) ^ 2)]

theorem requested_cost (t r : ℕ) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (he : st.lists 7 = []) :
    (requested.run st).2 ≤ 500000 * (2 ^ t + Nat.size r + 3) ^ 4 := by
  let s := setReg st 21 r
  have hc : ((enumerateMasks.rename id requestedLists).run s).2 ≤
      400000 * (2 ^ t + Nat.size r + 3) ^ 4 := by
    rw [Stmt.run_rename_cost enumerateMasks id requestedLists Function.injective_id
      requestedLists_injective]
    apply enumerateMasks_cost t r
    · simpa [State.restrict, s, Function.update] using ht
    · simp [State.restrict, s]
    · simpa [State.restrict, s, requestedLists] using he
  simp only [requested, run_seq_snd, run_assign_fst, Expr.eval, hr]
  change (Expr.var 23).cost st.regs + ((enumerateMasks.rename id requestedLists).run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hr]
  have hlow : Nat.size r + 3 ≤ (2 ^ t + Nat.size r + 3) ^ 4 :=
    (Nat.add_le_add_right (Nat.le_add_left (Nat.size r) (2 ^ t)) 3).trans (Nat.le_pow (by decide))
  nlinarith only [hc, hlow]

theorem prepare_cost (t r : ℕ) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (he : st.lists 7 = []) :
    (prepare.run st).2 ≤ 8000000 * (2 ^ t + Nat.size r + 3) ^ 4 := by
  have hc := full_cost t st ht he
  have hs20 := run_regs_frame full 20 (by decide) st
  have hs23 := run_regs_frame full 23 (by decide) st
  have hs7 := run_lists_frame full 7 (by decide) st
  simp only [prepare, run_seq_snd]
  generalize hs : (full.run st).1 = s at *
  have hd := requested_cost t r s (hs20.trans ht) (hs23.trans hr) (hs7.trans he)
  have hc' : (full.run st).2 ≤ 7000000 * (2 ^ t + Nat.size r + 3) ^ 4 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have hpos : 1 ≤ (2 ^ t + Nat.size r + 3) ^ 4 := by
    have hb : 0 < 2 ^ t + Nat.size r + 3 := Nat.succ_pos _
    exact Nat.one_le_pow _ _ hb
  omega

theorem masks_size (t r : ℕ) : listSize (masks t r) ≤ 2 ^ t * (2 ^ t + 1) :=
  listSize_masksBelow t r (2 ^ t)

theorem masks_length_le (t r : ℕ) : (masks t r).length ≤ 2 ^ t :=
  (List.length_filter_le _ _).trans (by simp)

theorem table_bits (t : ℕ) (f : (Fin t → ZMod 2) → ZMod 2) :
    ∀ c ∈ table t f, c < 2 := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact ZMod.val_lt _

theorem table_size (t : ℕ) (f : (Fin t → ZMod 2) → ZMod 2) :
    listSize (table t f) ≤ 2 * 2 ^ t := by
  simpa [table] using BinaryField.listSize_bits (table_bits t f)

/-- The complete generated-mask transform has a uniform degree-eight domain-size bound. -/
theorem transform_cost (t r : ℕ) (f : (Fin t → ZMod 2) → ZMod 2) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (hv : st.lists 1 = table t f)
    (he : st.lists 7 = []) :
    (transform.run st).2 ≤ (10000000 + 625 * (BooleanMaskSubset.passConstant + 300)) *
      (2 ^ t + Nat.size r + 3) ^ 8 := by
  have hp := prepare_run t r st ht hr he
  have hc := prepare_cost t r st ht hr he
  have hs20 := run_regs_frame prepare 20 (by decide) st
  have hs1 := run_lists_frame prepare 1 (by decide) st
  have hs7 := run_lists_frame prepare 7 (by decide) st
  simp only [transform, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hs : (prepare.run st).1 = s at *
  let u := setReg s 0 (s.regs 20)
  have hrec : (recovery36.run u).2 ≤ (BooleanMaskSubset.passConstant + 300) *
      (t + listSize (fullMasks t) + listSize (table t f) + (fullMasks t).length +
        listSize (masks t r) + (masks t r).length + 5) ^ 4 := by
    rw [recovery36, Stmt.run_rename_cost BooleanCoefficientRecoveryLang.recover recoveryRegs id
      (show Function.Injective recoveryRegs from Fin.castLE_injective _) Function.injective_id]
    have hh := BooleanCoefficientRecoveryLang.recover_cost (u.restrict recoveryRegs id)
      (by change s.lists 7 = []; exact hs7.trans he)
      (by change ∀ c ∈ s.lists 1, c < 2; rw [hs1, hv]; exact table_bits t f)
    change _ ≤ (BooleanMaskSubset.passConstant + 300) *
      (s.regs 20 + listSize (s.lists 0) + listSize (s.lists 1) + (s.lists 0).length +
        listSize (s.lists 4) + (s.lists 4).length + 5) ^ 4 at hh
    simpa only [hs20, ht, hp.1, hp.2, hs1, hv] using hh
  have hfullSize : listSize (fullMasks t) ≤ 2 ^ t * (2 ^ t + 1) := by
    rw [← masks_full]; exact masks_size t t
  have hfullLen : (fullMasks t).length = 2 ^ t := by simp [fullMasks]
  have hreqSize := masks_size t r
  have hreqLen := masks_length_le t r
  have htable := table_size t f
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hmeasure : t + listSize (fullMasks t) + listSize (table t f) + (fullMasks t).length +
      listSize (masks t r) + (masks t r).length + 5 ≤
        5 * (2 ^ t + Nat.size r + 3) ^ 2 := by
    nlinarith only [hfullSize, hfullLen, hreqSize, hreqLen, htable, htq,
      Nat.zero_le ((2 ^ t) ^ 2), Nat.zero_le ((Nat.size r) ^ 2),
      Nat.zero_le (2 ^ t * Nat.size r)]
  have hrec' : (recovery36.run u).2 ≤ 625 * (BooleanMaskSubset.passConstant + 300) *
      (2 ^ t + Nat.size r + 3) ^ 8 := by
    calc
      _ ≤ (BooleanMaskSubset.passConstant + 300) *
          (5 * (2 ^ t + Nat.size r + 3) ^ 2) ^ 4 :=
        hrec.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmeasure 4))
      _ = _ := by ring
  have hsize : Nat.size (s.regs 20) ≤ 2 ^ t := by rw [hs20, ht]; exact (size_le_self _).trans htq
  change (prepare.run st).2 + ((Expr.var 20).cost s.regs + (recovery36.run u).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  have hpow : (2 ^ t + Nat.size r + 3) ^ 4 ≤ (2 ^ t + Nat.size r + 3) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hlow : 2 ^ t + 3 ≤ (2 ^ t + Nat.size r + 3) ^ 8 :=
    (show 2 ^ t + 3 ≤ 2 ^ t + Nat.size r + 3 by omega).trans (Nat.le_pow (by decide))
  nlinarith only [hc, hrec', hsize, hpow, hlow]

end PCP.Lang.BooleanCoefficientTransform
