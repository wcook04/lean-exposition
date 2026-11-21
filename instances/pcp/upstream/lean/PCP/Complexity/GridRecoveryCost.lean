import PCP.Complexity.GridRecoveryLang

/-! # Charged polynomial cost of the entire stored grid recovery vector -/

namespace PCP.Lang.GridRecovery

open PCP.Algebraic BinaryFieldCode

variable {t : ℕ} [NeZero t]

theorem scalar_cost (h : ℕ) (hh : h ≤ 2 ^ t) (z : BinaryMaterializedField.Element t)
    (st : State 41 17) (hc : Context t h st) (hz : st.regs 0 = (fieldEquiv t z).val) :
    (scalar.run st).2 ≤ 60000000 * (h + t + 1) ^ 5 := by
  have hp := GridFactor.program_cost z h hh
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) hz hc.1 hc.2.1
    hc.2.2.1 hc.2.2.2
  rw [← scalar_result st] at hp
  exact hp

theorem body_cost (h : ℕ) (hh : h ≤ 2 ^ t) (z : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t)) (out : List ℕ)
    (st : State 41 17) (hi : Inv h (z :: xs) out st) :
    (body.run st).2 ≤ 60000010 * (h + t + 1) ^ 5 := by
  let s := setReg (setReg (setList st 14 (codes xs)) 0 (fieldEquiv t z).val) 40 1
  have hs : ((Stmt.pop 14 0 40).run st).1 = s := by
    simp [Stmt.run, hi.2.1, codes, s]
  have hc : Context t h s := by simpa [Context, s, Function.update] using hi.1
  have hz : s.regs 0 = (fieldEquiv t z).val := by simp [s, Function.update]
  have hr := (scalar_run h hh z s hc hz).1
  have hp := scalar_cost h hh z s hc hz
  have hin : Nat.size (fieldEquiv t z).val ≤ t := Nat.size_le.mpr (fieldEquiv t z).isLt
  have hout : Nat.size (fieldEquiv t (GridFactor.value z h)).val ≤ t :=
    Nat.size_le.mpr (fieldEquiv t (GridFactor.value z h)).isLt
  have hpop : ((Stmt.pop 14 0 40).run st).2 = Nat.size (fieldEquiv t z).val + 1 := by
    simp [Stmt.run, hi.2.1, codes]
  have hlin : h + t + 1 ≤ (h + t + 1) ^ 5 := Nat.le_self_pow (by decide) _
  simp only [body, run_seq_snd, hs, run_push_snd, hr, hpop]
  omega

theorem iterate_cost (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (out : List ℕ) (c : ℕ)
    (st : State 41 17) (hi : Inv h xs out st) :
    (iterate body.run c xs.length st).2 ≤ xs.length * (c + 60000010 * (h + t + 1) ^ 5) := by
  induction xs generalizing st out with
  | nil => simp [iterate]
  | cons z xs ih =>
      have hb := body_cost h hh z xs out st hi
      have ht := ih _ _ (body_step h hh z xs out st hi)
      change c + (body.run st).2 + (iterate body.run c xs.length (body.run st).1).2 ≤ _
      simp only [List.length_cons]
      nlinarith

omit [NeZero t] in
theorem codes_size (xs : List (BinaryMaterializedField.Element t)) :
    listSize (codes xs) ≤ xs.length * (t + 1) := by
  induction xs with
  | nil => simp [codes, listSize]
  | cons z xs ih =>
      have hz : Nat.size (fieldEquiv t z).val ≤ t := Nat.size_le.mpr (fieldEquiv t z).isLt
      simp only [codes, List.map_cons, listSize, List.sum_cons, List.length_cons] at ih ⊢
      nlinarith

theorem values_size (h : ℕ) (xs : List (BinaryMaterializedField.Element t)) :
    listSize (values h xs) ≤ xs.length * (t + 1) := by
  have hp := codes_size (xs.map fun z => GridFactor.value z h)
  simpa only [codes, List.map_map, Function.comp_def, values, List.length_map] using hp

/-- Every scalar field product is computed, and the retained source and result lists are charged. -/
theorem program_cost (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (st : State 41 17)
    (hc : Context t h st) (hx : st.lists 12 = codes xs) :
    (program.run st).2 ≤ 100000000 * (h + t + xs.length + 1) ^ 6 := by
  let s := setReg (setList (setList st 14 (st.lists 12)) 16 []) 39 xs.length
  have hi : Inv h xs [] s := by simpa [Inv, Context, s, Function.update, hx] using hc
  have hr := iterate_run h hh xs [] (Nat.size xs.length + 1) s hi
  have hp := iterate_cost h hh xs [] (Nat.size xs.length + 1) s hi
  have hxs := codes_size xs
  have hv := values_size h xs
  have hsize : listSize
      ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16) ≤
        xs.length * (t + 1) := by
    rw [hr.2.2, List.append_nil, listSize_reverse]
    exact hv
  have hlength : (st.lists 12).length = xs.length := by simp [hx, codes]
  have hprogram : (program.run st).2 = listSize (st.lists 12) + 1 +
      (1 + (listSize (st.lists 12) + Nat.size xs.length + 1 +
        ((iterate body.run (Nat.size xs.length + 1) xs.length s).2 +
          Nat.size xs.length + 1 +
          (listSize ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16) + 1)
        + 1) + 1) + 1) + 1 := by
    simp [program, run_seq_snd, run_copy_snd, run_copy_fst, run_len_fst, run_len_snd,
      run_loop_snd, run_loop_fst, run_rev_snd, listSize, Function.update,
      hc.2.2.2, hlength, s]
  rw [hprogram, hx]
  let N := h + t + xs.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htN : h + t + 1 ≤ N := by dsimp [N]; omega
  have hnN : xs.length ≤ N := by dsimp [N]; omega
  have hnat := size_le_self xs.length
  have h5 : (h + t + 1) ^ 5 ≤ N ^ 5 := Nat.pow_le_pow_left htN 5
  have hlin : N ≤ N ^ 5 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 5)
  have hprod : xs.length * N ^ 5 ≤ N ^ 6 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ hnN |>.trans_eq (Nat.mul_comm _ _)
  have hpoly : N ^ 5 ≤ N ^ 6 := Nat.pow_le_pow_right hN (by decide)
  have hpc := hp.trans (Nat.mul_le_mul_left xs.length
    (Nat.add_le_add_left (Nat.mul_le_mul_left 60000010 h5) _))
  have htn : t + 1 ≤ N ^ 5 := (show t + 1 ≤ N by dsimp [N]; omega).trans hlin
  have hn5 : xs.length ≤ N ^ 5 := hnN.trans hlin
  have hls : xs.length * (t + 1) ≤ N ^ 6 :=
    (Nat.mul_le_mul_left _ htn).trans hprod
  change _ ≤ 100000000 * N ^ 6
  nlinarith

end PCP.Lang.GridRecovery
