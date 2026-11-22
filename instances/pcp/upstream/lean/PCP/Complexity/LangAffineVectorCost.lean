import PCP.Complexity.LangAffineVector

/-!
# Polynomial charged cost of affine coordinate-vector construction
-/

namespace PCP.Lang.AffineVector

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

omit [NeZero t] in
private theorem field_size (a : BinaryMaterializedField.Element t) :
    Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt

theorem scalar_cost (u v a : BinaryMaterializedField.Element t) (st : State 41 17)
    (hc : Context a st) (hu : st.regs 0 = (fieldEquiv t u).val)
    (hv : st.regs 1 = (fieldEquiv t v).val) :
    (scalar.run st).2 ≤ 40000029 * (t + 1) ^ 4 := by
  have hview : View t ![u, v, a]
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    refine ⟨?_, hc.2⟩
    intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hc.1
  have h := FieldExpression.scalar_cost affineTerm
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ![u, v, a] hview
  rw [← scalar_result st] at h
  simpa only [affineTerm, Term.weight, Nat.reduceAdd] using h

theorem body_cost (a : BinaryMaterializedField.Element t)
    (p : BinaryMaterializedField.Element t × BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (out : List ℕ) (st : State 41 17) (hi : Inv a (p :: xs) out st) :
    (body.run st).2 ≤ 50000000 * (t + 1) ^ 4 := by
  let s := setReg (setReg (setList st 14 (leftCodes xs)) 0 (fieldEquiv t p.1).val) 40 1
  let u := setReg (setReg (setList s 15 (rightCodes xs)) 1 (fieldEquiv t p.2).val) 40 1
  have hs : ((Stmt.pop 14 0 40).run st).1 = s := by
    simp [Stmt.run, hi.2.1, leftCodes, s]
  have hu : ((Stmt.pop 15 1 40).run s).1 = u := by
    simp [Stmt.run, s, hi.2.2.1, rightCodes, Function.update, u]
  have hc : Context a u := by simpa [Context, u, s, Function.update] using hi.1
  have h0 : u.regs 0 = (fieldEquiv t p.1).val := by simp [u, s, Function.update]
  have h1 : u.regs 1 = (fieldEquiv t p.2).val := by simp [u, Function.update]
  have hcost := scalar_cost p.1 p.2 a u hc h0 h1
  have hout := (scalar_run p.1 p.2 a u hc h0 h1).1
  have hp0 : ((Stmt.pop 14 0 40).run st).2 = Nat.size (fieldEquiv t p.1).val + 1 := by
    simp [Stmt.run, hi.2.1, leftCodes]
  have hp1 : ((Stmt.pop 15 1 40).run s).2 = Nat.size (fieldEquiv t p.2).val + 1 := by
    simp [Stmt.run, s, hi.2.2.1, rightCodes, Function.update]
  have ha := field_size p.1
  have hb := field_size p.2
  have ho := field_size (p.1 + a * p.2)
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [body, run_seq_snd, hs, hu, run_push_snd, hout, hp0, hp1]
  omega

private theorem iterate_step_cost {R Q : ℕ}
    (f : State R Q → State R Q × ℕ) (c n : ℕ) (st : State R Q) :
    (iterate f c (n + 1) st).2 = c + (f st).2 + (iterate f c n (f st).1).2 := rfl

theorem iterate_cost (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (out : List ℕ) (c : ℕ) (st : State 41 17) (hi : Inv a xs out st) :
    (iterate body.run c xs.length st).2 ≤ xs.length * (c + 50000000 * (t + 1) ^ 4) := by
  induction xs generalizing out st with
  | nil => simp [iterate]
  | cons p xs ih =>
    have hb := body_cost a p xs out st hi
    have hh := ih _ _ (body_step a p xs out st hi)
    rw [List.length_cons, iterate_step_cost, Nat.succ_mul]
    omega

omit [NeZero t] in
private theorem codes_size {α : Type*} (xs : List α) (f : α → BinaryMaterializedField.Element t) :
    listSize (xs.map (fun x => (fieldEquiv t (f x)).val)) ≤ xs.length * (t + 1) := by
  induction xs with
  | nil => simp [listSize]
  | cons x xs ih =>
    have hx := field_size (f x)
    simp only [List.map_cons, List.length_cons, listSize, List.map_cons, List.sum_cons] at ih ⊢
    nlinarith

/-- The source vectors, complete materialized field calls, and final reversal are all charged. -/
theorem program_cost (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (st : State 41 17) (hc : Context a st)
    (hu : st.lists 12 = leftCodes xs) (hv : st.lists 13 = rightCodes xs) :
    (program.run st).2 ≤ 100000000 * (t + xs.length + 1) ^ 5 := by
  let s := setReg (setList (setList (setList st 14 (st.lists 12)) 15 (st.lists 13)) 16 [])
    39 xs.length
  have hi : Inv a xs [] s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Context, s, Function.update] using hc
    · simp [s, Function.update, hu]
    · simp [s, Function.update, hv]
    · simp [s, Function.update]
  have hrun := iterate_run a xs [] (Nat.size xs.length + 1) s hi
  have hcost := iterate_cost a xs [] (Nat.size xs.length + 1) s hi
  have hl := codes_size xs Prod.fst
  have hr := codes_size xs Prod.snd
  have ho := codes_size xs (fun p => p.1 + a * p.2)
  change listSize (leftCodes xs) ≤ _ at hl
  change listSize (rightCodes xs) ≤ _ at hr
  change listSize (values a xs) ≤ _ at ho
  have hrsize : listSize
      ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16) ≤
        xs.length * (t + 1) := by
    rw [hrun.2.2.2, List.append_nil, listSize_reverse]
    exact ho
  have hlength : (st.lists 12).length = xs.length := by simp [hu, leftCodes]
  have hprogram : (program.run st).2 = listSize (st.lists 12) + 1 +
      (listSize (st.lists 13) + 1 + (1 +
        (listSize (st.lists 12) + Nat.size xs.length + 1 +
          ((iterate body.run (Nat.size xs.length + 1) xs.length s).2 +
            Nat.size xs.length + 1 +
              (listSize ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16) + 1)
            + 1) + 1) + 1) + 1) + 1 := by
    simp [program, run_seq_snd, run_copy_snd, run_copy_fst,
      run_len_fst, run_len_snd, run_loop_fst, run_loop_snd, run_rev_snd, listSize,
      Function.update, hc.2.2.2, hlength, s]
  rw [hprogram, hu, hv]
  let N := t + xs.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htN : t + 1 ≤ N := by dsimp [N]; omega
  have hnN : xs.length ≤ N := by dsimp [N]; omega
  have hsize := size_le_self xs.length
  have h4 : (t + 1) ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left htN 4
  have hlin : N ≤ N ^ 4 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 4)
  have hprod : xs.length * N ^ 4 ≤ N ^ 5 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ hnN |>.trans_eq (Nat.mul_comm _ _)
  have hpoly : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by decide)
  have hcost' := hcost.trans (Nat.mul_le_mul_left xs.length
    (Nat.add_le_add_left (Nat.mul_le_mul_left 50000000 h4) _))
  have htn : t + 1 ≤ N ^ 4 := htN.trans hlin
  have hn4 : xs.length ≤ N ^ 4 := hnN.trans hlin
  have hls : xs.length * (t + 1) ≤ N ^ 5 :=
    (Nat.mul_le_mul_left _ htn).trans hprod
  change _ ≤ 100000000 * N ^ 5
  nlinarith

end PCP.Lang.AffineVector
