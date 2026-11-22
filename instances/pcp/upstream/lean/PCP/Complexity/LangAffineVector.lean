import PCP.Complexity.InterpolationWeightLang

/-!
# Affine combinations of stored coordinate vectors

The source lists survive. Working copies feed the same materialized field
expression at every coordinate; the result is stored in original coordinate order.
-/

namespace PCP.Lang.AffineVector

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

def scalar : Stmt 41 17 :=
  (FieldExpression.scalar affineTerm).rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def body : Stmt 41 17 := .seq (.pop 14 0 40)
  (.seq (.pop 15 1 40) (.seq scalar (.push 16 29)))

def program : Stmt 41 17 := .seq (.copy 12 14) (.seq (.copy 13 15)
  (.seq (.copy 7 16) (.seq (.len 12 39) (.seq (.loop 39 body) (.rev 16)))))

def Context (a : BinaryMaterializedField.Element t) (st : State 41 17) : Prop :=
  st.regs 2 = (fieldEquiv t a).val ∧ st.regs 23 = t ∧
  st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

def leftCodes (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t)) :
    List ℕ := xs.map (fun p => (fieldEquiv t p.1).val)

def rightCodes (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t)) :
    List ℕ := xs.map (fun p => (fieldEquiv t p.2).val)

def values (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t)) : List ℕ :=
  xs.map (fun p => (fieldEquiv t (p.1 + a * p.2)).val)

def Inv (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (out : List ℕ) (st : State 41 17) : Prop :=
  Context a st ∧ st.lists 14 = leftCodes xs ∧ st.lists 15 = rightCodes xs ∧ st.lists 16 = out

theorem scalar_result (st : State 41 17) :
    ((scalar.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      (scalar.run st).2) = (FieldExpression.scalar affineTerm).run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  unfold scalar
  exact Stmt.run_rename _ _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem scalar_list (st : State 41 17) (L : Fin 17) (hL : 12 ≤ L.val) :
    (scalar.run st).1.lists L = st.lists L := by
  unfold scalar
  apply Stmt.run_rename_list_outside
  intro i h
  have := congrArg Fin.val h
  simp only [Fin.val_castLE] at this
  omega

theorem scalar_run (u v a : BinaryMaterializedField.Element t) (st : State 41 17)
    (hc : Context a st) (hu : st.regs 0 = (fieldEquiv t u).val)
    (hv : st.regs 1 = (fieldEquiv t v).val) :
    (scalar.run st).1.regs 29 = (fieldEquiv t (u + a * v)).val ∧
      Context a (scalar.run st).1 := by
  have hview : View t ![u, v, a]
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    refine ⟨?_, hc.2⟩
    intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hc.1
  have h := FieldExpression.scalar_spec affineTerm
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ![u, v, a] hview
  rw [← scalar_result st] at h
  have hi := h.2.2.1 (2 : Fin 3)
  have hw := h.2.2.2
  simp only [State.restrict_regs, State.restrict_lists,
    show Fin.castLE (by decide : 39 ≤ 41) (slot 3 26) = (29 : Fin 41) from rfl,
    show Fin.castLE (by decide : 39 ≤ 41) (slot 3 20) = (23 : Fin 41) from rfl,
    show Fin.castLE (by decide : 12 ≤ 17) (3 : Fin 12) = (3 : Fin 17) from rfl,
    show Fin.castLE (by decide : 12 ≤ 17) (7 : Fin 12) = (7 : Fin 17) from rfl] at h hw
  generalize hout : (scalar.run st).1 = w at *
  constructor
  · simpa only [affineTerm_eval] using h.1
  · refine ⟨?_, hw⟩
    exact hi

theorem body_step (a : BinaryMaterializedField.Element t)
    (p : BinaryMaterializedField.Element t × BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (out : List ℕ) (st : State 41 17) (hi : Inv a (p :: xs) out st) :
    Inv a xs ((fieldEquiv t (p.1 + a * p.2)).val :: out) (body.run st).1 := by
  let s := setReg (setReg (setList st 14 (leftCodes xs)) 0 (fieldEquiv t p.1).val) 40 1
  let u := setReg (setReg (setList s 15 (rightCodes xs)) 1 (fieldEquiv t p.2).val) 40 1
  have hs : ((Stmt.pop 14 0 40).run st).1 = s := by
    simp [Stmt.run, hi.2.1, leftCodes, s]
  have hu : ((Stmt.pop 15 1 40).run s).1 = u := by
    simp [Stmt.run, s, hi.2.2.1, rightCodes, Function.update, u]
  have hc : Context a u := by simpa [Context, u, s, Function.update] using hi.1
  have hr := scalar_run p.1 p.2 a u hc
    (by simp [u, s, Function.update]) (by simp [u, Function.update])
  have hl14 := scalar_list u 14 (by decide)
  have hl15 := scalar_list u 15 (by decide)
  have hl16 := scalar_list u 16 (by decide)
  simp only [body, run_seq_fst, hs, hu, run_push_fst]
  generalize hw : (scalar.run u).1 = w at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Context, Function.update] using hr.2
  · simpa [u, s, Function.update] using hl14
  · simpa [u, Function.update] using hl15
  · simp [Function.update, hr.1, hl16, u, s, hi.2.2.2]

theorem iterate_run (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (out : List ℕ) (c : ℕ) (st : State 41 17) (hi : Inv a xs out st) :
    Inv a [] ((values a xs).reverse ++ out) (iterate body.run c xs.length st).1 := by
  induction xs generalizing out st with
  | nil => simpa [values, iterate] using hi
  | cons p xs ih =>
    rw [List.length_cons, iterate_succ_fst]
    have h := ih _ _ (body_step a p xs out st hi)
    simpa [values, List.append_assoc] using h

/-- Exact coordinatewise affine combination, with source vectors retained. -/
theorem program_run (a : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t × BinaryMaterializedField.Element t))
    (st : State 41 17) (hc : Context a st)
    (hu : st.lists 12 = leftCodes xs) (hv : st.lists 13 = rightCodes xs) :
    (program.run st).1.lists 16 = values a xs ∧ Context a (program.run st).1 ∧
    (program.run st).1.lists 12 = st.lists 12 ∧ (program.run st).1.lists 13 = st.lists 13 := by
  let s := setReg (setList (setList (setList st 14 (st.lists 12)) 15 (st.lists 13)) 16 [])
    39 xs.length
  have hi : Inv a xs [] s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Context, s, Function.update] using hc
    · simp [s, Function.update, hu]
    · simp [s, Function.update, hv]
    · simp [s, Function.update]
  have hr := iterate_run a xs [] (Nat.size xs.length + 1) s hi
  have hf : (program.run st).1 = setList
      (iterate body.run (Nat.size xs.length + 1) xs.length s).1 16
      ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16).reverse := by
    simp [program, run_seq_fst, run_copy_fst, run_len_fst, run_loop_fst, run_rev_fst,
      Function.update, hc.2.2.2, hu, leftCodes, s]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]
    simp [Function.update, hr.2.2.2]
  · rw [hf]
    simpa [Context, Function.update] using hr.1
  · apply run_lists_frame
    simp only [program, body, Stmt.listWrites, scalar, Stmt.listWrites_rename,
      List.mem_append, List.mem_map, List.mem_singleton, List.not_mem_nil]
    rintro (h | h | h | h | h | ⟨L, _, h⟩ | h | h) <;> try contradiction
  · apply run_lists_frame
    simp only [program, body, Stmt.listWrites, scalar, Stmt.listWrites_rename,
      List.mem_append, List.mem_map, List.mem_singleton, List.not_mem_nil]
    rintro (h | h | h | h | h | ⟨L, _, h⟩ | h | h) <;> try contradiction

/-- The coordinate list agrees with the line-query point at every dimension. -/
theorem program_point {d : ℕ} (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (st : State 41 17)
    (hc : Context a st)
    (hu : st.lists 12 = List.ofFn (fun i => (fieldEquiv t (u i)).val))
    (hv : st.lists 13 = List.ofFn (fun i => (fieldEquiv t (v i)).val)) :
    (program.run st).1.lists 16 = List.ofFn
      (fun i => (fieldEquiv t (PolynomialLine.point u v a i)).val) := by
  have h := (program_run a (List.ofFn (fun i => (u i, v i))) st hc
    (by simpa [leftCodes, Function.comp_def] using hu)
    (by simpa [rightCodes, Function.comp_def] using hv)).1
  simpa [values, PolynomialLine.point, Function.comp_def] using h

end PCP.Lang.AffineVector
