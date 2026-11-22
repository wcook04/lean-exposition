import PCP.Complexity.GridFactorCost
import PCP.Complexity.LangRenaming

/-!
# Materialized coordinatewise grid recovery factors

The stored point survives a counted scan. Every coordinate invokes the actual
finite-alphabet product program and the results retain production coordinate order.
-/

namespace PCP.Lang.GridRecovery

open PCP.Algebraic BinaryFieldCode

variable {t : ℕ} [NeZero t]

def scalar : Stmt 41 17 := GridFactor.program.rename
  (Fin.castLE (by decide)) (Fin.castLE (by decide))

def body : Stmt 41 17 := .seq (.pop 14 0 40) (.seq scalar (.push 16 2))

def program : Stmt 41 17 := .seq (.copy 12 14) (.seq (.copy 7 16)
  (.seq (.len 12 39) (.seq (.loop 39 body) (.rev 16))))

def Context (t h : ℕ) [NeZero t] (st : State 41 17) : Prop :=
  st.regs 23 = t ∧ st.regs 31 = h ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

def codes (xs : List (BinaryMaterializedField.Element t)) : List ℕ :=
  xs.map (fun z => (fieldEquiv t z).val)

def values (h : ℕ) (xs : List (BinaryMaterializedField.Element t)) : List ℕ :=
  xs.map (fun z => (fieldEquiv t (GridFactor.value z h)).val)

def Inv (h : ℕ) (xs : List (BinaryMaterializedField.Element t))
    (out : List ℕ) (st : State 41 17) : Prop :=
  Context t h st ∧ st.lists 14 = codes xs ∧ st.lists 16 = out

theorem scalar_result (st : State 41 17) :
    ((scalar.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      (scalar.run st).2) = GridFactor.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  GridFactor.program.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem scalar_list (st : State 41 17) (L : Fin 17) (hL : 12 ≤ L.val) :
    (scalar.run st).1.lists L = st.lists L := by
  unfold scalar
  apply Stmt.run_rename_list_outside
  intro i hi
  have := congrArg Fin.val hi
  simp only [Fin.val_castLE] at this
  omega

theorem scalar_run (h : ℕ) (hh : h ≤ 2 ^ t) (z : BinaryMaterializedField.Element t)
    (st : State 41 17) (hc : Context t h st) (hz : st.regs 0 = (fieldEquiv t z).val) :
    (scalar.run st).1.regs 2 = (fieldEquiv t (GridFactor.value z h)).val ∧
      Context t h (scalar.run st).1 := by
  have hp := GridFactor.program_run z h hh
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) hz hc.1 hc.2.1
    hc.2.2.1 hc.2.2.2
  rw [← scalar_result st] at hp
  exact ⟨hp.2.2.1, hp.2.2.2⟩

theorem body_step (h : ℕ) (hh : h ≤ 2 ^ t) (z : BinaryMaterializedField.Element t)
    (xs : List (BinaryMaterializedField.Element t)) (out : List ℕ)
    (st : State 41 17) (hi : Inv h (z :: xs) out st) :
    Inv h xs ((fieldEquiv t (GridFactor.value z h)).val :: out) (body.run st).1 := by
  let s := setReg (setReg (setList st 14 (codes xs)) 0 (fieldEquiv t z).val) 40 1
  have hs : ((Stmt.pop 14 0 40).run st).1 = s := by
    simp [Stmt.run, hi.2.1, codes, s]
  have hc : Context t h s := by simpa [Context, s, Function.update] using hi.1
  have hr := scalar_run h hh z s hc (by simp [s, Function.update])
  have h14 := scalar_list s 14 (by decide)
  have h16 := scalar_list s 16 (by decide)
  simp only [body, run_seq_fst, hs, run_push_fst]
  generalize hu : (scalar.run s).1 = u at *
  refine ⟨?_, ?_, ?_⟩
  · simpa [Context, Function.update] using hr.2
  · simpa [s, Function.update] using h14
  · simp [hr.1, h16, s, hi.2.2, Function.update]

theorem iterate_run (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (out : List ℕ) (c : ℕ)
    (st : State 41 17) (hi : Inv h xs out st) :
    Inv (t := t) h [] ((values h xs).reverse ++ out) (iterate body.run c xs.length st).1 := by
  induction xs generalizing st out with
  | nil => simpa [values, iterate] using hi
  | cons z xs ih =>
      rw [List.length_cons, iterate_succ_fst]
      have hr := ih _ _ (body_step h hh z xs out st hi)
      simpa [values, List.append_assoc] using hr

/-- Exact output, with the source vector and all field context retained. -/
theorem program_run (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (st : State 41 17)
    (hc : Context t h st) (hx : st.lists 12 = codes xs) :
    (program.run st).1.lists 16 = values h xs ∧
    Context t h (program.run st).1 ∧ (program.run st).1.lists 12 = st.lists 12 := by
  let s := setReg (setList (setList st 14 (st.lists 12)) 16 []) 39 xs.length
  have hi : Inv h xs [] s := by simpa [Inv, Context, s, Function.update, hx] using hc
  have hr := iterate_run h hh xs [] (Nat.size xs.length + 1) s hi
  have heq : (program.run st).1 = setList
      (iterate body.run (Nat.size xs.length + 1) xs.length s).1 16
      ((iterate body.run (Nat.size xs.length + 1) xs.length s).1.lists 16).reverse := by
    simp [program, run_seq_fst, run_copy_fst, run_len_fst, run_loop_fst, run_rev_fst,
      Function.update, hc.2.2.2, hx, codes, s]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    simp [hr.2.2]
  · rw [heq]
    simpa [Context, Function.update] using hr.1
  · apply run_lists_frame
    simp only [program, body, Stmt.listWrites, scalar, Stmt.listWrites_rename,
      List.mem_append, List.mem_map, List.mem_singleton, List.not_mem_nil]
    rintro (h | h | h | h | ⟨i, _, hi⟩ | h | h) <;> try contradiction

end PCP.Lang.GridRecovery
