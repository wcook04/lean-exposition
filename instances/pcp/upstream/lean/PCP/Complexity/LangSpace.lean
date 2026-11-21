import PCP.Complexity.Lang

/-!
# Data sizes are bounded by the charged cost

The first resource invariant for COMPILE. `State.Sized B` bounds every natural register's bit size
and every list register's entire encoded size. Executing any statement, including nested counted
loops, increases this bound by at most its actual cost. There is no loop-free hypothesis and no
assumption about distinct source/destination registers.

This is a statement about the language semantics, not a machine implementation. `LangStep.lean`
uses it to bound the data at every intermediate configuration of an operational execution.
-/

namespace PCP.Lang

variable {R Q : ℕ}

/-- A uniform bound on register bit sizes and whole list sizes. -/
def State.Sized (st : State R Q) (B : ℕ) : Prop :=
  (∀ x, Nat.size (st.regs x) ≤ B) ∧ ∀ L, listSize (st.lists L) ≤ B

theorem State.Sized.mono {st : State R Q} {B C : ℕ} (h : st.Sized B) (hBC : B ≤ C) :
    st.Sized C :=
  ⟨fun x => Nat.le_trans (h.1 x) hBC, fun L => Nat.le_trans (h.2 L) hBC⟩

theorem State.Sized.setReg {st : State R Q} {B : ℕ} (h : st.Sized B) (x : Fin R) (v : ℕ)
    (hv : Nat.size v ≤ B) : (setReg st x v).Sized B := by
  refine ⟨fun y => ?_, h.2⟩
  simp only [setReg_regs, Function.update_apply]
  split_ifs with hy
  · exact hv
  · exact h.1 y

theorem State.Sized.setList {st : State R Q} {B : ℕ} (h : st.Sized B) (L : Fin Q) (l : List ℕ)
    (hl : listSize l ≤ B) : (setList st L l).Sized B := by
  refine ⟨h.1, fun M => ?_⟩
  simp only [setList_lists, Function.update_apply]
  split_ifs with hM
  · exact hl
  · exact h.2 M

/-- Iteration accumulates size growth additively, just as it accumulates cost. -/
theorem iterate_sized (f : State R Q → State R Q × ℕ) (c : ℕ)
    (hf : ∀ st B, st.Sized B → (f st).1.Sized (B + (f st).2)) :
    ∀ n st B, st.Sized B → (iterate f c n st).1.Sized (B + (iterate f c n st).2) := by
  intro n
  induction n with
  | zero => intro st B h; simpa [iterate] using h
  | succ n ih =>
    intro st B h
    have hnext := ih (f st).1 (B + (f st).2) (hf st B h)
    exact hnext.mono (by simp only [iterate]; omega)

/-- **All statements preserve the input-size-plus-cost bound**, with arbitrary loop nesting. -/
theorem Stmt.run_sized (s : Stmt R Q) :
    ∀ st B, st.Sized B → (s.run st).1.Sized (B + (s.run st).2) := by
  induction s with
  | skip => intro st B h; exact h.mono (by simp [Stmt.run])
  | seq s t ihs iht =>
    intro st B h
    have ht := iht (s.run st).1 (B + (s.run st).2) (ihs st B h)
    exact ht.mono (by rw [run_seq_snd]; omega)
  | assign x e =>
    intro st B h
    exact (h.mono (Nat.le_add_right _ _)).setReg x (e.eval st.regs)
      (by simp only [Stmt.run, Expr.cost]; omega)
  | push L x =>
    intro st B h
    apply (h.mono (Nat.le_add_right _ _)).setList L (st.regs x :: st.lists L)
    have := h.2 L
    simp only [Stmt.run, listSize, List.map_cons, List.sum_cons] at *
    omega
  | pop L x flag =>
    intro st B h
    cases hl : st.lists L with
    | nil =>
      simp only [Stmt.run, hl]
      exact ((h.mono (by omega)).setReg x 0 (by simp)).setReg flag 0 (by simp)
    | cons v l =>
      simp only [Stmt.run, hl]
      have ht : listSize l ≤ B := by
        have := h.2 L
        simp only [hl, listSize, List.map_cons, List.sum_cons] at this ⊢
        omega
      exact (((h.mono (by omega)).setList L l (by omega)).setReg x v (by omega)).setReg
        flag 1 (by simp; omega)
  | len L x =>
    intro st B h
    exact (h.mono (Nat.le_add_right _ _)).setReg x (st.lists L).length
      (by simp only [Stmt.run]; omega)
  | rev L =>
    intro st B h
    apply (h.mono (Nat.le_add_right _ _)).setList L (st.lists L).reverse
    rw [listSize_reverse]
    exact Nat.le_trans (h.2 L) (Nat.le_add_right _ _)
  | copy L M =>
    intro st B h
    apply (h.mono (Nat.le_add_right _ _)).setList M (st.lists L)
    exact Nat.le_trans (h.2 L) (Nat.le_add_right _ _)
  | revApp L M =>
    intro st B h
    apply (h.mono (Nat.le_add_right _ _)).setList M ((st.lists L).reverse ++ st.lists M)
    have := h.2 M
    simp only [listSize, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
      Stmt.run] at *
    omega
  | ite x s t ihs iht =>
    intro st B h
    simp only [Stmt.run]
    split_ifs
    · exact (ihs st B h).mono (by omega)
    · exact (iht st B h).mono (by omega)
  | loop x s ih =>
    intro st B h
    exact (iterate_sized s.run _ ih (st.regs x) st B h).mono
      (by rw [run_loop_snd]; omega)

/-- Even an empty loop or a `skip` pays for a control step. -/
theorem Stmt.run_cost_pos (s : Stmt R Q) (st : State R Q) : 0 < (s.run st).2 := by
  cases s <;> simp only [Stmt.run, Expr.cost]
  all_goals first | omega | (split <;> omega)

theorem Prog.init_sized (P : Prog) (l : List ℕ) : (P.init l).Sized (listSize l) := by
  refine ⟨fun x => by simp [Prog.init], fun L => ?_⟩
  simp only [Prog.init]
  split_ifs
  · exact Nat.le_refl _
  · simp [listSize]

/-- The entire output is paid for by the input and the program's actual cost. -/
theorem Prog.run_listSize_le (P : Prog) (l : List ℕ) :
    listSize (P.run l) ≤ listSize l + P.cost l :=
  (P.body.run_sized (P.init l) (listSize l) (P.init_sized l)).2 P.outL

end PCP.Lang
