/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedCardinal

/-!
# Materialized radix construction for a fixed Hadamard row degree

Production uses the two programs at degrees one and three. Only this bounded
syntax depends on the fixed row degree; field width and all cardinalities are
computed from their live inputs.
-/

namespace PCP.Lang.HadamardSeed

variable {t : ℕ}

def degrees (r : ℕ) : List ℕ :=
  (List.ofFn fun k : Fin (r - 1) => k.val + 1) ++ [1, r, r]

theorem degrees_map (t r : ℕ) : (degrees r).map (cardinal t) = radices t r := by
  simp [degrees, radices, Function.comp_def]

def emit (a : ℕ) : Stmt 100 32 := .seq (count a) (.push 25 73)

def emitAll : List ℕ → Stmt 100 32
  | [] => .skip
  | a :: as => .seq (emit a) (emitAll as)

def radixProgram (r : ℕ) : Stmt 100 32 :=
  .seq (.copy 7 25) (.seq (emitAll (degrees r)) (.rev 25))

theorem emit_run (a : ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((emit a).run st).1.lists 25 = cardinal t a :: st.lists 25 ∧
      ((emit a).run st).1.regs 20 = t ∧ ((emit a).run st).1.lists 7 = [] := by
  have h := count_run a st ht he
  have hf := count_frame a st
  simp only [emit, run_seq_fst, run_push_fst]
  exact ⟨by simp only [setList_lists, Function.update_self, h.2, hf.2.2],
    hf.1.trans ht, by simpa [Function.update] using hf.2.1.trans he⟩

theorem emitAll_run (as : List ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((emitAll as).run st).1.lists 25 = (as.map (cardinal t)).reverse ++ st.lists 25 ∧
      ((emitAll as).run st).1.regs 20 = t ∧ ((emitAll as).run st).1.lists 7 = [] := by
  induction as generalizing st with
  | nil => simpa [emitAll, Stmt.run] using And.intro ht he
  | cons a as ih =>
      have h := emit_run a st ht he
      have h' := ih ((emit a).run st).1 h.2.1 h.2.2
      simp only [emitAll, run_seq_fst]
      refine ⟨?_, h'.2⟩
      rw [h'.1, h.1]
      simp [List.reverse_cons, List.append_assoc]

theorem radixProgram_run (r : ℕ) (st : State 100 32) (ht : st.regs 20 = t)
    (he : st.lists 7 = []) :
    ((radixProgram r).run st).1.lists 25 = radices t r ∧
      ((radixProgram r).run st).1.regs 20 = t ∧
      ((radixProgram r).run st).1.lists 7 = [] := by
  have h := emitAll_run (degrees r) (setList st 25 []) ht
    (by simpa [Function.update] using he)
  simp only [setList_lists, Function.update_self, List.append_nil, degrees_map] at h
  simp only [radixProgram, run_seq_fst, run_copy_fst, he]
  generalize hu : ((emitAll (degrees r)).run (setList st 25 [])).1 = u at *
  simp only [run_rev_fst]
  exact ⟨by simp [h.1], h.2.1, by simpa [Function.update] using h.2.2⟩

theorem count_protected (a : ℕ) (st : State 100 32) (i : Fin 100) (hi : 80 ≤ i.val) :
    ((count a).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  have h : ∀ i : Fin 100, 80 ≤ i.val → i ∉ (count 0).regWrites := by decide
  exact h i hi

theorem emitAll_protected (as : List ℕ) (st : State 100 32)
    (i : Fin 100) (hi : 80 ≤ i.val) :
    ((emitAll as).run st).1.regs i = st.regs i := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
      simp only [emitAll, run_seq_fst, ih, emit, run_push_fst, setList_regs]
      exact count_protected a st i hi

theorem radixProgram_protected (r : ℕ) (st : State 100 32)
    (i : Fin 100) (hi : 80 ≤ i.val) :
    ((radixProgram r).run st).1.regs i = st.regs i := by
  simp only [radixProgram, run_seq_fst, run_copy_fst, run_rev_fst, setList_regs]
  exact emitAll_protected _ _ i hi

end PCP.Lang.HadamardSeed
