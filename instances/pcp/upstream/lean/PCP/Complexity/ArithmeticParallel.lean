/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticExpressionCost
import Mathlib.Data.List.FinRange

/-!
# Simultaneous arithmetic register updates

All right-hand sides are evaluated before any source register is overwritten.
The temporary expression stack is restored exactly. This supplies a loop-free
implementation of a finite machine's numeric configuration transition.
-/

namespace PCP.Lang.ArithmeticExpression

variable {n : ℕ}

def pushValues : List (Term n) → Stmt (n + 3) 2
  | [] => .skip
  | t :: ts => .seq (compile t) (pushValues ts)

theorem pushValues_inputs (ts : List (Term n)) (st : State (n + 3) 2) :
    (fun i : Fin n => ((pushValues ts).run st).1.regs (i.castAdd 3)) =
      fun i => st.regs (i.castAdd 3) := by
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih =>
      simp only [pushValues, run_seq_fst, ih, compile_inputs]

theorem pushValues_stack (ts : List (Term n)) (st : State (n + 3) 2) :
    ((pushValues ts).run st).1.lists 1 =
      (ts.map (Term.eval (fun i => st.regs (i.castAdd 3)))).reverse ++ st.lists 1 := by
  induction ts generalizing st with
  | nil => simp [pushValues, Stmt.run]
  | cons t ts ih =>
      simp [pushValues, run_seq_fst, ih, compile_inputs, compile_spec, List.reverse_cons,
        List.append_assoc]

theorem pushValues_source (ts : List (Term n)) (st : State (n + 3) 2) :
    ((pushValues ts).run st).1.lists 0 = st.lists 0 := by
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih => simp [pushValues, run_seq_fst, ih, compile_preserves_source]

def popValues : List (Fin n) → Stmt (n + 3) 2
  | [] => .skip
  | i :: is => .seq (.pop 1 (i.castAdd 3) (flagReg n)) (popValues is)

theorem popValues_spec (is : List (Fin n)) (r : Fin n → ℕ)
    (tail : List ℕ) (st : State (n + 3) 2)
    (hs : st.lists 1 = is.map r ++ tail) :
    ((popValues is).run st).1.lists 1 = tail ∧
    ((popValues is).run st).1.lists 0 = st.lists 0 ∧
    ∀ i, ((popValues is).run st).1.regs (i.castAdd 3) =
      if i ∈ is then r i else st.regs (i.castAdd 3) := by
  induction is generalizing st with
  | nil => simpa [popValues, Stmt.run] using hs
  | cons j js ih =>
      let s := ((Stmt.pop 1 (j.castAdd 3) (flagReg n)).run st).1
      have hflag (i : Fin n) : i.castAdd 3 ≠ flagReg n := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, flagReg]
        omega
      have hjf : j.castAdd 3 ≠ flagReg n := hflag j
      have hstack : s.lists 1 = js.map r ++ tail := by
        simp [s, Stmt.run, hs]
      obtain ⟨h1, h0, hr⟩ := ih s hstack
      refine ⟨h1, h0.trans ?_, ?_⟩
      · simp [s, Stmt.run, hs]
      · intro i
        change ((popValues js).run s).1.regs (i.castAdd 3) = _
        rw [hr]
        by_cases hij : i = j
        · subst i
          simp [s, Stmt.run, hs, hflag]
        · have hc : i.castAdd 3 ≠ j.castAdd 3 := by
            simpa only [ne_eq, Fin.ext_iff, Fin.val_castAdd] using hij
          simp [s, Stmt.run, hs, hflag, hc, hij]

/-- Simultaneously replace each input register by its arithmetic right-hand side. -/
def parallel (ts : Fin n → Term n) : Stmt (n + 3) 2 :=
  .seq (pushValues (List.ofFn ts)) (popValues (List.finRange n).reverse)

theorem parallel_spec (ts : Fin n → Term n) (st : State (n + 3) 2) :
    (∀ i, ((parallel ts).run st).1.regs (i.castAdd 3) =
      (ts i).eval (fun j => st.regs (j.castAdd 3))) ∧
    ((parallel ts).run st).1.lists = st.lists := by
  let r := fun i => (ts i).eval (fun j => st.regs (j.castAdd 3))
  have hs : ((pushValues (List.ofFn ts)).run st).1.lists 1 =
      (List.finRange n).reverse.map r ++ st.lists 1 := by
    rw [pushValues_stack]
    simp [List.ofFn_eq_map, List.map_reverse, List.map_map, r, Function.comp_def]
  obtain ⟨h1, h0, hr⟩ := popValues_spec (List.finRange n).reverse r (st.lists 1) _ hs
  refine ⟨?_, ?_⟩
  · intro i
    simpa [parallel, run_seq_fst, r] using hr i
  · funext L
    fin_cases L
    · simpa [parallel, run_seq_fst, pushValues_source] using h0
    · exact h1

@[simp] theorem pushValues_loopFree (ts : List (Term n)) :
    (pushValues ts).loopFree = true := by
  induction ts <;> simp_all [pushValues, Stmt.loopFree]

@[simp] theorem popValues_loopFree (is : List (Fin n)) :
    (popValues is).loopFree = true := by
  induction is <;> simp_all [popValues, Stmt.loopFree]

@[simp] theorem parallel_loopFree (ts : Fin n → Term n) :
    (parallel ts).loopFree = true := by simp [parallel, Stmt.loopFree]

theorem pushValues_uses (ts : List (Term n)) (r : Fin (n + 3))
    (hr : r ∈ (pushValues ts).uses) : ∃ i : Fin n, r = i.castAdd 3 := by
  induction ts with
  | nil => simp [pushValues, Stmt.uses] at hr
  | cons t ts ih =>
      simp only [pushValues, Stmt.uses, List.mem_append, List.mem_filter] at hr
      exact hr.elim (compile_uses t r) (fun h => ih h.1)

@[simp] theorem popValues_uses (is : List (Fin n)) : (popValues is).uses = [] := by
  induction is <;> simp_all [popValues, Stmt.uses]

theorem parallel_uses (ts : Fin n → Term n) (r : Fin (n + 3))
    (hr : r ∈ (parallel ts).uses) : ∃ i : Fin n, r = i.castAdd 3 := by
  exact pushValues_uses _ r (by simpa [parallel, Stmt.uses] using hr)

theorem pushValues_lUses (ts : List (Term n)) (L : Fin 2)
    (hL : L ∈ (pushValues ts).lUses) : L = 1 := by
  induction ts with
  | nil => simp [pushValues, Stmt.lUses] at hL
  | cons t ts ih =>
      simp only [pushValues, Stmt.lUses, List.mem_append] at hL
      exact hL.elim (compile_lUses t L) ih

theorem popValues_lUses (is : List (Fin n)) (L : Fin 2)
    (hL : L ∈ (popValues is).lUses) : L = 1 := by
  induction is with
  | nil => simp [popValues, Stmt.lUses] at hL
  | cons i is ih =>
      simp only [popValues, Stmt.lUses, List.mem_append, List.mem_singleton] at hL
      exact hL.elim id ih

theorem parallel_lUses (ts : Fin n → Term n) (L : Fin 2)
    (hL : L ∈ (parallel ts).lUses) : L = 1 := by
  simp only [parallel, Stmt.lUses, List.mem_append] at hL
  exact hL.elim (pushValues_lUses _ L) (popValues_lUses _ L)

/-- The update costs linearly in the bit widths of the old configuration.
Initial compiler scratch values do not enter the bound. -/
theorem parallel_cost (ts : Fin n → Term n) (st : State (n + 3) 2) (W : ℕ)
    (hr : ∀ i : Fin n, Nat.size (st.regs (i.castAdd 3)) ≤ W)
    (hl : listSize (st.lists 1) ≤ W) :
    ((parallel ts).run st).2 ≤
      (parallel ts).C * ((parallel ts).width + (parallel ts).csize + 1) * (W + 1) := by
  apply loopFree_cost_le (parallel ts) (parallel_loopFree ts) st W
  · intro r hmem
    obtain ⟨i, rfl⟩ := parallel_uses ts r hmem
    exact hr i
  · intro L hmem
    rw [parallel_lUses ts L hmem]
    exact hl

end PCP.Lang.ArithmeticExpression
