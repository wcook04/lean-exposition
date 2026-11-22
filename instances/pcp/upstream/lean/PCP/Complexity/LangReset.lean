import PCP.Complexity.LangRenaming

/-!
# Fresh workspace initialization for repeated subprogram calls

Only the designated finite register and list sets are cleared. An external empty
list supplies the zeros for list storage and remains outside the cleared set.
-/

namespace PCP.Lang.Reset

variable {R Q : ℕ}

def regs : List (Fin R) → Stmt R Q
  | [] => .skip
  | r :: rs => .seq (.assign r (.const 0)) (regs rs)

def lists (empty : Fin Q) : List (Fin Q) → Stmt R Q
  | [] => .skip
  | q :: qs => .seq (.copy empty q) (lists empty qs)

theorem regs_run (rs : List (Fin R)) (st : State R Q) :
    (regs rs).run st =
      (⟨fun r => if r ∈ rs then 0 else st.regs r, st.lists⟩, 2*rs.length+1) := by
  induction rs generalizing st with
  | nil => simp [regs, Stmt.run]
  | cons r rs ih =>
      simp only [regs, Stmt.run, Expr.eval, ih, Expr.cost, Expr.readSize, Nat.size_zero]
      congr 1
      · congr 1
        funext i
        simp only [List.mem_cons, setReg_regs, Function.update_apply]
        split_ifs <;> simp_all
      · simp [List.length_cons]
        omega

theorem lists_run (empty : Fin Q) (qs : List (Fin Q)) (st : State R Q)
    (he : st.lists empty = []) (hne : empty ∉ qs) :
    (lists empty qs).run st =
      (⟨st.regs, fun q => if q ∈ qs then [] else st.lists q⟩, 2*qs.length+1) := by
  induction qs generalizing st with
  | nil => simp [lists, Stmt.run]
  | cons q qs ih =>
      have hq : empty ≠ q := by simp only [List.mem_cons, not_or] at hne; exact hne.1
      have he' : (setList st q []).lists empty = [] := by
        simp [Function.update, hq, he]
      have ht : empty ∉ qs := fun h => hne (List.mem_cons_of_mem q h)
      simp only [lists, Stmt.run, he, ih _ he' ht,
        show listSize ([] : List ℕ) = 0 from rfl]
      congr 1
      · congr 1
        funext i
        simp only [List.mem_cons, setList_lists, Function.update_apply]
        split_ifs <;> simp_all
      · simp [List.length_cons]
        omega

end PCP.Lang.Reset
