/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteGeneratorSearch

/-!
# Numeric minimality of the production root search

The search visits field elements in increasing coordinate-code order. These
lemmas pin down its result by that order for comparison with language programs.
-/

namespace PCP.Algebraic.FiniteGeneratorSearch

variable {F : Type*} [Field F] [DecidableEq F] {q : ℕ}

theorem scan_le (e : F ≃ Fin q) (p : ℕ) (is : List (Fin q))
    (horder : is.Pairwise (· ≤ ·)) {z : F} (h : scan e p is = some z)
    (i : Fin q) (hi : i ∈ is) (hp : Candidate p (e.symm i)) : e z ≤ i := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    obtain ⟨hj, hs⟩ := List.pairwise_cons.mp horder
    by_cases hpj : Candidate p (e.symm j)
    · have hz : e.symm j = z := by simpa [scan, hpj] using h
      rw [← hz, e.apply_symm_apply]
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_rfl
      · exact hj i hi
    · have htail : scan e p js = some z := by simpa [scan, hpj] using h
      rcases List.mem_cons.mp hi with rfl | hi
      · exact False.elim (hpj hp)
      · exact ih hs htail hi

theorem search_le (e : F ≃ Fin q) (p : ℕ) {z : F}
    (h : search e p = some z) (w : F) (hw : Candidate p w) : e z ≤ e w := by
  apply scan_le e p (List.finRange q) _ h (e w) (List.mem_finRange _) (by simpa using hw)
  change (List.ofFn (fun i : Fin q => i)).Pairwise (· ≤ ·)
  exact List.pairwise_ofFn.mpr fun _ _ hlt => hlt.le

/-- Whenever the root predicate is inhabited, the totalized search returns its least code. -/
theorem root_le (e : F ≃ Fin q) (p : ℕ) (w : F) (hw : Candidate p w) :
    e (root e p) ≤ e w := by
  cases hs : search e p with
  | none => exact False.elim ((search_eq_none_iff e p).mp hs w hw)
  | some z => simpa only [root, hs, Option.getD_some] using search_le e p hs w hw

end PCP.Algebraic.FiniteGeneratorSearch
