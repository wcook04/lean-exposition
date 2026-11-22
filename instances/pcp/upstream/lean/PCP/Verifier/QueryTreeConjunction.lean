/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Verifier.QueryList

/-!
# Sequential conjunction of Boolean query trees

Run the second tree only when the first accepts. Iterating this construction
gives a concrete tree for the conjunction of a finite family, with the sum of
the query budgets and no additional proof addresses. This is a deterministic
construction; no sampling, independence, or running-time claim is involved.
-/

namespace PCP.QueryTree

/-- Run the second tree precisely when the first tree accepts. -/
def andThen : {d e : ℕ} → QueryTree d → QueryTree e → QueryTree (d + e)
  | d, _, .leaf b, U => if b then weaken (Nat.le_add_left _ d) U else .leaf false
  | _ + 1, _, .query a f t, U =>
      weaken (by omega) (.query a (andThen f U) (andThen t U))

@[simp] theorem eval_andThen {d e : ℕ} (T : QueryTree d) (U : QueryTree e)
    (π : ProofOracle) : (andThen T U).eval π = (T.eval π && U.eval π) := by
  induction T with
  | leaf b => cases b <;> simp [andThen, eval]
  | query a f t hf ht =>
    simp only [andThen, eval_weaken, eval, hf, ht]
    cases π a <;> rfl

theorem eval_andThen_eq_true_iff {d e : ℕ} (T : QueryTree d) (U : QueryTree e)
    (π : ProofOracle) :
    (andThen T U).eval π = true ↔ T.eval π = true ∧ U.eval π = true := by
  simp

/-- Sequential composition reaches only addresses from its two component trees. -/
theorem addresses_andThen_subset {d e : ℕ} (T : QueryTree d) (U : QueryTree e) :
    (andThen T U).addresses ⊆ T.addresses ∪ U.addresses := by
  induction T with
  | leaf b => cases b <;> simp [andThen, addresses]
  | query a f t hf ht =>
    intro x hx
    simp only [andThen, addresses_weaken, addresses, Finset.mem_insert,
      Finset.mem_union] at hx ⊢
    rcases hx with rfl | hx | hx
    · exact Or.inl (Or.inl rfl)
    · rcases Finset.mem_union.mp (hf hx) with hx | hx
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inr hx
    · rcases Finset.mem_union.mp (ht hx) with hx | hx
      · exact Or.inl (Or.inr (Or.inr hx))
      · exact Or.inr hx

/-- A finite sequence of depth-`q` trees, stopping at its first rejection. -/
def all {q : ℕ} : {k : ℕ} → (Fin k → QueryTree q) → QueryTree (k * q)
  | 0, _ => .leaf true
  | k + 1, T =>
      weaken (by simp [Nat.add_mul, Nat.add_comm])
        (andThen (T 0) (all (fun i : Fin k => T i.succ)))

/-- The conjunction accepts exactly when every component accepts. -/
theorem eval_all_eq_true_iff {k q : ℕ} (T : Fin k → QueryTree q) (π : ProofOracle) :
    (all T).eval π = true ↔ ∀ i, (T i).eval π = true := by
  induction k with
  | zero => simp [all, eval]
  | succ k ih =>
    simp only [all, eval_weaken, eval_andThen, Bool.and_eq_true, ih]
    exact (Fin.forall_fin_succ (P := fun i => (T i).eval π = true)).symm

theorem eval_all {k q : ℕ} (T : Fin k → QueryTree q) (π : ProofOracle) :
    (all T).eval π = decide (∀ i, (T i).eval π = true) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using eval_all_eq_true_iff T π

/-- Every reachable address belongs to at least one of the component trees. -/
theorem addresses_all_subset {k q : ℕ} (T : Fin k → QueryTree q) :
    (all T).addresses ⊆ Finset.univ.biUnion (fun i => (T i).addresses) := by
  induction k with
  | zero => simp [all, addresses]
  | succ k ih =>
    intro a ha
    rw [all, addresses_weaken] at ha
    rcases Finset.mem_union.mp (addresses_andThen_subset _ _ ha) with ha | ha
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ha⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (ih (fun i => T i.succ) ha)
      exact Finset.mem_biUnion.mpr ⟨i.succ, Finset.mem_univ _, hi⟩

/-- A common address bound is preserved, including empty families and zero depth. -/
theorem addresses_all_lt {k q N : ℕ} (T : Fin k → QueryTree q)
    (h : ∀ i, ∀ a ∈ (T i).addresses, a < N) :
    ∀ a ∈ (all T).addresses, a < N := by
  intro a ha
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (addresses_all_subset T ha)
  exact h i a hi

end PCP.QueryTree
