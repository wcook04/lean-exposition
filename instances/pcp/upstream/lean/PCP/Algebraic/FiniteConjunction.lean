/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteDistance
import Mathlib.Logic.Equiv.Prod

/-!
# Conjoining tests with independent finite seeds

The complete seed contains one independent seed for each test, even when the
individual seed types have different cardinalities. Each branch's normalized
rejection is bounded by that of the conjunction, with no sampling-weight loss.
-/

namespace PCP.Algebraic.FiniteConjunction

variable {I : Type*} {Seed : I → Type*}

/-- Turning equality with an accepted answer into a Boolean verdict preserves rejection. -/
theorem distance_decide_eq {S B : Type*} [Fintype S] [DecidableEq B]
    (f : S → B) (a : B) :
    relativeDistance (fun s => decide (f s = a)) (fun _ => true) =
      relativeDistance f (fun _ => a) := by
  apply le_antisymm
  · apply relativeDistance_le_of_disagreement
    intro s hs he
    exact hs (by simp only [he, decide_true])
  · apply relativeDistance_le_of_disagreement
    intro s hs he
    exact hs (of_decide_eq_true he)

/-- Run every branch with its own seed and accept exactly when all accept. -/
noncomputable def test (checks : ∀ i, Seed i → Bool) (s : ∀ i, Seed i) : Bool := by
  classical
  exact decide (∀ i, checks i (s i) = true)

@[simp] theorem test_eq_true (checks : ∀ i, Seed i → Bool) (s : ∀ i, Seed i) :
    test checks s = true ↔ ∀ i, checks i (s i) = true := by
  classical
  simp only [test, decide_eq_true_eq]

/-- Branchwise agreement determines the combined verdict. -/
theorem test_congr (checks checks' : ∀ i, Seed i → Bool) (s : ∀ i, Seed i)
    (h : ∀ i, checks i (s i) = checks' i (s i)) : test checks s = test checks' s := by
  unfold test
  congr 1
  simp only [h]

variable [Fintype I] [DecidableEq I] [∀ i, Fintype (Seed i)]

/-- Actual rejection over the full product of branch seeds. -/
noncomputable def rejectionRate (checks : ∀ i, Seed i → Bool) : ℚ :=
  relativeDistance (test checks) (fun _ => true)

theorem rejectionRate_nonneg (checks : ∀ i, Seed i → Bool) :
    0 ≤ rejectionRate checks := relativeDistance_nonneg _ _

variable [∀ i, Nonempty (Seed i)]

/-- Projecting a uniform dependent product onto one coordinate is exactly uniform. -/
theorem relativeDistance_apply {B : Type*} [DecidableEq B] (i : I) (f g : Seed i → B) :
    relativeDistance (fun s : ∀ i, Seed i => f (s i)) (fun s => g (s i)) =
      relativeDistance f g := by
  let e := Equiv.piSplitAt i Seed
  have h := relativeDistance_comp_equiv e
    (fun p : Seed i × (∀ j : {j // j ≠ i}, Seed j) => f p.1) (fun p => g p.1)
  exact h.trans (relativeDistance_comp_fst f g)

/-- Failure of any branch forces failure of the actual conjunction. -/
theorem branch_rejection_le (checks : ∀ i, Seed i → Bool) (i : I) :
    relativeDistance (checks i) (fun _ => true) ≤ rejectionRate checks := by
  rw [← relativeDistance_apply (Seed := Seed) i (checks i) (fun _ => true)]
  apply relativeDistance_le_of_disagreement
  intro s hs ht
  exact hs ((test_eq_true checks s).mp ht i)

omit [∀ i, Nonempty (Seed i)] in
/-- Pointwise completeness of every branch gives zero actual rejection. -/
theorem rejectionRate_eq_zero (checks : ∀ i, Seed i → Bool)
    (h : ∀ i s, checks i s = true) : rejectionRate checks = 0 := by
  apply relativeDistance_eq_zero_iff.mpr
  funext s
  exact (test_eq_true checks s).mpr (fun i => h i (s i))

end PCP.Algebraic.FiniteConjunction
