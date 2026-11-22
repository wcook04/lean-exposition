import PCP.Algebraic.ComputableThreeColorQueryAlgorithm

/-!
# Exact history slicing for sequential verifier repetition
-/

namespace PCP.QueryTree

/-- A completed accepting copy passes exactly its unconsumed answers to the next copy. -/
theorem thenStep_listStep (qs : List ℕ) (f : ProofOracle → Bool)
    (next : List Bool → Bool ⊕ ℕ) (as : List Bool) :
    thenStep qs f next as =
      match listStep qs f as with
      | .inl b => if b then next (as.drop qs.length) else .inl false
      | .inr q => .inr q := by
  induction qs generalizing f as with
  | nil => simp [thenStep, listStep]
  | cons q qs ih =>
      cases as with
      | nil => rfl
      | cons b bs =>
          simpa only [thenStep, listStep, List.length_cons, List.drop_succ_cons] using
            (ih (fun π => f (Function.update π q b)) bs)

/-- One copy's complete observable behavior, including surplus and short histories. -/
theorem thenStep_slicing (qs : List ℕ) (f : ProofOracle → Bool)
    (next : List Bool → Bool ⊕ ℕ) (as : List Bool) :
    thenStep qs f next as =
      if h : as.length < qs.length then .inr qs[as.length]
      else if f (answersOracle qs as) then next (as.drop qs.length) else .inl false := by
  rw [thenStep_listStep]
  by_cases h : as.length < qs.length
  · rw [listStep_next qs f as h, dite_eq_left h]
  · rw [listStep_halt qs f as (by omega), dite_eq_right h]

end PCP.QueryTree
