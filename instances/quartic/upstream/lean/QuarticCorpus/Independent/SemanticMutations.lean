module

public import QuarticCorpus.Independent.Semantics

/-! Native validation: `research/adjudication/round3_formal.json`. Positive detection theorems for deliberately bad
semantic alternatives. These are not claims that Comparator has run. -/

@[expose] public section
set_option autoImplicit false

namespace QuarticQuery.SemanticReview

/-- Reversing the algorithm/input quantifiers wrongly allows an algorithm to
choose its constant answer after seeing the input. -/
theorem input_dependent_program_mutant_accepts_identity :
    ∀ x b, oneBitIdentity x = some b →
      ∃ A : RandomizedProgram (Fin 1),
        A.depth ≤ 0 ∧ (2 / 3 : ℝ) ≤ A.success x b := by
  intro x b hb
  refine ⟨RandomizedProgram.ofTree (.leaf b), by simp, ?_⟩
  rw [RandomizedProgram.success_ofTree]
  norm_num [QueryTree.eval]

theorem wrong_quantifier_order_changes_answer :
    (∀ x b, oneBitIdentity x = some b →
      ∃ A : RandomizedProgram (Fin 1),
        A.depth ≤ 0 ∧ (2 / 3 : ℝ) ≤ A.success x b) ∧
    ¬ RLe oneBitIdentity 0 :=
  ⟨input_dependent_program_mutant_accepts_identity, identity_not_zero⟩

/-- The chosen mixture sits on the inclusive boundary at input 00. -/
theorem strict_threshold_mutant_rejects_mixture :
    ¬ (∀ x b, orTwo x = some b → (2 / 3 : ℝ) < orMixture.success x b) := by
  intro h
  have hbad := h (fun _ => false) false rfl
  have heq : orMixture.success (fun _ => false) false = (2 / 3 : ℝ) := by
    simpa using orMixture_success (fun _ => false)
  rw [heq] at hbad
  exact (lt_irrefl _) hbad

/-- Deliberately wrong high branch: taking the absolute numerator erases the
sign distinction in the actual preprint promise. -/
def absoluteHighPromise (k t : ℕ) : PartialBool (ForrelationCoord k t) := fun z =>
  let n := forrelationNumerator k t z
  let d := forrelationDenominator k t
  if (2 : ℤ) ^ (5 * k) * |n| ≥ d then some true
  else if (2 : ℤ) ^ (5 * k + 1) * |n| ≤ d then some false
  else none

theorem absolute_high_mutant_accepts_negative :
    absoluteHighPromise 2 1 negativePair = some true := by
  decide +kernel

theorem absolute_high_changes_answer :
    absoluteHighPromise 2 1 negativePair ≠ P 2 1 negativePair := by
  rw [absolute_high_mutant_accepts_negative, negativePair_P_none]
  decide

/-- Declaring the off-promise input to have value false makes this particular
promise the total identity, whose zero-query impossibility was proved above. -/
def offPromiseFalse : PartialBool (Fin 1) :=
  fun x => some ((trueOnly x).getD false)

theorem off_promise_false_changes_zero_query_answer :
    RLe trueOnly 0 ∧ ¬ RLe offPromiseFalse 0 := by
  refine ⟨trueOnly_RLe_zero, ?_⟩
  exact both_labels_preclude_zero offPromiseFalse
    (fun _ => false) (fun _ => true) rfl rfl

end QuarticQuery.SemanticReview
