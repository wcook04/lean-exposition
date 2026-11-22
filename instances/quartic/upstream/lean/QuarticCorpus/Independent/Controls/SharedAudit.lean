module

public import QuarticCorpus.Independent.Semantics
public import QuarticCorpus.Independent.Controls.SharedSolution

/-! A separate semantic expectation distinguishes a shared bad specification
from the actual project's predicate: one has a concrete witness, the other has
none. This file contains proved detection goals, not intentionally failing code.
Native validation: `research/adjudication/round3_formal.json`. -/

@[expose] public section
set_option autoImplicit false

namespace Round3.SharedAudit

theorem actual_comparison_has_witness :
    ∃ a : Fin 2 → Fin 2 → ℝ, QuarticQuery.Tournament.IsComparison a :=
  QuarticQuery.SemanticReview.comparison_has_witness

theorem shared_bad_spec_has_no_witness :
    ¬ ∃ a : Fin 2 → Fin 2 → ℝ, SharedBadSpec.IsComparison a := by
  rintro ⟨a, ha⟩
  exact ha.impossible

theorem independently_expected_matrix_fails_shared_bad_spec :
    ¬ SharedBadSpec.IsComparison QuarticQuery.SemanticReview.fairComparison := by
  intro h
  exact h.impossible

end Round3.SharedAudit
