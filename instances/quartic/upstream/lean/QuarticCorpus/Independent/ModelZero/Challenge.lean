module

public import QuarticCorpus.Independent.ModelZero.Spec

/-! Specification-only challenge. The intentional `sorry` is not a proof. -/

@[expose] public section

namespace QuarticQuery.Independent.ModelZero

theorem checked_zero_query_characterization {ι : Type} [Fintype ι] (f : PartialBool ι) :
    (D f = 0 ↔ LabelsAgree f) ∧
    (R f = 0 ↔ LabelsAgree f) ∧
    (Q f = 0 ↔ LabelsAgree f) := by
  sorry

end QuarticQuery.Independent.ModelZero
