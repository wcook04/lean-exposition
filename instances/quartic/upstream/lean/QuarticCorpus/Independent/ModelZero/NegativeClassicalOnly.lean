module

public import QuarticCorpus.Independent.ModelZero.Spec
import QuarticCorpus.Independent.ModelZero.Proof

/-! Valid classical theorem, deliberately omitting the quantum clause. -/

@[expose] public section

namespace QuarticQuery.Independent.ModelZero

theorem checked_zero_query_characterization {ι : Type} [Fintype ι] (f : PartialBool ι) :
    (D f = 0 ↔ LabelsAgree f) ∧ (R f = 0 ↔ LabelsAgree f) := by
  exact ⟨D_zero_iff f, R_zero_iff f⟩

end QuarticQuery.Independent.ModelZero
