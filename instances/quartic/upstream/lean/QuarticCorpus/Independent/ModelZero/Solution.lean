module

public import QuarticCorpus.Independent.ModelZero.Spec
import QuarticCorpus.Independent.ModelZero.Proof

@[expose] public section

namespace QuarticQuery.Independent.ModelZero

theorem checked_zero_query_characterization {ι : Type} [Fintype ι] (f : PartialBool ι) :
    (D f = 0 ↔ LabelsAgree f) ∧
    (R f = 0 ↔ LabelsAgree f) ∧
    (Q f = 0 ↔ LabelsAgree f) := by
  exact zero_query_characterization f

end QuarticQuery.Independent.ModelZero
