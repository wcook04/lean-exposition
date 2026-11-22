module

public import QuarticCorpus.Independent.Degree.Spec
public import Complexity.Computability.QueryComplexity.Degree

/-! Meaningful negative target: a valid existential span theorem omits the
uniqueness and exact degree characterization required by the semantic target.
The duplicate theorem name is deliberate; this module is compiled separately
from the positive bridge. It must be rejected for target-type mismatch. -/

@[expose] public section

namespace QuarticQuery.Independent.Degree

theorem checked_degree_conventions {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ d : ℕ, (fun x => Cslib.BitString.bitVal ℝ (f x)) ∈
      Cslib.BitString.lowDegree ℝ (Fin n) d :=
  ⟨n, by
    simpa using (Cslib.BitString.mem_lowDegree_self
      (fun x => Cslib.BitString.bitVal ℝ (f x)))⟩

end QuarticQuery.Independent.Degree
