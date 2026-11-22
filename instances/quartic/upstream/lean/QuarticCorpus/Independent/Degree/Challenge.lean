module

public import QuarticCorpus.Independent.Degree.Spec
public import Complexity.Computability.QueryComplexity.Degree

/-! Authored semantic target. The intended challenge hole is not imported by
proof-bearing modules. Only the canonical quantity being checked is shared;
the squarefree coefficient semantics is independently authored in Spec. -/

@[expose] public section

namespace QuarticQuery.Independent.Degree

theorem checked_degree_conventions {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∀ inputSigns outputSigns : Bool,
      ∃ a : Finset (Fin n) → ℝ,
        RepresentsAs inputSigns outputSigns a f ∧
        (∀ b : Finset (Fin n) → ℝ,
          RepresentsAs inputSigns outputSigns b f → b = a) ∧
        (∀ d : ℕ, Cslib.QueryComplexity.degree f ≤ d ↔ CoefficientsAtMost a d) := by
  sorry

end QuarticQuery.Independent.Degree
