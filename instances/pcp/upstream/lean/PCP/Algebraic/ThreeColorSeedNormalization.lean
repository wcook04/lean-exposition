import PCP.Algebraic.ComputableThreeColorQueryAlgorithm
import PCP.Verifier.ReductionResources

/-!
# Surplus-bit invariance of the actual amplified verifier

The executable amplified protocol already decodes its canonical-width seed.
Input reductions may therefore retain the supplied random-bit list verbatim;
no second runtime seed-normalization pass is needed.
-/

namespace PCP.Algebraic.ComputableThreeColorAmplifiedQueryAlgorithm

/-- Canonical normalization of a supplied seed does not change any next-query result. -/
theorem algorithm_normalize (x bits answers : List Bool) :
    algorithm x (PCP.bitsOfFin (ComputableThreeColorAmplifiedVerifier.verifier.randomness x.length)
      (SeedBitCompatibility.decodeSeed
        (ComputableThreeColorAmplifiedVerifier.verifier.randomness x.length) bits)) answers =
      algorithm x bits answers := by
  rw [ComputableThreeColorAmplifiedVerifier.verifier_eq, algorithm_eq]
  simp only [ThreeColorAmplifiedQueryAlgorithm.algorithm,
    ThreeColorAmplifiedQueryAlgorithm.algorithmFor, ThreeColorAmplifiedQueryAlgorithm.blockBits,
    ThreeColorAmplifiedVerifier.verifier, PCP.Verifier.repeat,
    ThreeColorCanonicalVerifier.verifier, SeedBitCompatibility.decodeSeed_bitsOfFin]

/-- Reduce the input while retaining the target algorithm's own seed decoder. -/
def reduceInput (f : List Bool → List Bool) : PCP.VerifierAlg :=
  fun x bits answers => algorithm (f x) bits answers

theorem reduceInput_eq (f : List Bool → List Bool) :
    reduceInput f = PCP.Verifier.Reduction.algorithm algorithm f
      ComputableThreeColorAmplifiedVerifier.verifier.randomness := by
  funext x bits answers
  exact (algorithm_normalize (f x) bits answers).symm

/-- Exact implementation of the canonically padded input-reduced verifier. -/
theorem reduceInput_implementedBy (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, ComputableThreeColorAmplifiedVerifier.verifier.randomness (f x).length ≤
      budget x.length) :
    PCP.Verifier.ImplementedBy
      (PCP.Verifier.Reduction.verifier ComputableThreeColorAmplifiedVerifier.verifier f budget h)
      (reduceInput f) := by
  rw [reduceInput_eq]
  exact PCP.Verifier.Reduction.implementedBy _ _
    ComputableThreeColorAmplifiedVerifier.implementedBy f budget h

end PCP.Algebraic.ComputableThreeColorAmplifiedQueryAlgorithm
