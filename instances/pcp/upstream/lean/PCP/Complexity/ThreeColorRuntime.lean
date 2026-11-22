import PCP.Complexity.ThreeColorBaseCorrect
import PCP.Complexity.ThreeColorBasePolynomial

/-! The fixed algebraic verifier has a concrete polynomial-time machine. -/

namespace PCP.Lang.ThreeColorRuntime

open PCP.Algebraic

/-- Complete runtime certificate for the production amplified verifier. -/
theorem polyTimeAlg :
    Machine.PolyTimeAlg ComputableThreeColorAmplifiedQueryAlgorithm.algorithm := by
  obtain ⟨C,d,hC⟩ := ThreeColorBaseBranches.program_polynomial_cost
  exact ThreeColorAmplifiedRuntime.of_callback ThreeColorBaseBranches.program
    ThreeColorBaseBranches.correct C d hC

end PCP.Lang.ThreeColorRuntime
