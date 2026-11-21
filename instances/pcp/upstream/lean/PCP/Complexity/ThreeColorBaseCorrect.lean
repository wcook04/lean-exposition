import PCP.Complexity.ThreeColorBaseProtocol
import PCP.Complexity.ThreeColorBaseInputSemantics
import PCP.Complexity.ThreeColorAmplifiedRuntime

/-! The complete concrete callback implements the production three-color verifier. -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorAmplifiedRuntime

attribute [local irreducible] program allQueries allVerdict

/-- Exact callback behavior on arbitrary graph, seed, and answer words. -/
theorem correct : AmplifiedStream.Correct program queries verdict := by
  classical
  constructor
  intro x bits answers
  have hs := initial_sources x bits answers
  by_cases hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)
  · have hp := program_valid x bits answers hv _ hs
    have hq : allQueries (ThreeColorEncoding.vertexCount x) x bits hv = queries x bits := by
      exact allQueries_input_eq x bits hv
    have ht := allVerdict_input_eq x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) answers
    change allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) answers =
      verdict x bits (QueryTree.answersOracle
        (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) answers) at ht
    rw [hq] at ht
    refine ⟨hp.2.1.trans hq, ?_⟩
    rw [hq] at hp
    exact hp.1.trans (congrArg Bool.toNat ht)
  · have hp := program_invalid x bits answers hv _ hs
    have hq : queries x bits = [] := by
      change (ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val = []
      rw [queryList_invalid_input x bits hv, List.map_nil]
    have ht := verdict_invalid_input x bits hv
      (QueryTree.wordOfOracle _ (QueryTree.answersOracle (queries x bits) answers))
    refine ⟨hp.2.1.trans hq.symm, ?_⟩
    rw [show verdict x bits (QueryTree.answersOracle (queries x bits) answers) = true from ht]
    exact hp.1

end PCP.Lang.ThreeColorBaseBranches
