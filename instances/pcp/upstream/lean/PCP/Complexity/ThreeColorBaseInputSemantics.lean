import PCP.Complexity.ThreeColorBaseProduction

/-! # Production callback identities at the parser's actual vertex count -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorCanonicalVerifier

attribute [local irreducible] allQueries querySegments allVerdict verdicts
  ThreeColorBaseSeed.sample ComputableThreeColorQueryAlgorithm.queryList
  ComputableThreeColorQueryAlgorithm.verdict

theorem valid_graphOrder_iff (x bits : List Bool) :
    Valid (ThreeColorBaseSeed.sample (graphOrder x) bits) ↔
      Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits) :=
  Iff.of_eq (congrArg (fun N => Valid (ThreeColorBaseSeed.sample N bits)) (graphOrder_eq x))

theorem allQueries_input_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)) :
    allQueries (ThreeColorEncoding.vertexCount x) x bits hv =
      (ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val := by
  have h := allQueries_eq x bits ((valid_graphOrder_iff x bits).mpr hv)
  simpa only [graphOrder_eq] using h

theorem allVerdict_input_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (qs : List ℕ) (bs : List Bool) :
    allVerdict (ThreeColorEncoding.vertexCount x) x bits hv qs bs =
      ComputableThreeColorQueryAlgorithm.verdict x bits
        (QueryTree.wordOfOracle _ (QueryTree.answersOracle qs bs)) := by
  have h := allVerdict_eq x bits ((valid_graphOrder_iff x bits).mpr hv) qs bs
  simpa only [graphOrder_eq] using h

theorem queryList_invalid_input (x bits : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)) :
    ComputableThreeColorQueryAlgorithm.queryList x bits = [] :=
  queryList_of_invalid x bits (fun h => hv ((valid_graphOrder_iff x bits).mp h))

theorem verdict_invalid_input (x bits : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (w : Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x)) → Bool) :
    ComputableThreeColorQueryAlgorithm.verdict x bits w = true :=
  verdict_of_invalid x bits (fun h => hv ((valid_graphOrder_iff x bits).mp h)) w

end PCP.Lang.ThreeColorBaseBranches
