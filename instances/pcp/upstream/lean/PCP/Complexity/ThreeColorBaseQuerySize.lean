import PCP.Complexity.ThreeColorBaseProduction
import PCP.Complexity.ThreeColorQuerySize

/-! # Uniform storage bounds for the executed seven-branch physical trace -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorCanonicalVerifier

attribute [local irreducible] proofBound allQueries querySegments ThreeColorBaseSeed.sample
  ComputableThreeColorQueryAlgorithm.queryList

theorem allQueries_size (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)) :
    listSize (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) ≤
      187*(proofBound.eval x.length+1) := by
  have hv' : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits) :=
    (congrArg (fun N => Valid (ThreeColorBaseSeed.sample N bits)) (graphOrder_eq x)).mpr hv
  have h := allQueries_eq x bits hv'
  simp only [graphOrder_eq] at h
  rw [h]
  exact ThreeColorQuerySize.queryList_size x bits

theorem polynomial_allQueries_size : ∃ C d : ℕ, ∀ (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)),
    listSize (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) ≤
      C*(x.length+1)^d := by
  obtain ⟨C,d,hC⟩ := ThreeColorQuerySize.polynomial_queryList_size
  refine ⟨C,d,fun x bits hv => ?_⟩
  have hv' : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits) :=
    (congrArg (fun N => Valid (ThreeColorBaseSeed.sample N bits)) (graphOrder_eq x)).mpr hv
  have h := allQueries_eq x bits hv'
  simp only [graphOrder_eq] at h
  rw [h]
  exact hC x bits

end PCP.Lang.ThreeColorBaseBranches
