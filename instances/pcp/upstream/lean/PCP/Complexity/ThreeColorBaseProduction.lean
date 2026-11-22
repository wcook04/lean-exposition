import PCP.Complexity.ThreeColorBasePass
import PCP.Complexity.ThreeColorProductionCode
import PCP.Complexity.DerivedGridQuerySemantics
import PCP.Complexity.ProductionEdgeLang
import PCP.Algebraic.ComputableThreeColorQueryAlgorithm

/-! # Exact production interpretation of the seven concrete base-verifier branches -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  ThreeColorCanonicalVerifier LocalCorrection

theorem weight_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits)) :
    DerivedSeed.weight .proper (size (exponent (graphOrder x)))
      (size_le_fieldCode (exponent (graphOrder x))) x
      (ThreeColorBaseDerived.sample .proper (graphOrder x) bits hv) =
      FieldQueryArithmetic.edgeValue (grid (exponent (graphOrder x)))
        (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
        (ThreeColorBaseDerived.sample .proper (graphOrder x) bits hv).1 := by
  let a := exponent (graphOrder x)
  let z := (ThreeColorBaseDerived.sample .proper (graphOrder x) bits hv).1
  have hcode := congrArg (fun e : Field a ≃ Fin (2^binaryDimension a) =>
    FieldQueryArithmetic.edgeValue (FiniteAlphabetIndex.alphabet e (size_le_fieldCode a))
      (ThreeColorGridIndex.pad (FiniteAlphabetIndex.code e (size_le_fieldCode a))
        (size a) (ThreeColorEncoding.graph x)) z) (ProductionGrid.fieldEquiv_eq_fieldCode a)
  have hgraph := congrArg (fun G => ThreeColorVerifier.edgeValue (grid a) G z)
    (ProductionGrid.canonical_gridGraph x)
  exact hcode.trans ((FieldQueryArithmetic.edgeValue_eq _ _ _).trans
    (hgraph.symm.trans (FieldQueryArithmetic.edgeValue_eq _ _ _).symm))

theorem querySegments_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits)) (i : Fin 7) :
    querySegments (graphOrder x) x bits hv i =
      (ComputableThreeColorVerifier.branchQueries (coordinates (exponent (graphOrder x)))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x)) i
        (unpad (ThreeColorBaseSeed.sample (graphOrder x) bits) hv i)).map
          (fun q => (ThreeColorBinaryVerifier.addressEquiv (graphOrder x) q).val) := by
  have hraw : querySegments (graphOrder x) x bits hv i =
      (ComputableThreeColorVerifier.branchQueries (coordinates (exponent (graphOrder x)))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x)) i
        (unpad (ThreeColorBaseSeed.sample (graphOrder x) bits) hv i)).map queryCode := by
    fin_cases i
    · change ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 3)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .color (graphOrder x) bits)).map
          OuterBranch.Kind.color.query).map queryCode =
        ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 3)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .color (graphOrder x) bits)).map
          ThreeColorVerifier.colorQuery).map queryCode
      congr 2
      funext q
      exact OuterBranch.Kind.query_color q
    · change ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 1)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .valid (graphOrder x) bits)).map
          OuterBranch.Kind.valid.query).map queryCode =
        ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 1)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .valid (graphOrder x) bits)).map
          ThreeColorVerifier.validQuery).map queryCode
      congr 2
      funext q
      exact OuterBranch.Kind.query_valid q
    · change ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 3)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .difference (graphOrder x) bits)).map
          OuterBranch.Kind.difference.query).map queryCode =
        ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 3)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .difference (graphOrder x) bits)).map
          ThreeColorVerifier.differenceQuery).map queryCode
      congr 2
      funext q
      exact OuterBranch.Kind.query_difference q
    · change ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 1)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .proper (graphOrder x) bits)).map
          OuterBranch.Kind.proper.query).map queryCode =
        ((ComputableEncodedLineLowDegreeTest.queries (by decide : 1 ≤ 1)
        (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
        (generator (exponent (graphOrder x)))
        (ThreeColorBaseOuter.sample .proper (graphOrder x) bits)).map
          ThreeColorVerifier.properQuery).map queryCode
      congr 2
      funext q
      exact OuterBranch.Kind.query_proper q
    · change DerivedGrid.queries .valid _ _ _ _ _ = _
      erw [DerivedGrid.queries_valid, ← ProductionGrid.grid_eq_alphabet]
      change _ = ((ComputableDerivedZeroOnGrid.queries (coordinates (exponent (graphOrder x)))
        (fun _ => BooleanCoefficientRecovery.cubicQuery (coordinates (exponent (graphOrder x))))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBaseDerived.sample .valid (graphOrder x) bits hv)).map
          ThreeColorVerifier.validGridQuery).map queryCode
      erw [List.map_map]
      rfl
    · change DerivedGrid.queries .proper _ _ _ _ _ = _
      erw [weight_eq, ← ProductionGrid.grid_eq_alphabet, DerivedGrid.queries_proper]
      change _ = ((ComputableDerivedZeroOnGrid.queries (coordinates (exponent (graphOrder x)))
        (fun z => BooleanCoefficientRecovery.weightedCubicQuery
          (coordinates (exponent (graphOrder x)))
          (FieldQueryArithmetic.edgeValue (grid (exponent (graphOrder x)))
            (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x)) z))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBaseDerived.sample .proper (graphOrder x) bits hv)).map
          ThreeColorVerifier.properGridQuery).map queryCode
      erw [List.map_map]
      rfl
    · rfl
  exact hraw.trans (List.map_congr_left fun q _ => physicalCode_eq _ q)

theorem verdicts_eq_history (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits))
    (qs : List ℕ) (bs : List Bool) (i : Fin 7) :
    verdicts (graphOrder x) x bits hv qs bs i =
      ComputableThreeColorVerifier.branchTest (coordinates (exponent (graphOrder x)))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
        (DerivedGrid.historyProof qs bs) i
        (unpad (ThreeColorBaseSeed.sample (graphOrder x) bits) hv i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change derivedVerdict .valid _ x bits hv qs bs = _
    dsimp only [derivedVerdict]
    erw [DerivedGrid.decision_valid, ← ProductionGrid.grid_eq_alphabet]
    rfl
  · change derivedVerdict .proper _ x bits hv qs bs = _
    dsimp only [derivedVerdict]
    erw [weight_eq, ← ProductionGrid.grid_eq_alphabet, DerivedGrid.decision_proper]
    rfl
  · change NumericDifference.verdict _ _ qs bs = _
    unfold NumericDifference.verdict
    simp only [DerivedGrid.boolEquiv_natCast]
    rfl

theorem allQueries_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits)) :
    allQueries (graphOrder x) x bits hv =
      (ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val := by
  change order.flatMap (querySegments (graphOrder x) x bits hv) =
    ((ComputableThreeColorFullFieldSampling.queries (coordinates (exponent (graphOrder x)))
      (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
      (grid (exponent (graphOrder x)))
      (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
      (ThreeColorBaseSeed.sample (graphOrder x) bits)).map
      (ThreeColorBinaryVerifier.addressEquiv (graphOrder x))).map Fin.val
  erw [ComputableThreeColorFullFieldSampling.queries, FieldQueryArithmetic.decodeSeed_eq,
    decode, dite_eq_left hv]
  simp only [order, ComputableThreeColorVerifier.queries, List.flatMap_def,
    List.map_flatten, List.map_ofFn]
  congr 2
  funext i
  simpa only [Function.comp_def, List.map_map, id_eq] using querySegments_eq x bits hv i

theorem allVerdict_eq (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (graphOrder x) bits)) (qs : List ℕ) (bs : List Bool) :
    allVerdict (graphOrder x) x bits hv qs bs =
      ComputableThreeColorQueryAlgorithm.verdict x bits
        (QueryTree.wordOfOracle _ (QueryTree.answersOracle qs bs)) := by
  have h : allVerdict (graphOrder x) x bits hv qs bs =
      ComputableThreeColorVerifier.test (coordinates (exponent (graphOrder x)))
        (nodes (exponent (graphOrder x))) (generator (exponent (graphOrder x)))
        (grid (exponent (graphOrder x)))
        (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
        (DerivedGrid.historyProof qs bs)
        (unpad (ThreeColorBaseSeed.sample (graphOrder x) bits) hv) := by
    apply Bool.eq_iff_iff.mpr
    simp only [allVerdict, order, List.all_eq_true, List.mem_ofFn, id_eq,
      ComputableThreeColorVerifier.test, decide_eq_true_eq]
    constructor
    · intro h i
      exact (verdicts_eq_history x bits hv qs bs i).symm.trans (h i ⟨i,rfl⟩)
    · intro h i _
      exact (verdicts_eq_history x bits hv qs bs i).trans (h i)
  change _ = ComputableThreeColorFullFieldSampling.test
    (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
    (generator (exponent (graphOrder x))) (grid (exponent (graphOrder x)))
    (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
    (ThreeColorBinaryVerifier.decodeProof (fieldWord
      (QueryTree.wordOfOracle _ (QueryTree.answersOracle qs bs))))
    (ThreeColorBaseSeed.sample (graphOrder x) bits)
  erw [ComputableThreeColorFullFieldSampling.test, FieldQueryArithmetic.decodeSeed_eq,
    decode, dite_eq_left hv]
  exact h.trans (congrArg (fun π => ComputableThreeColorVerifier.test
    (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
    (generator (exponent (graphOrder x))) (grid (exponent (graphOrder x)))
    (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x)) π
    (unpad (ThreeColorBaseSeed.sample (graphOrder x) bits) hv)) (historyProof_eq _ qs bs))

theorem queryList_of_invalid (x bits : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (graphOrder x) bits)) :
    ComputableThreeColorQueryAlgorithm.queryList x bits = [] := by
  change (ComputableThreeColorFullFieldSampling.queries
    (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
    (generator (exponent (graphOrder x))) (grid (exponent (graphOrder x)))
    (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
    (ThreeColorBaseSeed.sample (graphOrder x) bits)).map _ = []
  erw [ComputableThreeColorFullFieldSampling.queries, FieldQueryArithmetic.decodeSeed_eq,
    decode_of_not_valid _ hv]
  rfl

theorem verdict_of_invalid (x bits : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (graphOrder x) bits))
    (w : Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x)) → Bool) :
    ComputableThreeColorQueryAlgorithm.verdict x bits w = true := by
  change ComputableThreeColorFullFieldSampling.test
    (coordinates (exponent (graphOrder x))) (nodes (exponent (graphOrder x)))
    (generator (exponent (graphOrder x))) (grid (exponent (graphOrder x)))
    (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x) (vertexCode x))
    (ThreeColorBinaryVerifier.decodeProof (fieldWord w))
    (ThreeColorBaseSeed.sample (graphOrder x) bits) = true
  erw [ComputableThreeColorFullFieldSampling.test, FieldQueryArithmetic.decodeSeed_eq,
    decode_of_not_valid _ hv]

end PCP.Lang.ThreeColorBaseBranches
