import PCP.Complexity.GridEdgeLang
import PCP.Complexity.ProductionGridLang
import PCP.Algebraic.ThreeColorCanonicalVerifier

/-!
# Public edge arithmetic at the production verifier's field and grid
-/

namespace PCP.Lang.ProductionGrid

open PCP.Algebraic BinaryFieldCode ThreeColorParameters

/-- The standalone edge program uses the actual production field and prefix grid. -/
theorem edge_run (a n : ℕ) (x : List Bool) (z : Fin (n + n) → Field a)
    (st : State 70 20) (hi : GridEdge.Input (binaryDimension a) (size a) n x z st) :
    (GridEdge.program.run st).1.regs 50 =
      (fieldCode a (FieldQueryArithmetic.edgeValue (grid a)
        (ThreeColorGridIndex.pad (gridCode a) n (ThreeColorEncoding.graph x)) z)).val := by
  have hp := @GridEdge.program_run (binaryDimension a) (size a) n _ (size_le_fieldCode a)
  rw [fieldEquiv_eq_fieldCode] at hp
  exact hp x z st hi

/-- The canonical vertex codec leaves the explicit numeric placement unchanged. -/
theorem canonical_gridGraph (x : List Bool) :
    ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x)
        (ThreeColorCanonicalVerifier.vertexCode x) =
      ThreeColorGridIndex.pad
        (gridCode (ThreeColorParameterChoice.exponent
          (ThreeColorCanonicalVerifier.graphOrder x)))
        (size (ThreeColorParameterChoice.exponent (ThreeColorCanonicalVerifier.graphOrder x)))
        (ThreeColorEncoding.graph x) := by
  ext u v
  change (ThreeColorGridIndex.pad _ _ _).Adj u v ↔ (ThreeColorGridIndex.pad _ _ _).Adj u v
  rw [GridEdgeArithmetic.pad_adj, GridEdgeArithmetic.pad_adj]
  simp only [GridEdgeArithmetic.Adj, Fintype.card_fin, SimpleGraph.comap_adj]
  split_ifs <;> rfl

instance canonicalGridDecidableAdj (x : List Bool) : DecidableRel
    (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x)
      (ThreeColorCanonicalVerifier.vertexCode x)).Adj := by
  unfold ThreeColorBinaryVerifier.gridGraph
  infer_instance

/-- The exact public edge value requested by the canonical binary verifier is executable. -/
theorem canonical_edge_run (x : List Bool)
    (z : Fin (size (ThreeColorParameterChoice.exponent
      (ThreeColorCanonicalVerifier.graphOrder x)) + size (ThreeColorParameterChoice.exponent
      (ThreeColorCanonicalVerifier.graphOrder x))) →
      Field (ThreeColorParameterChoice.exponent (ThreeColorCanonicalVerifier.graphOrder x)))
    (st : State 70 20)
    (hi : GridEdge.Input
      (binaryDimension (ThreeColorParameterChoice.exponent
        (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (ThreeColorParameterChoice.exponent (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (ThreeColorParameterChoice.exponent
        (ThreeColorCanonicalVerifier.graphOrder x))) x z st) :
    (GridEdge.program.run st).1.regs 50 =
      (fieldCode (ThreeColorParameterChoice.exponent (ThreeColorCanonicalVerifier.graphOrder x))
        (FieldQueryArithmetic.edgeValue
          (grid (ThreeColorParameterChoice.exponent (ThreeColorCanonicalVerifier.graphOrder x)))
          (ThreeColorBinaryVerifier.gridGraph (ThreeColorEncoding.graph x)
            (ThreeColorCanonicalVerifier.vertexCode x)) z)).val := by
  have he := edge_run _ _ x z st hi
  simp only [FieldQueryArithmetic.edgeValue_eq] at he ⊢
  rw [canonical_gridGraph]
  exact he

end PCP.Lang.ProductionGrid
