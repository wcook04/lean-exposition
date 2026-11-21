import PCP.Complexity.DerivedGridSemantics
import PCP.Complexity.ProductionEdgeLang
import PCP.Algebraic.ComputableThreeColorQueryAlgorithm

/-! # Numeric physical addresses and the production finite proof word -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  ThreeColorCanonicalVerifier LocalCorrection

theorem coefficientCode_eq {F : Type*} {q n m c t : ℕ} (eF : F ≃ Fin q)
    (z : ThreeColorVerifier.Query F n m c t) :
    (ThreeColorQueryIndex.equiv eF (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) z).val =
    (ThreeColorQueryIndex.equiv eF (BooleanCoefficientIndex.affineEquiv t)
      (BooleanCoefficientIndex.cubicEquiv t) z).val := by
  rw [← QueryAddress.term_eq, ← QueryAddress.term_eq]
  congr 1
  cases z <;> funext i <;> fin_cases i <;>
    simp [QueryAddress.inputs, BooleanCoefficientIndex.affineEquiv,
      BooleanCoefficientIndex.cubicEquiv]

theorem physicalCode_eq (N : ℕ) (q : ThreeColorBinaryVerifier.Address N) :
    queryCode q = (ThreeColorBinaryVerifier.addressEquiv N q).val := by
  have hf : BinaryFieldCode.fieldEquiv (binaryDimension (exponent N)) =
      ThreeColorBinaryVerifier.fieldIndex N :=
    ProductionGrid.fieldEquiv_eq_fieldCode (exponent N)
  change (ThreeColorQueryIndex.equiv (BinaryFieldCode.fieldEquiv (binaryDimension (exponent N)))
    (BooleanCoefficientIndex.coefficientEquiv (binaryDimension (exponent N)) 1)
    (BooleanCoefficientIndex.coefficientEquiv (binaryDimension (exponent N)) 3) q).val = _
  have h := coefficientCode_eq (BinaryFieldCode.fieldEquiv (binaryDimension (exponent N))) q
  exact h.trans (congrArg (fun e => (ThreeColorQueryIndex.equiv e
    (BooleanCoefficientIndex.affineEquiv (binaryDimension (exponent N)))
    (BooleanCoefficientIndex.cubicEquiv (binaryDimension (exponent N))) q).val) hf)

theorem historyProof_eq (N : ℕ) (qs : List ℕ) (bs : List Bool) :
    DerivedGrid.historyProof (t := binaryDimension (exponent N))
      (n := size (exponent N)) (m := size (exponent N)) qs bs =
      ThreeColorBinaryVerifier.decodeProof (fieldWord
        (QueryTree.wordOfOracle (ThreeColorBinaryVerifier.proofLength N)
          (QueryTree.answersOracle qs bs))) := by
  unfold DerivedGrid.historyProof ThreeColorBinaryVerifier.decodeProof
  congr 1
  funext q
  erw [physicalCode_eq]
  exact (DerivedGrid.boolEquiv_natCast _).symm


end PCP.Lang.ThreeColorBaseBranches
