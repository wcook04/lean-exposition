import PCP.Complexity.Simulate

/-!
# The two coherence theorems

Obligations **NP-1b** and **NP-1c**: the two coherence fields of `CostModel` for the concrete
machine predicates.

These two declarations were stated in `PCP/Complexity/Machine.lean`, next to the predicates they
are about.  They are proved *here* instead, under the same full names and with the same types,
because their proofs need the effective codecs of `PCP/Complexity/Codec.lean`, which imports
`Machine.lean` — stating and proving them in the same file would be an import cycle.

Both follow from one generic bridge, `PCP.Machine.computable_of_polyTime`, applied to the concrete
encodings: an effective input encoder, an effective left inverse of the output encoder, and the
machine certificate.  Neither is restricted to the example machines; both quantify over an arbitrary
witness of the concrete predicate.

What this does **not** do: it contributes nothing to the quantitative closure field.  That field,
and with it `exists_standardCostModel` (NP-1), is discharged in `PCP/Complexity/StandardModel.lean`
by the finite-witness checker machine.  The comparison with the reference definition of NP is in
`PCP/Complexity/ReferenceNPConverse.lean`.
-/

namespace PCP.Machine

open Turing

/-- **Obligation NP-1b.**  A polynomial-time checking relation is computable. -/
theorem polyTimeRel_computable (R : List Bool → List Bool → Bool) (h : PolyTimeRel R) :
    Computable₂ R := by
  obtain ⟨w⟩ := h
  exact computable_of_polyTime w computable_encodePair computable_decodeBool decodeBool_encodeBool

/-- **Obligation NP-1c.**  A polynomial-time verifier algorithm is computable. -/
theorem polyTimeAlg_computable (alg : VerifierAlg) (h : PolyTimeAlg alg) :
    Computable (fun t : List Bool × List Bool × List Bool => alg t.1 t.2.1 t.2.2) := by
  obtain ⟨w⟩ := h
  exact computable_of_polyTime w computable_encodeTriple computable_decodeAnswer
    decodeAnswer_encodeAnswer

end PCP.Machine
