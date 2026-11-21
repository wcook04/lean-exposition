import TorusEuler.Paper.Proofs.S5a.Library.Mono53

/-!
# S53 library: the data-level form of the jets of Proposition 5.1

The copies of the library chain in `Paper.Lib.S53` take the jets of the seven coefficient fields of the
parent through a hypothesis `LeafBounds B U X T D k Λ` (`Lib.S5a.LeafBounds`, the conclusion of the
library form of Proposition 5.1 at the data level) instead of calling the library lemma
`exists_parent_coefficientJetBounds`. In `Proof.lemma_5_3_of` the hypothesis is supplied by `h5_1` at the
scale `D^{C0}` (`Lib.S5a.leafBounds_of_h51`).
-/
