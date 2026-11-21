import PCP.Complexity.NP
import PCP.Complexity.Machine
import Complexitylib.Classes.NP

/-!
# The three headline statements, with no proofs

Comparator reads this file as the challenge. It imports only the files that define the
words the statements use: the verifier, the machine model, this project's NP, and the
vendored ComplexityLib NP. It does not import any proof.

Each statement is copied from the authors' source, under the authors' own name:
`PCP/Theorem.lean` (lines 25 to 33), `PCP/ReverseConcrete.lean` and
`PCP/Complexity/ReferenceNPConverse.lean`.
-/

namespace PCP

theorem np_subset_pcp (L : Language) (hL : InNP Machine.PolyTimeRel L) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) := by
  sorry

theorem pcp_subset_np_concrete (L : Language) (V : Verifier) (alg : VerifierAlg) (a b : ℕ)
    (p : Polynomial ℕ) (halg : Machine.PolyTimeAlg alg) (himpl : V.ImplementedBy alg)
    (hrand : V.CanonicalRandomness a b)
    (hlen : ∀ x : List Bool, V.ReadsBelow x (p.eval x.length))
    (hcomplete : ∀ x : List Bool, L x → V.CompleteAt x)
    (hsound : ∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) :
    InNP Machine.PolyTimeRel L := by
  sorry

end PCP

namespace PCP.ReferenceNP

theorem inNP_iff_mem {L : Complexity.Language} :
    PCP.InNP Machine.PolyTimeRel L ↔ L ∈ Complexity.NP := by
  sorry

end PCP.ReferenceNP
