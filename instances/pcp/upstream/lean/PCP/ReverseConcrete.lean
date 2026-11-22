import PCP.Theorem
import PCP.Complexity.StandardModel

/-!
# The reverse inclusion, for the concrete model

`pcp_subset_np` is proved for **every** `CostModel`, deliberately: that separates the semantic
argument from the machine-level obligation.  Now that the concrete model is known to be one —
`PCP.Machine.exists_standardCostModel`, obligation NP-1 — the reverse direction can be stated
without a model parameter at all.

This adds no simulation and no complexity argument.  It obtains the model, rewrites the two
predicate equalities the model carries, and applies the already-proved lemma.  Both locked
signatures, `np_subset_pcp` and `pcp_subset_np`, are untouched.

The conclusion is `InNP Machine.PolyTimeRel L`, membership in *this* project's concrete class.
Agreement of that class with the pinned ComplexityLib definition of NP is a separate theorem,
`PCP.ReferenceNP.inNP_iff_mem` in `PCP/Complexity/ReferenceNPConverse.lean`.
-/

namespace PCP

open Verifier

/-- **`PCP(O(log n), O(1)) ⊆ NP` for the concrete machine model.**

An efficiently implemented verifier — polynomial-time in the sense of `PCP/Complexity/Machine.lean`,
a step count on `Turing.FinTM2` — with a canonical logarithmic budget, a polynomial proof-length
bound, perfect completeness and soundness `1/2` puts its language in NP for that same concrete
class.  No cost model is a parameter, and no model-existence premise is assumed: the model comes
from `Machine.exists_standardCostModel`, whose closure field is the certified finite-witness
checker of `PCP/Complexity/CheckerFinal.lean`. -/
theorem pcp_subset_np_concrete (L : Language) (V : Verifier) (alg : VerifierAlg) (a b : ℕ)
    (p : Polynomial ℕ) (halg : Machine.PolyTimeAlg alg) (himpl : V.ImplementedBy alg)
    (hrand : V.CanonicalRandomness a b)
    (hlen : ∀ x : List Bool, V.ReadsBelow x (p.eval x.length))
    (hcomplete : ∀ x : List Bool, L x → V.CompleteAt x)
    (hsound : ∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) :
    InNP Machine.PolyTimeRel L := by
  obtain ⟨M, hrel, halgeq⟩ := Machine.exists_standardCostModel
  have heff : M.Efficient V := ⟨alg, by rw [halgeq]; exact halg, himpl⟩
  have h := pcp_subset_np M L V a b p heff hrand hlen hcomplete hsound
  rwa [hrel] at h

end PCP
