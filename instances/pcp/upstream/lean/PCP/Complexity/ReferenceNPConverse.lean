import PCP.Complexity.ReferenceBoundedVerifier
import PCP.Complexity.ReferencePairDecider
import PCP.Complexity.ReferenceNPBridge

/-!
# Equivalence with the pinned reference NP class

The reverse bridge translates the concrete relation checker into an actual
reference decider, computes the certificate polynomial on work tape, and uses
the reference bounded-guess compiler. The latter enforces the witness bound,
so the supplied checker need not reject longer strings. All machine simulation,
pair parsing, output normalization and polynomial running-time obligations
are discharged by the imported constructions.
-/

namespace PCP.ReferenceNP

/-- Every language with a concrete polynomial-time witness checker belongs to
the exact pinned ComplexityLib nondeterministic-machine class. -/
theorem of_inNP {L : Complexity.Language} (hL : PCP.InNP Machine.PolyTimeRel L) :
    L ∈ Complexity.NP := by
  obtain ⟨cert⟩ := hL
  obtain ⟨k, M, runtime, hM⟩ :=
    Machine.ReferencePair.exists_decider cert.check cert.check_polyTime
  apply ReferenceBoundedVerifier.mem_NP_of_bounded_verifier
    cert.witnessBound runtime M hM
  intro x
  change L x ↔ _
  simpa only [Machine.ReferencePair.pair_mem_checkerLanguage, Set.mem_ofPred_eq]
    using cert.spec x

/-- The concrete `FinTM2` certificate class is exactly ComplexityLib's NP.
Neither direction requires a supplied machine simulation or cost premise. -/
theorem mem_iff_inNP {L : Complexity.Language} :
    L ∈ Complexity.NP ↔ PCP.InNP Machine.PolyTimeRel L :=
  ⟨to_inNP, of_inNP⟩

/-- The same equality oriented from the concrete certificate definition. -/
theorem inNP_iff_mem {L : Complexity.Language} :
    PCP.InNP Machine.PolyTimeRel L ↔ L ∈ Complexity.NP :=
  mem_iff_inNP.symm

end PCP.ReferenceNP
