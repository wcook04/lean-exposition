import PCP.Complexity.CheckerFinal
import PCP.Complexity.Bridge

/-!
# The standard cost model — obligation NP-1, discharged

`exists_standardCostModel` was stated in `PCP/Complexity/Machine.lean`, next to the two predicates
it is about.  It is proved **here**, under the same full name and with the same type, because its
proof needs the finite-witness checker built in `CheckerFinal.lean` and the computability bridge of
`Bridge.lean`, both of which import `Machine.lean` — stating and proving it in the same file would
be an import cycle.  This is the same move NP-1b and NP-1c made to `Bridge.lean`.

## The closure field

`polyTimeRel_finiteWitnessCheck_concrete` is the one field that was open.  Given a polynomial-time
witness for the verifier algorithm, the checker machine of `CheckerFinal.lean` decides

```text
fun x w => checkAll alg V.queries (canonicalWidth a b x.length) x w
```

in polynomial time in the length of `encodePair (x, w)`.  Canonical randomness makes that width
*equal* to `V.randomness x.length`, and `checkAll_eq_finiteWitnessCheck` makes the relation *equal*
to `finiteWitnessCheck V` — for **every** witness string, short ones included, whose missing bits
read `false`.

The `ReadsBelow` hypothesis of the field is not used by this machine theorem: the checker's cost is
bounded in the actual encoded witness length, and numeric addresses were eliminated through the
algorithm's own output bound.  That hypothesis still matters to the separate argument bounding
witness lengths in the NP definition.

## What this does not discharge

This module supplies the concrete cost model, not the forward PCP construction; that is
`np_subset_pcp` in `PCP/Theorem.lean`.  The comparison of the concrete class with the pinned
ComplexityLib definition of NP is proved separately, in `PCP/Complexity/ReferenceNPConverse.lean`.
-/

namespace PCP.Machine

open Turing

/-- **The closure field, for the concrete predicates.**  An efficiently implemented verifier with a
canonical logarithmic budget induces a polynomial-time finite-witness checking relation. -/
theorem polyTimeRel_finiteWitnessCheck_concrete (V : Verifier) (alg : VerifierAlg) (a b : ℕ)
    (p : Polynomial ℕ) (halg : PolyTimeAlg alg) (himp : V.ImplementedBy alg)
    (hcan : V.CanonicalRandomness a b)
    (_hreads : ∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) :
    PolyTimeRel (finiteWitnessCheck V) := by
  obtain ⟨hw⟩ := halg
  have heq : finiteWitnessCheck V
      = fun x w => checkAll alg V.queries (canonicalWidth a b x.length) x w := by
    funext x w
    rw [← checkAll_eq_finiteWitnessCheck himp x w, hcan x.length]
    rfl
  rw [heq]
  exact ⟨checkerWitness hw a b V.queries⟩

/-- **Obligation NP-1, discharged.**  The concrete model satisfies the `CostModel` interface: its
two predicates are exactly `PolyTimeRel` and `PolyTimeAlg` of `Machine.lean`, the two coherence
fields are the bridge of `Bridge.lean`, and the closure field is the checker machine above. -/
theorem exists_standardCostModel :
    ∃ M : CostModel, M.PolyTimeRel = PolyTimeRel ∧ M.PolyTimeAlg = PolyTimeAlg :=
  ⟨{ PolyTimeRel := PolyTimeRel
     PolyTimeAlg := PolyTimeAlg
     polyTimeRel_computable := polyTimeRel_computable
     polyTimeAlg_computable := polyTimeAlg_computable
     polyTimeRel_finiteWitnessCheck := fun V alg a b p halg himp hcan hreads =>
       polyTimeRel_finiteWitnessCheck_concrete V alg a b p halg himp hcan hreads },
   rfl, rfl⟩

end PCP.Machine
