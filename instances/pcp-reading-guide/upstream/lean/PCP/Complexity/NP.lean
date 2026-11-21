import PCP.Complexity.CostModel

/-!
# Binary languages and polynomial witness certificates

`NPCertificate` records a polynomial witness bound and a checking relation.
The forward PCP theorem instantiates it with `Machine.PolyTimeRel`; the reverse
inclusion uses a `CostModel`. `ReferenceNPConverse` proves equivalence with the
pinned ComplexityLib definition of NP.
-/

namespace PCP

/-- A language over the binary alphabet: inputs are bit strings. -/
def Language : Type := List Bool → Prop

/-- A certificate that `L` is in NP relative to a notion `P` of polynomial-time checkability: a
polynomial witness bound and a witness-checking relation that `P` accepts.

`P` is a plain parameter here, and that is safe *because nothing is proved by quantifying over it*.
`InNP` is a definition, not a theorem. The two consumers each pin it down:

* `pcp_subset_np` instantiates `P := M.PolyTimeRel` for a `CostModel` `M`, whose closure field is
  what makes the conclusion non-vacuous;
* `np_subset_pcp` instantiates `P := PCP.Machine.PolyTimeRel`, the concrete machine definition.

Neither quantifies over an arbitrary `P`. The distinction matters:
a *theorem* over an unconstrained interface is refutable by choosing a degenerate instance; a
*definition* parameterised by one is just a definition. -/
structure NPCertificate (P : (List Bool → List Bool → Bool) → Prop) (L : Language) where
  /-- Polynomial bound on witness length. -/
  witnessBound : Polynomial ℕ
  /-- The witness-checking relation. -/
  check : List Bool → List Bool → Bool
  /-- The relation is polynomial-time checkable. -/
  check_polyTime : P check
  /-- The relation defines `L`. -/
  spec : ∀ x : List Bool, L x ↔
    ∃ w : List Bool, w.length ≤ witnessBound.eval x.length ∧ check x w = true

/-- `L` is in NP relative to the polynomial-time-checkability notion `P`. -/
def InNP (P : (List Bool → List Bool → Bool) → Prop) (L : Language) : Prop :=
  Nonempty (NPCertificate P L)



end PCP
