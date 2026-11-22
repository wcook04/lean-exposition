import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.LocalExtr

/-!
# The local-minimum statement, with no proof

Comparator reads this file as the challenge. It imports two Mathlib files and nothing from
Physlib, so every word of the statement is defined in Mathlib.

The statement is copied from the author's source, under the author's own name:
`PhyslibAlpha/ClassicalMechanics/CoupledSpringPotential.lean`, lines 153 to 157.
-/

theorem coupled_spring_potential :
    let U := fun x : EuclideanSpace ℝ (Fin 2) => (x 0)^2 + x 0 * x 1 + (x 1)^2
    IsLocalMin U {
        ofLp := ![0,0]
    } := by
  sorry
