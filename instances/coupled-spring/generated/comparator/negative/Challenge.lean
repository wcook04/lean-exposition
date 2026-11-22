import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.LocalExtr

/-!
# The control: a changed statement Comparator must refuse

The same file as the challenge with `IsLocalMax` in place of `IsLocalMin`.
-/

theorem coupled_spring_potential :
    let U := fun x : EuclideanSpace ℝ (Fin 2) => (x 0)^2 + x 0 * x 1 + (x 1)^2
    IsLocalMax U {
        ofLp := ![0,0]
    } := by
  sorry
