import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

theorem paramsBounded_holds : ParamsBoundedHolds := by
  intro k d hscale
  refine ⟨∑ j, (|d.radius j| + |d.stiffRadius| / |d.scale j|), ?_⟩
  intro q hq i
  obtain ⟨hadj, hstiff⟩ := hq
  have hterm : ∀ j, 0 ≤ |d.radius j| + |d.stiffRadius| / |d.scale j| := fun j =>
    add_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsingle : |d.radius i| + |d.stiffRadius| / |d.scale i| ≤
      ∑ j, (|d.radius j| + |d.stiffRadius| / |d.scale j|) :=
    Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
  refine le_trans ?_ hsingle
  by_cases hi : i ∈ d.adjointSet
  · have h1 : |q i| ≤ |d.radius i| := le_trans (hadj i hi) (le_abs_self _)
    have h2 : 0 ≤ |d.stiffRadius| / |d.scale i| := div_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  · have hic : i ∈ d.adjointSetᶜ := Finset.mem_compl.mpr hi
    have hsq : (d.scale i * q i) ^ 2 ≤ d.stiffRadius ^ 2 := by
      refine le_trans ?_ hstiff
      exact Finset.single_le_sum (f := fun j => (d.scale j * q j) ^ 2)
        (fun j _ => sq_nonneg _) hic
    have habs : |d.scale i| * |q i| ≤ |d.stiffRadius| := by
      rw [← abs_mul]
      exact sq_le_sq.mp hsq
    have hpos : 0 < |d.scale i| := abs_pos.mpr (hscale i)
    have h3 : |q i| ≤ |d.stiffRadius| / |d.scale i| := by
      rw [le_div_iff₀ hpos]
      linarith
    have h4 : 0 ≤ |d.radius i| := abs_nonneg _
    linarith

end Instantiation

end CellReduction

end Breakdown
