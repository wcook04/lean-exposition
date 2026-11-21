import Breakdown.FracCert.StHeld
import Mathlib

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

theorem testBoxSubset : TestBoxSubsetStatement := by
  intro α k N d hd p hp j
  unfold FracCertData.testBox Held.testSet at hp
  obtain ⟨hact, hsum⟩ := hp
  by_cases hj : j ∈ d.activeSet
  · exact hact j hj
  · have hjc : j ∈ d.activeSetᶜ := Finset.mem_compl.mpr hj
    have hsingle : (d.slope j * p j) ^ 2 ≤ ∑ i ∈ d.activeSetᶜ, (d.slope i * p i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (d.slope i * p i) ^ 2) (fun i _ => sq_nonneg _) hjc
    have hε := hd.ellipsoid_le j hj
    have hε0 := hd.ellipsoidRadius_nonneg
    have hpos : 0 < |d.slope j| := abs_pos.mpr (hd.slope_ne_zero j)
    have hb0 : 0 ≤ |d.slope j| * d.radius j := le_trans hε0 hε
    have hsq : (d.slope j * p j) ^ 2 ≤ (|d.slope j| * d.radius j) ^ 2 :=
      le_trans hsingle (le_trans hsum (pow_le_pow_left₀ hε0 hε 2))
    have habs : |d.slope j * p j| ≤ |d.slope j| * d.radius j := by
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hb0] at this
    rw [abs_mul] at habs
    exact le_of_mul_le_mul_left habs hpos

end SteadyCert

end Breakdown
