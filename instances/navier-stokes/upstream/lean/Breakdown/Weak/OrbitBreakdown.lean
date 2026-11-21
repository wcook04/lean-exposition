import Breakdown.Uniqueness.Space
import Breakdown.Weak.Basic

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

theorem breakdownOnSpace_of_orbit
    (h : ∃ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space),
      realization.F.IsOrbit (realization.rot R) w P) :
    BreakdownOnSpace := by
  obtain ⟨w, P, R, hw⟩ := h
  obtain ⟨u, hu0, -, hmild, C, κ, hκ, hbound⟩ :=
    transferHolds_of_dichotomy dichotomyHolds X realization.F (realization.rot R)
      (realization.rot_commutes R) w P hw realization.test realization.test_dense 1 one_pos
  obtain ⟨φ, hφ, hembed⟩ := realization.test_spec (u 0) hu0
  apply breakdownOnSpace_of_unit_viscosity
  refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2, ?_⟩
  rintro ⟨v, q, hv, hE⟩
  have hcont : ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 1 ×ˢ univ) :=
    hv.smooth_velocity.continuousOn.mono (Set.prod_mono Icc_subset_Ici_self Subset.rfl)
  exact false_of_orbit_rate fieldReading_realization hw hκ hbound hcont
    (agree_of_mildRegular mildRegular_realization hφ hmild hembed.symm hv hE)

end Breakdown.WeakProfile
