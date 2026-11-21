import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Advection

theorem sum_coord_inner (L : Space →L[ℝ] Space) (v a : Space) :
    ∑ j : Fin 3, v j * inner ℝ (L (unitVector j)) a = inner ℝ (L v) a := by
  have hv : v = ∑ j : Fin 3, v j • unitVector j := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    simpa [unitVector] using this.symm
  conv_rhs => rw [hv]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, real_inner_smul_left]

end Internal.Advection

theorem advectionTrilinear (h1 : VelocityDecay) (h2 : PartialDecay) :
    AdvectionTrilinear := by
  intro f w hf _
  unfold advectionPairing trilinear
  refine integral_congr_ae ?_
  filter_upwards [h1 f hf, ae_all_iff.2 (fun j => h2 f hf j)] with x hv hp
  simp only [hv, hp, partialField, advectionAt]
  exact (Internal.Advection.sum_coord_inner (fderiv ℝ f x) (f x) (w x)).symm

end Breakdown.Freq
