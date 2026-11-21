import Breakdown.FracCell.Defs
import Breakdown.FracCell.AssemblyDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

namespace ExteriorData

variable {k N : ℕ} (c : FracCellData k N) (e : ExteriorData)

end ExteriorData

structure IsExteriorData (α : ℝ) {k N : ℕ} (c : FracCellData k N) (e : ExteriorData) : Prop where
  radius_measurable : Measurable e.radius
  radiusMin_pos : 0 < e.radiusMin
  radius_between : ∀ y, e.radiusMin ≤ e.radius y ∧ e.radius y ≤ e.radiusMax
  radius_homogeneous : ∀ (t : ℝ) (y : Space), 0 < t → e.radius (t • y) = e.radius y
  exterior_eq : c.cellRegionᶜ =ᵐ[volume] {y : Space | e.radius y < ‖y‖}
  innerWeight_ge : c.coercivity ≤ c.innerWeight
  innerWeight_le : c.innerWeight ≤ c.splitVisc
  curlGrad_traceFree : ∀ y ∉ c.cellRegion, ∑ i : Fin 3, entry (c.centreCurlGrad y) i i = 0
  strainBound_measurable : Measurable e.strainBound
  strain_le : ∀ y ∉ c.cellRegion, ∀ u : Space, inner ℝ (c.centreStrain y u) u ≤ e.strainBound y * ‖u‖ ^ 2
  curlGrad_le : ∀ y ∉ c.cellRegion, ‖c.centreCurlGrad y‖ ≤ e.meanCurlGradBound y + e.waveCurlGradBound y
  meanCurlGradBound_nonneg : ∀ y, 0 ≤ e.meanCurlGradBound y
  waveCurlGradBound_nonneg : ∀ y, 0 ≤ e.waveCurlGradBound y
  splitLength_pos : ∀ y ∉ c.cellRegion, 0 < e.splitLength y
  splitLength_measurable : Measurable e.splitLength
  coef_lower : ∀ y ∉ c.cellRegion, e.coefLower ≤ ExteriorData.gradientCoef c e α y
  wave_bound : ∀ y ∉ c.cellRegion,
    ‖y‖ ^ 2 * ((traceFreeConst / 2) * e.waveCurlGradBound y / e.splitLength y) ≤ e.weightedWave
  mean_bound : ∀ y ∉ c.cellRegion, ‖y‖ * (traceFreeConst * e.meanCurlGradBound y) ≤ e.weightedMean
  exterior_test : 4 * e.weightedWave + 2 * e.weightedMean ≤ e.coefLower

end Exterior

end CellCert

end Breakdown
