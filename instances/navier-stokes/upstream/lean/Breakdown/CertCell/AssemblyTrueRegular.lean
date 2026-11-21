import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyTrueRegularParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open Internal.TrueRegular in
theorem trueFieldRegular_of_fieldRegular {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (hF : FieldRegular D) : TrueFieldRegular D := by
  obtain ⟨B, hW⟩ := hF.model_state
  obtain ⟨e₁, e₂, e₃, hadm⟩ := hF.admissible
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K q v G H g κ F Pg ht
    exact profile_regular hF.azimuth_pos ht.perturbation (hF.mesh_valid.box_valid K)
  · intro q hq v G H g hv K
    exact density_measurable_on D (hadm q hq) (hF.bounds_measurable q hq) hW hv
      (rect_ae_le_halfPlane (hF.mesh_valid.box_valid K))
  · intro q hq v G H g hv K
    exact aesm_stretch_integrand hW hv.measurable_velocity hv.measurable_gradient
      (rect_ae_le_halfPlane (hF.mesh_valid.box_valid K))
  · intro K α
    exact given_modes_measurable hW D.azimuthOrder (rect_ae_le_halfPlane (hF.mesh_valid.box_valid K)) α
  · intro q hq v G H g hv
    exact density_measurable_on D (hadm q hq) (hF.bounds_measurable q hq) hW hv (inter_halfPlane_ae_le _)

theorem trueFieldRegularHolds : TrueFieldRegularHolds :=
  fun D hF => trueFieldRegular_of_fieldRegular D hF

end Assembly

end CertCell

end Breakdown
