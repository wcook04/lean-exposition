import Breakdown.CertCell.ShapeStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

def GivenJetDataValid : Prop :=
  ∀ J : GivenJetData, IsGivenJetData J → IsGivenKeyData J.keys fun κ => (J.data κ).toAmp

structure JetParts : Prop where
  shapeInfo : ShapeParts
  jet_valid : GivenJetDataValid

structure IsGivenJetEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k) (J : GivenJetData) : Prop where
  jets : IsGivenJetData J
  model_eq : F.model = J.model
  params_valid : IsShapeParams F.params
  actuatorParams_valid : ∀ i, IsShapeParams (F.actuatorParams i)
  actuators_valid : ∀ i, IsCompactTimeFieldData (F.actuatorEdge i) (F.actuators i)
  azimuth_eq : F.params.azimuthOrder = D.azimuthOrder
  actuatorAzimuth_eq : ∀ i, (F.actuatorParams i).azimuthOrder = D.azimuthOrder
  given_eq : D.given = shapeInfoField F.params F.model
  givenHess_eq : D.givenHess = shapeHess F.params F.model
  labels_cover : harmonicsOf D.azimuthOrder F.model ⊆ D.givenLabels
  labels_symm : ∀ β ∈ D.givenLabels, -β ∈ D.givenLabels
  actuator_eq : ∀ i, D.cert.actuator i = shapeInfoField (F.actuatorParams i) (F.actuators i)
  actuatorModes_eq : ∀ i, X.actuatorModes i = labelsOf (F.actuators i)

theorem givenShapeEntry_of_jets (h : JetParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (J : GivenJetData) (hJ : IsGivenJetEntry D X F J) : IsGivenShapeEntry D X F where
  params_valid := hJ.params_valid
  model_valid := hJ.model_eq ▸ h.shapeInfo.closure_valid _ _ (h.jet_valid J hJ.jets)
  actuatorParams_valid := hJ.actuatorParams_valid
  actuators_valid := hJ.actuators_valid
  azimuth_eq := hJ.azimuth_eq
  actuatorAzimuth_eq := hJ.actuatorAzimuth_eq
  given_eq := hJ.given_eq
  givenHess_eq := hJ.givenHess_eq
  labels_cover := hJ.labels_cover
  labels_symm := hJ.labels_symm
  actuator_eq := hJ.actuator_eq
  actuatorModes_eq := hJ.actuatorModes_eq

theorem layerShapeFacts_of_jets (h : JetParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (J : GivenJetData) (hJ : IsGivenJetEntry D X F J) : LayerShapeFacts D X :=
  layerShapeFacts_of_entry h.shapeInfo D X F (givenShapeEntry_of_jets h D X F J hJ)

end GivenShape

end CertCell

end Breakdown
