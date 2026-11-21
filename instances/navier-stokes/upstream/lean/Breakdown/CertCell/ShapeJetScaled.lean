import Breakdown.CertCell.ShapeJetEntry
import Breakdown.CertCell.ShapeKnots
import Breakdown.CertCell.ShapeKnotsNull
import Breakdown.CertCell.StatementDefs

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)

def cellVariable (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C (2 / (b - a)) * Polynomial.X - Polynomial.C ((a + b) / (b - a))

def jacobiBubble (n j : ℕ) (c a b : ℝ) : Polynomial ℂ :=
  (Polynomial.C c * (1 - cellVariable a b ^ 2) ^ n * (symmetricJacobi (2 * n) j).comp (cellVariable a b)).map
    (algebraMap ℝ ℂ)

namespace ScaledJetAxis

def dofPoly (A : ScaledJetAxis) (i : ℕ) : JetDof → Polynomial ℂ
  | .node k p => Polynomial.C ((((A.scale.getD k 1)⁻¹ ^ p : ℝ) : ℂ)) * A.base.dofPoly i (.node k p)
  | .bubble i' j =>
    if i' = i ∧ j < A.bubbleCount then
      jacobiBubble A.depth j (A.bubbleConst.getD j 0) (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0)
    else 0

end ScaledJetAxis

namespace ScaledJetSpline

def toSpline (H : ScaledJetSpline) : Spline :=
  ⟨⟨H.tAxis.breaks, H.xAxis.breaks⟩, fun i j => ∑ d ∈ H.tAxis.base.dofs, ∑ e ∈ H.xAxis.base.dofs,
    MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly i d) * embedSecond (H.xAxis.dofPoly j e)⟩

end ScaledJetSpline

namespace ScaledKeyData

end ScaledKeyData

namespace ScaledJetData

end ScaledJetData

def ScaledSplineAgreementHolds : Prop :=
  ∀ H : ScaledJetSpline, IsJetAxis H.tAxis.base 0 1 → IsJetAxis H.xAxis.base (-1) 1 →
    SplineAgrees H.toJet.toSpline H.toSpline

def ScaledJetDataHolds : Prop :=
  ∀ S : ScaledJetData, IsScaledJetData S → IsGivenJetData S.toJets

structure ScaledJetParts : Prop where
  jets : JetParts
  agrees : ScaledSplineAgreementHolds
  data_valid : ScaledJetDataHolds

theorem givenJetEntry_of_scaled (h : ScaledJetParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (S : ScaledJetData) (hS : IsScaledJetEntry D X F S) :
    IsGivenJetEntry { D with givenHess := shapeHess F.params F.model } X F S.toJets where
  jets := h.data_valid S hS.jets
  model_eq := hS.model_eq
  params_valid := hS.params_valid
  actuatorParams_valid := hS.actuatorParams_valid
  actuators_valid := hS.actuators_valid
  azimuth_eq := hS.azimuth_eq
  actuatorAzimuth_eq := hS.actuatorAzimuth_eq
  given_eq := hS.given_eq
  givenHess_eq := rfl
  labels_cover := hS.labels_cover
  labels_symm := hS.labels_symm
  actuator_eq := hS.actuator_eq
  actuatorModes_eq := hS.actuatorModes_eq


theorem layerShapeFacts_of_scaled (hJ : JetParts) (h : ScaledJetParts)
    {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (F : GivenShapeEntry k) (S : ScaledJetData) (hS : IsScaledJetEntry D X F S) : LayerShapeFacts D X := by
  have hF := layerShapeFacts_of_jets hJ { D with givenHess := shapeHess F.params F.model } X F S.toJets
    (givenJetEntry_of_scaled h D X F S hS)
  have hnull := KnotNull.shapeKnotsNullSpace F.params F.model hS.params_valid
  have hH : D.givenHess = KnotZero.zeroOn (mirrorKnots F.params F.model) (shapeHess F.params F.model) :=
    hS.givenHess_eq
  refine ⟨hF.actuator_shape, ?_, ?_, ?_, hF.harmonics_span⟩
  · rw [hH]
    exact KnotZero.flipModel_zeroOn (mirrorKnots_closed F.params F.model) hF.flip_model
  · obtain ⟨B, hB⟩ := hF.model_state
    rw [hH]
    exact ⟨B, KnotZero.weakHessianState_zeroOn hnull hB⟩
  · rw [hH]
    exact KnotZero.harmonicExpansion_zeroOn _ hF.model_harmonics

end GivenShape

end CertCell

end Breakdown
