import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.ActuatorPairing
import Breakdown.CertCell.ActuatorPairingDensity
import Breakdown.CertCell.ActuatorPairingGradient
import Breakdown.CertCell.FormNegativeFinite
import Breakdown.CertCell.Certificate
import Breakdown.CertCell.CertSlackBound
import Breakdown.CertCell.CertRealRestriction
import Breakdown.CertCell.CertCoordinateSlack
import Breakdown.CertCell.RowSharesInstance
import Breakdown.CertCell.InstancePairingFormula
import Breakdown.CertCell.InstancePairingPosDef
import Breakdown.CertCell.InstanceOrthonormal
import Breakdown.CertCell.InstanceNormIdentity
import Breakdown.CertCell.InstanceClassForm
import Breakdown.CertCell.InstanceMoments
import Breakdown.CertCell.InstanceMomentUpper
import Breakdown.CertCell.InstanceMomentLower
import Breakdown.CertCell.InstanceSmooth
import Breakdown.CertCell.InstanceDecay
import Breakdown.CertCell.InstanceSlope
import Breakdown.CertCell.InstanceRate
import Breakdown.CertCell.InstanceBasic
import Breakdown.CertCell.InstanceRegular
import Breakdown.CertCell.ShapeSupportRadius
import Breakdown.CertCell.ScalarPlaneMin
import Breakdown.CertCell.InstanceLinkRows

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

theorem actuatorPairing_holds : ActuatorPairingHolds :=
  actuatorPairing_of_solenoidal_and_gradient
    (fun w P h wt Γ W HW _ _ _ _ hw v G H g hv M hM ψ hψ hper hsupp hdiv =>
      multiplierField_pairing_of_solenoidal w P h wt Γ W HW hw v G H g hv M hM ψ hψ hper hsupp hdiv)
    (fun w P h wt Γ W HW _ _ _ _ hw b hb v G H g hv M hM =>
      multiplierField_pairing_gradient_part w P h wt Γ W HW hw b hb v G H g hv M hM)

theorem stateEnclosureCertificateNonneg_holds : Certificate.StateEnclosureCertificateNonneg :=
  Certificate.stateEnclosureCertificateNonneg_of_holds Certificate.signedCertificateTerminal
    Certificate.signedSlackBound Certificate.complexNodeRealBound Certificate.realRestrictionValue
    Certificate.coordinateSlack

theorem generatorPairingMoments_holds : Instance.GeneratorPairingMoments :=
  Instance.generatorPairingMoments_of_halves
    (fun M R m tauMax hR F hFm hFp hF2 a => Instance.generator_upper_pairing M R m tauMax hR F hFm hFp hF2 a)
    (fun M R m tauMax hR F hFm hFp hF2 a => Instance.generator_lower_pairing M R m tauMax hR F hFm hFp hF2 a)

theorem rowsClassForm_holds : Instance.RowsClassForm :=
  Instance.rowsClassForm_of
    (fun F hFm hF2 m κ S hS hSb hS0 c => Instance.labelVel_integrableOn F hFm hF2 m κ S hS hSb hS0 c)
    Instance.generatorPairingMatrixFormula Instance.rowPairingPosDef generatorPairingMoments_holds
    (Instance.rowNormIdentity Instance.generatorPairingMatrixFormula)

theorem instanceParts_holds : Instance.InstanceParts where
  pairing_formula := Instance.generatorPairingMatrixFormula
  pairing_posDef := Instance.rowPairingPosDef
  orthonormal := Instance.rowFieldsOrthonormal Instance.cellVecFieldRegular
  moments := generatorPairingMoments_holds
  norm_identity := Instance.rowNormIdentity Instance.generatorPairingMatrixFormula
  class_form := rowsClassForm_holds
  smooth := Instance.scalarSmoothOfJoins
  derivative_decay := Instance.scalarDerivativeDecay Instance.scalarSmoothOfJoins
  slope_bound := Instance.scalarSlopeBoundOfJoins
  rate := Instance.scalarRateOfDecay Instance.scalarSlopeBoundOfJoins
  scalar_basic := Instance.scalarBasicFacts
  step_basic := Instance.stepBasicFacts
  mirror := Instance.mirrorEval
  vec_regular := Instance.cellVecFieldRegular
  mat_regular := Instance.cellMatFieldRegular

section CellLayerBreakdown

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem halfPlaneFormBound_of_parts (hInit : InitialStateHolds) (hCell : CellCalculus.CellFormAssemblyStatement)
    (hPair : InstancePair.PairSharesFromSurrogateProfiles) (hCredit : CreditEval.CreditLeavesBoundHolds)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X)
    (hP : CellJunctions D R e T) : HalfPlaneFormBound D :=
  halfPlaneFormBound_of_hypothesis instanceParts_holds formNegFinite hInit stateEnclosureCertificateNonneg_holds
    hPair hCredit GivenShape.compactFieldSupportRadius_holds hCell rowSharesOfInstance D X R T e h hL hP

theorem rowRestClause_of_bridge_initial_cellForm (hBridge : Bridge.ModeDensityBridgeHolds)
    (hInit : InitialStateHolds) (hCell : CellCalculus.CellFormAssemblyStatement)
    (hPair : InstancePair.PairSharesFromSurrogateProfiles) (hCredit : CreditEval.CreditLeavesBoundHolds)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X)
    (hP : CellJunctions D R e T) :
    CoerciveWeak.RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight :=
  rowRestClause_of_halfPlane actuatorPairing_holds D
    (densityIdentity_of_hypothesis hBridge instanceParts_holds ScalarShape.chartBoundFacts D X R T e h hL)
    (admissible_of_hypothesis instanceParts_holds D X R T e h hL)
    (fun q hq i => (instanceConsequences_of_hypothesis instanceParts_holds D X R T e h hL).actuators q hq i)
    h.box_uniform.model_eq h.box_uniform.c_eq
    (halfPlaneFormBound_of_parts hInit hCell hPair hCredit D X R T e h hL hP)

theorem extendedCoerciveClause_of_bridge_initial_cellForm (hBridge : Bridge.ModeDensityBridgeHolds)
    (hInit : InitialStateHolds) (hCell : CellCalculus.CellFormAssemblyStatement)
    (hPair : InstancePair.PairSharesFromSurrogateProfiles) (hCredit : CreditEval.CreditLeavesBoundHolds)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X)
    (hP : CellJunctions D R e T)
    (hrad : ∀ j ∈ D.cert.adjointSet, 0 ≤ D.cert.radius j)
    (hwup : ∀ y, D.cert.weightFn y ≤ D.cert.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (D.cert.actuator i))
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖D.cert.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (D.cert.actuatorBound ^ 2))
    {epsSup epsGradSup ratio : ℝ}
    (hm : ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn (D.cert.model q) (D.modelHess q) D.cert.weight epsSup epsGradSup ratio)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt D.cert.weight) ^ 2 / D.coercivity
      + ratio / (D.pieces 0).cμ) / Real.sqrt D.coercivity ≤ D.cert.coerciveL2)
    (hPin : Real.sqrt (D.pinWeight / D.coercivity) ≤ D.cert.coercivePin) :
    CoerciveWeak.ExtendedCoerciveClause D.cert := by
  obtain ⟨B, hB⟩ := hL.model_state
  exact CoerciveWeak.extendedCoerciveClause_of_pieceData_proved hrad hwup hactm hactp hnorm D.modelHess (fun _ => B)
    (fun q hq => by rw [h.box_uniform.model_eq q hq]; exact hB)
    D.pieces D.bounds h.box_uniform.c_eq h.box_uniform.cμ_eq (by rw [h.pinWeight_eq]; norm_num) hm
    (rowRestClause_of_bridge_initial_cellForm hBridge hInit hCell hPair hCredit D X R T e h hL hP) hL2 hPin

end CellLayerBreakdown

end CertCell

end Breakdown
