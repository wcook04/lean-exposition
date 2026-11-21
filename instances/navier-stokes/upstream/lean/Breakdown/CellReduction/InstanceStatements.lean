import Breakdown.CertCell.ShapeStatements
import Breakdown.Cert.ExtendedStatement
import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.ReductionStatements
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline cellCount cellIndex atFirst weightPoly heightRatio)

structure StructuralClauses {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  target_continuous : ContinuousOn d.target d.params
  profile_smooth : ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space => d.profile z.1 z.2.1 z.2.2)
  profile_periodic : ∀ q, IsTimePeriodic (d.profile q)
  profile_divergence : ∀ q ∈ d.params, ∀ σ y, divergenceAt (d.profile q σ) y = 0
  profile_decay : ∀ q ∈ d.params, ∀ σ y, ‖d.profile q σ y‖ ≤ d.decay / (1 + ‖y‖) ∧
    ‖fderiv ℝ (d.profile q σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ 2 ∧
    ‖d.profileSecondDeriv q σ y‖ ≤ d.decay / (1 + ‖y‖) ^ 3
  profileSecondDeriv_measurable : ∀ q ∈ d.params,
    AEStronglyMeasurable (fun z : ℝ × Space => d.profileSecondDeriv q z.1 z.2) volume
  profileSecondDeriv_periodic : ∀ q ∈ d.params, IsTimePeriodic (d.profileSecondDeriv q)
  profileSecondDeriv_weak : ∀ q ∈ d.params, ∀ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => fderiv ℝ (d.profile q σ) y (unitVector j))
      (fun y => (d.profileSecondDeriv q σ y).flip (unitVector j))
  profile_invariant : ∀ q ∈ d.params, ∀ γ ∈ d.symmetries, ∀ σ y,
    d.profile q (σ + γ.2) (γ.1 y) = γ.1 (d.profile q σ y)
  pressureGrad_measurable : ∀ q ∈ d.params,
    AEStronglyMeasurable (fun z : ℝ × Space => d.pressureGrad q z.1 z.2) volume
  pressureGrad_periodic : ∀ q ∈ d.params, IsTimePeriodic (d.pressureGrad q)
  pressureGrad_orthogonal : ∀ q ∈ d.params, ∀ φ, IsSpaceTimeTestField φ →
    ∫ z : ℝ × Space, inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2) = 0
  adjoint_measurable : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    AEStronglyMeasurable (fun z : ℝ × Space => d.adjoint j q z.1 z.2) volume
  adjoint_periodic : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, IsTimePeriodic (d.adjoint j q)

def StepPhaseHolds : Prop :=
  ∀ (L edge : ℝ) (S : StepProfile), 0 < L → IsStepProfile S edge →
    IsRadialPhase (stepPhase L S) ∧ ∀ s, s ≤ (L * edge / (1 - edge)) ^ 2 → stepPhase L S s = 0

namespace ProfileShapeEntry

variable {k : ℕ} (R : ProfileShapeEntry k)

end ProfileShapeEntry

def InstantiationHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k)
    (Pr : PressureShapeEntry k) (Z : AdjointShapeEntry k),
    Instance.GeneratedByClassSymmetries D → (∀ j, D.cert.scale j ≠ 0) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume) →
    (∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤) →
    InstantiationBounded D R Pr Z →
    ∃ B : ℝ, StructuralClauses { D.cert with decay := B }

structure AdjointFieldFacts {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  weak_divergence : ∀ j ∈ d.adjointSet, ∀ q σ, ∀ φ : Space → ℝ, IsTestFunction φ →
    ∫ y, fderiv ℝ φ y (d.adjoint j q σ y) = 0
  field : ∀ j ∈ d.adjointSet, ∃ (A : ℝ → Space → Space) (C : ℝ),
    (∀ q, AdjointDefect.IsAdjointField (d.adjoint j q) C 3) ∧
    (∀ q, AdjointDefect.IsCurlPotential (d.adjoint j q) A C 2)

def AdjointFieldHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (Z : AdjointShapeEntry k),
    IsAdjointShapeEntry D Z → AdjointFieldFacts D.cert

def FieldDecayOrderHolds : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (e : ℕ), IsShapeParams P → IsTimeFieldData D →
    (∀ κ ∈ D.keys, e ≤ (D.amp κ).highOrder) → ∃ C : ℝ, ∀ σ y,
      ‖shapeInfoField P D σ y‖ ≤ C / (1 + ‖y‖) ^ e ∧
      ‖deriv (fun s => shapeInfoField P D s y) σ‖ ≤ C / (1 + ‖y‖) ^ e ∧
      ‖fderiv ℝ (shapeInfoField P D σ) y‖ ≤ C / (1 + ‖y‖) ^ (e + 1) ∧
      ‖shapeHess P D σ y‖ ≤ C / (1 + ‖y‖) ^ (e + 2)

def SecondDerivAgreeHolds : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∀ σ,
    ∀ᵐ y, DifferentiableAt ℝ (fun x => fderiv ℝ (shapeInfoField P D σ) x) y ∧
      AdjointDefect.secondDeriv (shapeInfoField P D σ) y = shapeHess P D σ y

def FieldPotentialHolds : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D →
    (∀ κ ∈ D.keys, 3 ≤ (D.amp κ).highOrder) → ∃ (A : ℝ → Space → Space) (C : ℝ),
      ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2) ∧ IsTimePeriodic A ∧
      (∀ σ y, AdjointDefect.curlAt (A σ) y = shapeInfoField P D σ y) ∧
      ∀ σ y, ‖A σ y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧ ‖deriv (fun s => A s y) σ‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
        ‖fderiv ℝ (A σ) y‖ ≤ C / (1 + ‖y‖) ^ 3

def ClassicalDivergenceWeakHolds : Prop :=
  ∀ v : Space → Space, ContDiff ℝ 1 v → (∀ y, divergenceAt v y = 0) →
    ∀ φ : Space → ℝ, IsTestFunction φ → ∫ y, fderiv ℝ φ y (v y) = 0

namespace OffsetExpansionEntry

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k)
  (Pr : PressureShapeEntry k) (O : OffsetExpansionEntry k)

end OffsetExpansionEntry

def ProfileSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k),
    IsProfileShapeEntry D R → ∀ q σ y,
      D.cert.profile q σ y = profileCentreAt R q σ y + ∑ i, q i • profileTangentAt R q i σ y

def ProfilePiecesFlowHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k) (M : ℝ),
    IsProfileShapeEntry D R → ∃ B : ℝ, ∀ q : Fin k → ℝ, (∀ i, |q i| ≤ M) →
      AdjointDefect.IsFlowPiece (profileCentreAt R q) B ∧ ∀ i, AdjointDefect.IsFlowPiece (profileTangentAt R q i) B

def AdjointStructureHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k)
    (Pr : PressureShapeEntry k) (Z : AdjointShapeEntry k) (O : OffsetExpansionEntry k)
    (r : Fin k → AdjointDefect.AdjointDefectEntry k),
    (∀ j, D.cert.scale j ≠ 0) → InstantiationBounded D R Pr Z →
    (∀ q ∈ D.cert.params, 1 / D.cert.period q = O.freqCentre + ∑ i, q i * O.freqTangent i) →
    AdjointEntryLinks D R Z O r →
    ∀ j ∈ D.cert.adjointSet, AdjointDefect.AdjointDefectStructure D.cert j (r j)

structure ShiftPiecesLinks {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) (r : CertReduction.ShiftPieces k) : Prop where
  count_eq : r.count = 2
  piece_eq : ∀ a q σ y, r.piece a q σ y =
    if a.val = 0 then R.field 0 σ y - D.given σ y else R.field q σ y - R.field 0 σ y
  pieceGrad_eq : ∀ a q σ y, r.pieceGrad a q σ y =
    if a.val = 0 then fderiv ℝ (R.field 0 σ) y - fderiv ℝ (D.given σ) y
    else fderiv ℝ (R.field q σ) y - fderiv ℝ (R.field 0 σ) y

def ShiftPiecesLinkHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (F : GivenShapeEntry k) (R : ProfileShapeEntry k) (r : CertReduction.ShiftPieces k),
    IsGivenShapeEntry D X F → IsProfileShapeEntry D R →
    (∀ q ∈ D.cert.params, D.cert.model q = D.given) → ShiftPiecesLinks D R r →
    (∀ q ∈ D.cert.params, ∀ σ y, D.cert.profile q σ y - D.cert.model q σ y = ∑ a, r.piece a q σ y) ∧
    (∀ q ∈ D.cert.params, ∀ σ y,
      fderiv ℝ (D.cert.profile q σ) y - fderiv ℝ (D.cert.model q σ) y = ∑ a, r.pieceGrad a q σ y) ∧
    (∀ a, ∀ q ∈ D.cert.params, StronglyMeasurable (fun z : ℝ × Space => r.piece a q z.1 z.2)) ∧
    (∀ a, ∀ q ∈ D.cert.params, StronglyMeasurable (fun z : ℝ × Space => r.pieceGrad a q z.1 z.2))

def MovedParamsValidHolds : Prop :=
  ∀ (P : ShapeParams) (moving : ℝ → ℝ) (a : ℝ), IsShapeParams P → IsRadialPhase moving →
    IsShapeParams (movedParams P moving a)

def AffineFieldStructureHolds : Prop :=
  ∀ {k : ℕ} (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData) (gt : Fin k → OriginProfile)
    (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ),
    IsShapeParams P → IsOriginProfile g → (∀ i, IsOriginProfile (gt i)) →
    IsTimeFieldData centre → (∀ i, IsTimeFieldData (tangent i)) →
    IsTimePeriodic (affineField P g centre gt tangent q) ∧
    (∀ σ y, divergenceAt (affineField P g centre gt tangent q σ) y = 0) ∧
    AEStronglyMeasurable (fun z : ℝ × Space => affineSecondDeriv P g centre gt tangent q z.1 z.2) volume ∧
    IsTimePeriodic (affineSecondDeriv P g centre gt tangent q)

def AffineFieldWeakSecondDerivHolds : Prop :=
  ∀ {k : ℕ} (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData) (gt : Fin k → OriginProfile)
    (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ),
    IsShapeParams P → IsOriginProfile g → (∀ i, IsOriginProfile (gt i)) →
    IsTimeFieldData centre → (∀ i, IsTimeFieldData (tangent i)) → ∀ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => fderiv ℝ (affineField P g centre gt tangent q σ) y (unitVector j))
      (fun y => (affineSecondDeriv P g centre gt tangent q σ y).flip (unitVector j))

def AffineFieldInvariantHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ),
    Instance.GeneratedByClassSymmetries D → P.azimuthOrder = D.azimuthOrder →
    IsShapeParams P → IsOriginProfile g → (∀ i, IsOriginProfile (gt i)) →
    IsTimeFieldData centre → (∀ i, IsTimeFieldData (tangent i)) →
    ∀ γ ∈ D.cert.symmetries, ∀ σ y,
      affineField P g centre gt tangent q (σ + γ.2) (γ.1 y) = γ.1 (affineField P g centre gt tangent q σ y)

def MovedFieldJointSmoothHolds : Prop :=
  ∀ {k : ℕ} (P : ShapeParams) (moving : ℝ → ℝ) (rate : Fin k → ℝ) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData),
    IsShapeParams P → IsRadialPhase moving → IsOriginProfile g → (∀ i, IsOriginProfile (gt i)) →
    IsTimeFieldData centre → (∀ i, IsTimeFieldData (tangent i)) →
    ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space =>
      affineField (movedParams P moving (phaseRate rate z.1)) g centre gt tangent z.1 z.2.1 z.2.2)

def MovedFieldUniformDecayHolds : Prop :=
  ∀ {k : ℕ} (P : ShapeParams) (moving : ℝ → ℝ) (rate : Fin k → ℝ) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData) (M : ℝ),
    IsShapeParams P → IsRadialPhase moving → IsOriginProfile g → (∀ i, IsOriginProfile (gt i)) →
    IsTimeFieldData centre → (∀ i, IsTimeFieldData (tangent i)) →
    ∃ B : ℝ, ∀ q : Fin k → ℝ, (∀ i, |q i| ≤ M) → ∀ σ y,
      ‖affineField (movedParams P moving (phaseRate rate q)) g centre gt tangent q σ y‖ ≤ B / (1 + ‖y‖) ∧
      ‖fderiv ℝ (affineField (movedParams P moving (phaseRate rate q)) g centre gt tangent q σ) y‖ ≤
        B / (1 + ‖y‖) ^ 2 ∧
      ‖affineSecondDeriv (movedParams P moving (phaseRate rate q)) g centre gt tangent q σ y‖ ≤ B / (1 + ‖y‖) ^ 3

def ParamsBoundedHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), (∀ j, d.scale j ≠ 0) →
    ∃ M : ℝ, ∀ q ∈ d.params, ∀ i, |q i| ≤ M

def PinValueContinuousHolds : Prop :=
  ∀ {k : ℕ} (W : (Fin k → ℝ) → ℝ → Space → Space) (χ : ℝ → Space → (Space →L[ℝ] Space))
    (S : Set (Fin k → ℝ)) (B : ℝ),
    ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space => W z.1 z.2.1 z.2.2) →
    (∀ q ∈ S, ∀ σ y, ‖fderiv ℝ (W q σ) y‖ ≤ B / (1 + ‖y‖) ^ 2) →
    AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) volume →
    periodLIntegral (fun σ y => matSq (χ σ y)) < ⊤ →
    ContinuousOn (fun q => pinValue χ (fun σ y => fderiv ℝ (W q σ) y)) S

def PressureFieldRegularHolds : Prop :=
  ∀ (P : ShapeParams) (D : PressureFieldData), IsShapeParams P → IsPressureFieldData D →
    Continuous (fun z : ℝ × Space => shapePressure P D z.1 z.2) ∧
    (∀ σ y, shapePressure P D (σ + 1) y = shapePressure P D σ y) ∧
    ∀ r : ℝ, ∃ L : NNReal, ∀ σ, LipschitzOnWith L (shapePressure P D σ) (Metric.closedBall 0 r)

def ScalarGradientOrthogonalHolds : Prop :=
  ∀ p : ℝ → Space → ℝ, Continuous (fun z : ℝ × Space => p z.1 z.2) →
    (∀ σ, ∀ r : ℝ, ∃ L : NNReal, LipschitzOnWith L (p σ) (Metric.closedBall 0 r)) →
    AEStronglyMeasurable (fun z : ℝ × Space => gradient (p z.1) z.2) volume ∧
    ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (gradient (p z.1) z.2) (φ z.1 z.2) = 0

def BallAgreementHolds : Prop :=
  ∀ (P : ShapeParams) (moving : ℝ → ℝ) (a r : ℝ) (D : TimeFieldData) (E : PressureFieldData),
    IsShapeParams P → IsRadialPhase moving → (∀ s, s ≤ r ^ 2 → moving s = 0) → IsTimeFieldData D →
    IsPressureFieldData E → ∀ σ y, ‖y‖ < r →
      shapeInfoField (movedParams P moving a) D σ y = shapeInfoField P D σ y ∧
      fderiv ℝ (shapeInfoField (movedParams P moving a) D σ) y = fderiv ℝ (shapeInfoField P D σ) y ∧
      shapeHess (movedParams P moving a) D σ y = shapeHess P D σ y ∧
      shapePressure (movedParams P moving a) E σ y = shapePressure P E σ y ∧
      gradient (shapePressure (movedParams P moving a) E σ) y = gradient (shapePressure P E σ) y

def OffsetBallIdentityHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (F : GivenShapeEntry k) (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k)
    (Z : AdjointShapeEntry k) (O : OffsetExpansionEntry k),
    IsGivenShapeEntry D X F → InstantiationBounded D R Pr Z → IsOffsetExpansionEntry D R Pr Z O →
    ∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params,
      ballPairing R.matchRadius (D.cert.defect q) (D.cert.adjoint j q) =
        ballPairing R.matchRadius (O.centreCoefficient D R Pr) (shapeInfoField Z.params (Z.field j))
        + (∑ i, q i * ballPairing R.matchRadius (O.linearCoefficient D R Pr i) (shapeInfoField Z.params (Z.field j)))
        + (∑ i, ∑ l ∈ Finset.Ici i, q i * q l *
          ballPairing R.matchRadius (O.quadraticCoefficient R i l) (shapeInfoField Z.params (Z.field j)))

def OffsetClauseHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (F : GivenShapeEntry k) (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k)
    (Z : AdjointShapeEntry k) (O : OffsetExpansionEntry k),
    (∀ j, D.cert.scale j ≠ 0) →
    IsGivenShapeEntry D X F → InstantiationBounded D R Pr Z → IsOffsetExpansionEntry D R Pr Z O →
    (∀ q ∈ D.cert.params,
      periodLIntegral (fun σ y => ‖D.cert.defect q σ y‖ ^ 2) ≤ ENNReal.ofReal (D.cert.defectBound q ^ 2)) →
    (∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params, ∀ σ,
      ∫⁻ y, ENNReal.ofReal (‖D.cert.adjoint j q σ y‖ ^ 2) ≤ ENNReal.ofReal (D.cert.adjointL2 j ^ 2)) →
    ∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params,
      |D.cert.adjustedMultiplier q j - D.cert.scale j * q j| ≤ D.cert.adjointOffset j

end Instantiation

end CellReduction

end Breakdown
