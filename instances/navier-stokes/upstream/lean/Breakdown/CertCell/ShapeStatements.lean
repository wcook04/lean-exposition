import Breakdown.CertCell.ShapeDefs
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst)

structure IsKeyFieldSmooth (f : Space → Fin 3 → ℂ) : Prop where
  smooth : ContDiff ℝ 1 f
  gradient_slope_bound : ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall 0 R)

structure IsKeyFieldDecay (f : Space → Fin 3 → ℂ) : Prop where
  bound : ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C / (1 + ‖y‖) ^ 3

def complexDivergence (f : Space → Fin 3 → ℂ) (y : Space) : ℂ :=
  ∑ i : Fin 3, fderiv ℝ f y (unitVector i) i

def LogPhaseIsRadial : Prop :=
  ∀ rate hbase : ℝ, 0 < hbase → IsRadialPhase (logRadialPhase rate hbase)

def OriginProfileSmooth : Prop :=
  ∀ g : OriginProfile, IsOriginProfile g → ContDiffOn ℝ 2 g.eval (Set.Iio 1) ∧
    ∀ R : ℝ, R < 1 → ∃ L : NNReal, LipschitzOnWith L (deriv (deriv g.eval)) (Set.Icc (-R) R)

def JoinedSplineSmooth : Prop :=
  ∀ (a b : ℕ) (S : Spline), IsJoinedSpline a b S →
    ContDiff ℝ (min a b) (fun z : ℝ × ℝ => S.evalHalf z.1 z.2)

def JoinedSplineGradSlopeBound : Prop :=
  ∀ (a b : ℕ) (S : Spline), IsJoinedSpline a b S → 1 ≤ a → 1 ≤ b → ∀ R : ℝ, ∃ L : NNReal,
    LipschitzOnWith L (fderiv ℝ (fun z : ℝ × ℝ => S.evalHalf z.1 z.2)) (Metric.closedBall 0 R)

def SplineDerivatives : Prop :=
  ∀ (a b : ℕ) (S : Spline), IsJoinedSpline a b S →
    (1 ≤ a → IsJoinedSpline (a - 1) b (tDerivSpline S) ∧
      ∀ t x, deriv (fun t' => S.evalHalf t' x) t = (tDerivSpline S).evalHalf t x) ∧
    (1 ≤ b → IsJoinedSpline a (b - 1) (xDerivSpline S) ∧
      ∀ t x, deriv (fun x' => S.evalHalf t x') x = (xDerivSpline S).evalHalf t x)

def SplineReflection : Prop :=
  ∀ (a b : ℕ) (odd : Bool) (S : Spline), IsJoinedSpline a b S →
    IsJoinedSpline a b (reflectSpline odd S) ∧
      ∀ t x, (reflectSpline odd S).evalHalf t x = (if odd then -1 else 1) * S.evalHalf t (-x)

def SplineConjugation : Prop :=
  ∀ (a b : ℕ) (S : Spline), IsJoinedSpline a b S →
    IsJoinedSpline a b S.conj ∧ ∀ t x, S.conj.evalHalf t x = starRingEnd ℂ (S.evalHalf t x)

def SplineAgreementRules : Prop :=
  ∀ (a b : ℕ) (odd : Bool) (S T U : Spline),
    SplineAgrees S S ∧ (SplineAgrees S T → SplineAgrees T S) ∧
    (SplineAgrees S T → SplineAgrees T U → SplineAgrees S U) ∧
    (SplineAgrees S T → SplineAgrees S.conj T.conj ∧ SplineAgrees (reflectSpline odd S) (reflectSpline odd T)) ∧
    SplineAgrees S.conj.conj S ∧ SplineAgrees (reflectSpline odd (reflectSpline odd S)) S ∧
    SplineAgrees (reflectSpline odd S).conj (reflectSpline odd S.conj) ∧
    (SplineAgrees S T → IsJoinedSpline a b S → IsJoinedSpline a b T) ∧
    (SplineAgrees S T → IsFullMesh S.mesh → ∀ t x, S.evalHalf t x = T.evalHalf t x)

def JetSplineJoined : Prop :=
  ∀ H : JetSpline, IsJetAxis H.tAxis 0 1 → IsJetAxis H.xAxis (-1) 1 →
    IsJoinedSpline (H.tAxis.depth - 1) (H.xAxis.depth - 1) H.toSpline

def JetReflection : Prop :=
  ∀ (odd : Bool) (H : JetSpline), IsJetAxis H.tAxis 0 1 → IsJetAxis H.xAxis (-1) 1 →
    IsSymmetricAxis H.xAxis → H.IsReflectFixed odd → SplineAgrees H.toSpline (reflectSpline odd H.toSpline)

def JetConjReflection : Prop :=
  ∀ (odd : Bool) (H : JetSpline), IsJetAxis H.tAxis 0 1 → IsJetAxis H.xAxis (-1) 1 →
    IsSymmetricAxis H.xAxis → H.IsConjReflectFixed odd →
      SplineAgrees H.toSpline (reflectSpline odd H.toSpline.conj)

def JetStartVanish : Prop :=
  ∀ H : JetSpline, IsJetAxis H.tAxis 0 1 → IsJetAxis H.xAxis (-1) 1 → H.VanishesAtStart →
    ∀ j < cellCount H.toSpline.mesh.xBreaks, atFirst 0 (H.toSpline.piece 0 j) = 0

def JetSplineVanishesFrom : Prop :=
  ∀ (H : JetSpline) (tb : ℝ), IsJetAxis H.tAxis 0 1 → IsJetAxis H.xAxis (-1) 1 →
    (∀ k p e, tb ≤ H.tAxis.breaks.getD k 1 → H.coef (JetDof.node k p) e = 0) →
    (∀ i s e, tb ≤ H.tAxis.breaks.getD i 1 → H.coef (JetDof.bubble i s) e = 0) →
      H.toSpline.VanishesFrom tb

def ClosureDataValid : Prop :=
  ∀ (S : Finset FieldKey) (given : FieldKey → KeyAmp), IsGivenKeyData S given →
    IsTimeFieldData (closureData S given)

def TypeOneKeySmooth : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P → IsTimeFieldData D →
    κ ∈ D.keys → κ.label.1 ≠ 0 → IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ)

def TypeTwoKeySmooth : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P → IsTimeFieldData D →
    κ ∈ D.keys → κ.label.1 = 0 → IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ)

def TypeOneKeyDecay : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P → IsTimeFieldData D →
    κ ∈ D.keys → κ.label.1 ≠ 0 → IsKeyFieldDecay (keyVector P κ (D.amp κ) σ)

def TypeTwoKeyDecay : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P → IsTimeFieldData D →
    κ ∈ D.keys → κ.label.1 = 0 → IsKeyFieldDecay (keyVector P κ (D.amp κ) σ)

def KeyDivergenceFree : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (y : Space), IsShapeParams P →
    IsTimeFieldData D → κ ∈ D.keys → complexDivergence (keyVector P κ (D.amp κ) σ) y = 0

def KeyTimeShift : Prop :=
  ∀ (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ τ : ℝ) (y : Space),
    keyVector P κ A (σ + τ) y =
      fun i => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * τ : ℝ) : ℂ) * Complex.I) * keyVector P κ A σ y i

def KeyRotation : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ φ : ℝ) (y : Space), IsTimeFieldData D →
    κ ∈ D.keys → keyVector P κ (D.amp κ) σ (axialRot φ y) =
      fun i => Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        rotateVec φ (keyVector P κ (D.amp κ) σ y) i

def KeyFlip : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (y : Space), IsTimeFieldData D →
    κ ∈ D.keys → keyVector P κ.flipKey (D.amp κ.flipKey) σ (flipPoint y) = flipVec (keyVector P κ (D.amp κ) σ y)

def KeyConjugate : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (y : Space), IsTimeFieldData D →
    κ ∈ D.keys → keyVector P κ.negKey (D.amp κ.negKey) σ y = fun i => starRingEnd ℂ (keyVector P κ (D.amp κ) σ y i)

def FieldJointSmooth : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D →
    ContDiff ℝ 1 (fun z : ℝ × Space => shapeInfoField P D z.1 z.2) ∧ IsTimePeriodic (shapeInfoField P D) ∧
      AEStronglyMeasurable (fun z : ℝ × Space => shapeHess P D z.1 z.2) volume ∧ IsTimePeriodic (shapeHess P D)

def FieldDivergenceFree : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D →
    ∀ σ y, divergenceAt (shapeInfoField P D σ) y = 0

def FieldWeakHessian : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∀ σ (j : Fin 3),
    IsWeakGradient (fun y => fderiv ℝ (shapeInfoField P D σ) y (unitVector j))
      (fun y => (shapeHess P D σ y).flip (unitVector j))

def FieldDecay : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∃ B : ℝ, ∀ σ y,
    ‖shapeInfoField P D σ y‖ ≤ B / (1 + ‖y‖) ∧ ‖fderiv ℝ (shapeInfoField P D σ) y‖ ≤ B / (1 + ‖y‖) ^ 2 ∧
      ‖shapeHess P D σ y‖ ≤ B / (1 + ‖y‖) ^ 3

def FieldClassInvariant : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D →
    (∀ σ y, shapeInfoField P D σ (flipPoint y) = flipPoint (shapeInfoField P D σ y)) ∧
    (∀ σ y, shapeInfoField P D (σ + 1 / 2) (axialRot (Real.pi / P.azimuthOrder) y) =
      axialRot (Real.pi / P.azimuthOrder) (shapeInfoField P D σ y)) ∧
    (∀ σ y, shapeInfoField P D σ (axialRot (2 * Real.pi / P.azimuthOrder) y) =
      axialRot (2 * Real.pi / P.azimuthOrder) (shapeInfoField P D σ y))

def FieldHessFlip : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∀ σ y a b,
    shapeHess P D σ (flipPoint y) (flipPoint a) (flipPoint b) = flipPoint (shapeHess P D σ y a b)

def FieldModeFormula : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∀ ξ σ y,
    modeVel ξ (shapeInfoField P D) σ y = ∑ κ ∈ keysOfHarmonic P.azimuthOrder D ξ, keyVector P κ (D.amp κ) σ y

def FieldHarmonicExpansion : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)), IsShapeParams P → IsTimeFieldData D →
    harmonicsOf P.azimuthOrder D ⊆ S → (∀ β ∈ S, -β ∈ S) →
      Bridge.IsHarmonicExpansion S (shapeInfoField P D) (shapeHess P D)

def CompactFieldSupport : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (tb : ℝ), IsShapeParams P → IsCompactTimeFieldData tb D →
    ∃ R : ℝ, ∀ σ y, R < ‖y‖ → shapeInfoField P D σ y = 0

def ActuatorShape : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (tb : ℝ), IsShapeParams P → IsCompactTimeFieldData tb D →
    Instance.ActuatorShapeFacts P.azimuthOrder (labelsOf D) (shapeInfoField P D)

structure ShapeParts : Prop where
  log_phase : LogPhaseIsRadial
  origin_profile : OriginProfileSmooth
  spline_smooth : JoinedSplineSmooth
  spline_slope_bound : JoinedSplineGradSlopeBound
  spline_derivatives : SplineDerivatives
  spline_reflection : SplineReflection
  spline_conjugation : SplineConjugation
  agreement_rules : SplineAgreementRules
  jet_joined : JetSplineJoined
  jet_reflection : JetReflection
  jet_conj_reflection : JetConjReflection
  jet_start : JetStartVanish
  jet_vanish : JetSplineVanishesFrom
  closure_valid : ClosureDataValid
  type_one_smooth : TypeOneKeySmooth
  type_two_smooth : TypeTwoKeySmooth
  type_one_decay : TypeOneKeyDecay
  type_two_decay : TypeTwoKeyDecay
  key_divergence : KeyDivergenceFree
  key_time : KeyTimeShift
  key_rotation : KeyRotation
  key_flip : KeyFlip
  key_conjugate : KeyConjugate
  field_smooth : FieldJointSmooth
  field_divergence : FieldDivergenceFree
  field_weak_hessian : FieldWeakHessian
  field_decay : FieldDecay
  field_class : FieldClassInvariant
  field_hess_flip : FieldHessFlip
  field_modes : FieldModeFormula
  field_expansion : FieldHarmonicExpansion
  compact_support : CompactFieldSupport
  actuator_shape : ActuatorShape

theorem weakHessianState_of_parts (h : ShapeParts) (P : ShapeParams) (D : TimeFieldData)
    (hP : IsShapeParams P) (hD : IsTimeFieldData D) :
    ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState (shapeInfoField P D) (shapeHess P D) B := by
  obtain ⟨hs, hp, hm, hhp⟩ := h.field_smooth P D hP hD
  obtain ⟨B, hB⟩ := h.field_decay P D hP hD
  exact ⟨B, ⟨hs, hp, h.field_divergence P D hP hD, hm, hhp, h.field_weak_hessian P D hP hD, hB⟩⟩

theorem flipModel_of_parts (h : ShapeParts) (P : ShapeParams) (D : TimeFieldData)
    (hP : IsShapeParams P) (hD : IsTimeFieldData D) :
    Bridge.IsFlipInvariantModel (shapeInfoField P D) (shapeHess P D) :=
  ⟨(h.field_class P D hP hD).1, h.field_hess_flip P D hP hD⟩

structure IsGivenShapeEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k) : Prop where
  params_valid : IsShapeParams F.params
  model_valid : IsTimeFieldData F.model
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

structure LayerShapeFacts {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) : Prop where
  actuator_shape : ∀ i, Instance.ActuatorShapeFacts D.azimuthOrder (X.actuatorModes i) (D.cert.actuator i)
  flip_model : Bridge.IsFlipInvariantModel D.given D.givenHess
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B
  model_harmonics : Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess
  harmonics_span : ∀ S : Finset (ℤ × ℤ), D.givenLabels ⊆ S → (∀ β ∈ S, -β ∈ S) → ∀ σ y i,
    D.given σ y i = ∑ β ∈ S, (modeVel β D.given σ y i).re

theorem layerShapeFacts_of_entry (h : ShapeParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (hF : IsGivenShapeEntry D X F) : LayerShapeFacts D X := by
  have hcov : harmonicsOf F.params.azimuthOrder F.model ⊆ D.givenLabels := hF.azimuth_eq ▸ hF.labels_cover
  refine ⟨fun i => ?_, ?_, ?_, ?_, fun S hS hSy σ y i => ?_⟩
  · rw [hF.actuatorModes_eq i, hF.actuator_eq i, ← hF.actuatorAzimuth_eq i]
    exact h.actuator_shape (F.actuatorParams i) (F.actuators i) (F.actuatorEdge i) (hF.actuatorParams_valid i)
      (hF.actuators_valid i)
  · rw [hF.given_eq, hF.givenHess_eq]
    exact flipModel_of_parts h F.params F.model hF.params_valid hF.model_valid
  · rw [hF.given_eq, hF.givenHess_eq]
    exact weakHessianState_of_parts h F.params F.model hF.params_valid hF.model_valid
  · rw [hF.given_eq, hF.givenHess_eq]
    exact h.field_expansion F.params F.model D.givenLabels hF.params_valid hF.model_valid hcov hF.labels_symm
  · rw [hF.given_eq]
    exact (h.field_expansion F.params F.model S hF.params_valid hF.model_valid (hcov.trans hS) hSy).field_span σ y i

theorem givenModeFormula_of_entry (h : ShapeParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (hF : IsGivenShapeEntry D X F) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ξ D.given σ y = ∑ κ ∈ keysOfHarmonic D.azimuthOrder F.model ξ, keyVector F.params κ (F.model.amp κ) σ y := by
  rw [hF.given_eq, ← hF.azimuth_eq]
  exact h.field_modes F.params F.model hF.params_valid hF.model_valid ξ σ y

theorem givenData_valid_of_closure (h : ShapeParts) (S : Finset FieldKey) (given : FieldKey → KeyAmp)
    (hS : IsGivenKeyData S given) : IsTimeFieldData (closureData S given) :=
  h.closure_valid S given hS

end GivenShape

end CertCell

end Breakdown
