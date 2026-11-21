import Breakdown.FracCell.MeshDefs
import Breakdown.CertCell.GaugeKeyDefs
import Breakdown.CertCell.Defs
import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.CertificateStatements
import Breakdown.CertCell.CertificateEnclosureStatements
import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.CreditEvalStatements
import Breakdown.CertCell.TailCoefficients
import Breakdown.CertCell.ShapeJetEntry
import Breakdown.CertCell.ShapeSupport
import Breakdown.CertCell.ShapeJetScaled
import Breakdown.CertCell.InstanceClauseSplit
import Breakdown.CertCell.ShapeMeasurable
import Breakdown.CertCell.ShapeJunction
import Breakdown.Cert.ExtendedCoerciveMain
import Breakdown.CertCell.StatementDefs

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def formScalarWith (cκ : ℝ) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : Fin k → ℝ) (F : ℝ → Space → Space) : ℝ :=
  cκ * D.cert.multiplierWeight ^ 2 * ∑ i, κ i ^ 2
    - ∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
    - D.coercivity * D.cert.rows F ^ 2 - D.pinWeight * vecNorm (fun i => pinValue (D.cert.pin i) G) ^ 2

end CellLayerData

section Statements

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def HalfPlaneFormBoundWith (D : CellLayerData k C nE nM) (cForm cκ : ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (D.cert.model q) D.cert.actuator κ v G g F →
        (D.withFormCoercivity cForm).formNeg q v G H < ⊤ ∧
        ENNReal.ofReal (D.formScalarWith cκ q v G H κ F / (4 * Real.pi))
            + (D.withFormCoercivity cForm).formNeg q v G H
          ≤ (D.withFormCoercivity cForm).formPos q v G H
            + ENNReal.ofReal (-D.formScalarWith cκ q v G H κ F / (4 * Real.pi))

def HalfPlaneFormBound (D : CellLayerData k C nE nM) : Prop :=
  HalfPlaneFormBoundWith D D.coercivity D.coercivity

def formValueWith (D : CellLayerData k C nE nM) (cForm cκ : ℝ) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : Fin k → ℝ) (F : ℝ → Space → Space) : ℝ :=
  ((D.withFormCoercivity cForm).formPos q v G H).toReal - ((D.withFormCoercivity cForm).formNeg q v G H).toReal
    - D.formScalarWith cκ q v G H κ F / (4 * Real.pi)

def FormNegFinite (D : CellLayerData k C nE nM) (cForm : ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    (D.withFormCoercivity cForm).formNeg q v G H < ⊤

def FormValueNonneg (D : CellLayerData k C nE nM) (cForm cκ : ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (D.cert.model q) D.cert.actuator κ v G g F →
        (D.withFormCoercivity cForm).formPos q v G H < ⊤ → 0 ≤ formValueWith D cForm cκ q v G H κ F

def AdmissibleTuple.value {D : CellLayerData k C nE nM} {cForm : ℝ} {q : Fin k → ℝ} (cκ : ℝ)
    (x : AdmissibleTuple D cForm q) : ℝ :=
  formValueWith D cForm cκ q x.v x.G x.H x.κ x.F

def CoefficientLowerBounds (D : CellLayerData k C nE nM) (cForm : ℝ) : Prop :=
  ∃ B : ℝ, ∀ q ∈ D.cert.params, ∀ ι : ℤ × ℤ, ∀ p ∈ halfPlane,
    -B ≤ (ModeCoefficients.ofPieces ((D.withFormCoercivity cForm).pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).hess ∧
    -B ≤ (ModeCoefficients.ofPieces ((D.withFormCoercivity cForm).pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).curlHess ∧
    -B ≤ (ModeCoefficients.ofPieces ((D.withFormCoercivity cForm).pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).curl ∧
    -B ≤ (ModeCoefficients.ofPieces ((D.withFormCoercivity cForm).pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).strain ∧
    -B ≤ (p.1 ^ 2 + p.2 ^ 2) * (ModeCoefficients.ofPieces ((D.withFormCoercivity cForm).pieces q) (D.cert.period q)
      (D.bounds q) D.cert.weightFn D.azimuthOrder ι p).velocity

def FormNegFiniteHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (cForm B : ℝ),
    1 ≤ D.azimuthOrder → CoefficientLowerBounds D cForm →
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B → FormNegFinite D cForm

theorem halfPlaneFormBoundWith_of_value (D : CellLayerData k C nE nM) (cForm cκ : ℝ)
    (hN : FormNegFinite D cForm) (hV : FormValueNonneg D cForm cκ) : HalfPlaneFormBoundWith D cForm cκ := by
  intro q hq v G H g hv κ F hFm hFp hF2 hR
  have hNf := hN q hq v G H g hv
  refine ⟨hNf, ?_⟩
  by_cases hP : (D.withFormCoercivity cForm).formPos q v G H = ⊤
  · rw [hP, top_add]
    exact le_top
  have hV' := hV q hq v G H g hv κ F hFm hFp hF2 hR (lt_top_iff_ne_top.2 hP)
  unfold formValueWith at hV'
  rw [← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_toReal hNf.ne, neg_div]
  have hn : 0 ≤ ((D.withFormCoercivity cForm).formNeg q v G H).toReal := ENNReal.toReal_nonneg
  have hp : 0 ≤ ((D.withFormCoercivity cForm).formPos q v G H).toReal := ENNReal.toReal_nonneg
  rcases le_or_gt 0 (D.formScalarWith cκ q v G H κ F / (4 * Real.pi)) with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 hX), add_zero, ← ENNReal.ofReal_add hX hn]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [ENNReal.ofReal_of_nonpos hX.le, zero_add, ← ENNReal.ofReal_add hp (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

def DensityIdentity (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityPosWith (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formPos q v G H ∧
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityNegWith (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formNeg q v G H

def ActuatorPairingHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (wt : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    {w₀ epsSup epsGradSup ratio : ℝ},
    CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio →
    ∀ b, Instance.ActuatorFacts w b →
    ∀ v G H g, IsPerturbation Γ P v G H g → ∀ M, w.IsMultiplierField v G H M →
      periodPairing b M = multiplierRight w v G H b

def extPos (D : CellLayerData k C nE nM) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
    + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchPosMean v G p * ENNReal.ofReal p.1

def extNeg (D : CellLayerData k C nE nM) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)))
    + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1

def flipAverage (F : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / 2 : ℝ) • (F σ y + flipPoint (F σ (flipPoint y)))

def initialStateValue (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : ℕ → ℂ) : ℝ :=
  ∑ K, CellCert.CellFormula.quadFormValue (R.cellForm K)
      (CellCalculus.cellState D.mesh K (R.layouts K) v G H Pg κ ζ (fun j => η (R.portKey K j)))
    + 2 * ∑ j, Coupling.quadForm (R.creditPatch j).credit (CreditEval.creditData D R j v G H Pg κ ζ η)
    + globalForm D e κ ζ

def OffModesVanish (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ K, CellCalculus.offNeg D K q (D.charges (some K)) (R.entryCharges K) v G H = 0

def ExteriorNonneg (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    extNeg D q v G H < ⊤ ∧ extNeg D q v G H ≤ extPos D q v G H

def RowSharesMatch (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q,
    ∑ K, CellCalculus.rowShare D K (flipAverage x.F) = D.coercivity * D.cert.rows x.F ^ 2 / (4 * Real.pi)

def PairSharesBound (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q, ∀ ζ : Fin k → ℝ,
    ∑ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) x.κ ζ x.G
      ≤ (∑ i, x.κ i * multiplierRight (D.pieces q) x.v x.G x.H (D.cert.actuator i)
          + 2 * ∑ i, ζ i * pinValue (D.cert.pin i) x.G) / (4 * Real.pi) + e * ∑ i, x.κ i ^ 2
        + ∑ K, CellCalculus.pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) x.G

def CreditLeavesBound (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q, ∀ (Pg : ℝ → Space → Space) (ζ : Fin k → ℝ) (η : ℕ → ℂ),
    2 * ∑ j, Coupling.quadForm (R.creditPatch j).credit (CreditEval.creditData D R j x.v x.G x.H Pg x.κ ζ η)
      ≤ ∑ K, CellCalculus.creditShare D R K x.v

def PressureRecovered (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q,
    CellCalculus.IsPeriodicPressure (fun σ y => flipAverage x.F σ y - (x.g σ y - secondDerivTrace (x.H σ y)
      + CellCalculus.couplingField D.given x.v x.G σ y + ∑ i, x.κ i • D.cert.actuator i σ y))

def InitialStateBound (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q, ∀ ζ : Fin k → ℝ, ∀ η : ℕ → ℂ,
    ∀ Pg : ℝ → Space → Space, CellCalculus.IsPeriodicPressure Pg →
      (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) →
      CellCalculus.IsStrongRightSide D.given D.cert.actuator x.κ x.v x.G x.H x.g (flipAverage x.F) Pg →
      initialStateValue D R e x.v x.G x.H Pg x.κ ζ η ≤ x.value D.coercivity

def InitialStateHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D),
    IsCellMesh D.mesh → 0 < D.pinWeight →
    (∀ q ∈ D.cert.params, D.cert.model q = D.given) →
    (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
    FormNegFinite D D.coercivity →
    CellCalculus.CellFormBoundsHold D R → OffModesVanish D R → ExteriorNonneg D →
    RowSharesMatch D → CreditLeavesBound D R → (∀ K, 0 ≤ R.kappaCost K) → ∀ e ePair : ℝ, PairSharesBound D R ePair →
    ∑ K, R.kappaCost K + ePair ≤ e → InitialStateBound D R e

def TreeReduction (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ) : Prop :=
  PressureRecovered D → InitialStateBound D R e → FormValueNonneg D D.coercivity D.coercivity

def RowSharesOfInstanceHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM),
    Instance.RowsClassForm → Instance.IsInstanceEntry D X → Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    RowSharesMatch D

def chosenPressure (D : CellLayerData k C nE nM) {q : Fin k → ℝ}
    (x : AdmissibleTuple D D.coercivity q) : ℝ → Space → Space :=
  fun σ y => flipAverage x.F σ y - (x.g σ y - secondDerivTrace (x.H σ y)
    + CellCalculus.couplingField D.given x.v x.G σ y + ∑ i, x.κ i • D.cert.actuator i σ y)

def headPotential (Q : Space → Space) : Space → ℝ :=
  fun y => CellCert.CellFormula.potentialOf Q y - ⨍ z in Metric.ball (0 : Space) 1, CellCert.CellFormula.potentialOf Q z

def headPressure (L : CellCert.CellFormula.CellLayout) {j : ℕ} (n : ℤ) (x : CellCert.Assembly.FieldTuple j) : ℝ × ℝ → ℂ :=
  fun p => CellCert.CellFormula.presMode L.order n (headPotential x.2.2.2.2) p.1 p.2

def headData (L : CellCert.CellFormula.CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) : L.Datum → ℂ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) =>
      (L.presSegment i.2.1).moment true (headPressure L i.1 x) (L.pressureGradMode i.1 x 0) (L.pressureGradMode i.1 x 2) i.2.2
  | d => L.trueData x d

def headHarmonic (L : CellCert.CellFormula.CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : L.Datum → ℂ :=
  fun d => headData L (CellCalculus.cosTuple ν v G H Pg) d + Complex.I * headData L (CellCalculus.sinTuple ν v G H Pg) d

def keyValue (L : CellCert.CellFormula.CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) : CellCert.CellCoordinates.SkeletonKey → ℂ
  | CellCert.CellCoordinates.SkeletonKey.velocity n rad lev lo hi t a d =>
      (keySeg rad lev lo hi t).moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d
  | CellCert.CellCoordinates.SkeletonKey.gradient n rad lev lo hi t a d =>
      if rad then (keySeg rad lev lo hi t).moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
          (L.secondModeOf n x a 0 2) d
      else (keySeg rad lev lo hi t).moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0)
          (L.secondModeOf n x a 2 2) d
  | CellCert.CellCoordinates.SkeletonKey.pressure n rad lev lo hi t d =>
      (keySeg rad lev lo hi t).moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d
  | CellCert.CellCoordinates.SkeletonKey.corner n p a =>
      CellCert.CellFormula.cornerMoment p.1 (p.1 + 1) p.2 (p.2 + 1) (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
        (L.secondModeOf n x a 0 2)
  | CellCert.CellCoordinates.SkeletonKey.stream p =>
      CellCert.CellFormula.heightStripMoment p.2 (p.2 + 1) 0 p.1 (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)
  | CellCert.CellCoordinates.SkeletonKey.private_ => 0

def keyHarmonic (L : CellCert.CellFormula.CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (key : CellCert.CellCoordinates.SkeletonKey) : ℂ :=
  keyValue L (CellCalculus.cosTuple ν v G H Pg) key + Complex.I * keyValue L (CellCalculus.sinTuple ν v G H Pg) key

namespace TreeEntry

variable {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D} (T : TreeEntry D R)

def gaugeMatrix : Matrix (Fin T.gauge.count) (Fin T.gauge.count) ℂ :=
  fun e c => T.gauge.dir c (T.gauge.deletedKey e).1 (T.gauge.deletedKey e).2

def fieldGauge (c : Fin T.gauge.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : ℂ :=
  -∑ e, T.gauge.inverse c e *
    keyHarmonic T.keyLayout (labelTime (T.gauge.deletedKey e).1) v G H Pg (T.gauge.deletedKey e).2

def gaugeValue (c : Fin T.gauge.count) (q : Fin k → ℝ) (x : AdmissibleTuple D D.coercivity q) : ℂ :=
  T.fieldGauge c x.v x.G x.H (chosenPressure D x)

def fieldHead (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ) :
    CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → ℂ :=
  Sum.elim (Sum.elim (fun d => headHarmonic ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d.2)
    (fun _ => 0)) (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun _ => 0))

def fieldShifted (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ) :
    CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → ℂ :=
  fun i => fieldHead (R := R) K v G H Pg κ i + ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c i

def fieldKey (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ)
    (key : CellCert.CellCoordinates.SkeletonKey) : ℂ :=
  keyHarmonic T.keyLayout (labelTime ι) v G H Pg key + ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c ι key

def fieldData (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ) (a : T.Slaved) : ℝ :=
  match T.evalCell a, T.evalKappa a with
  | some ⟨K, d⟩, _ =>
      let z := T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
      if T.evalImag a then z.im else z.re
  | none, some i => κ i
  | none, none =>
      match T.skelKey a with
      | some (ι, key) =>
          let z := T.fieldKey v G H Pg ι key
          if T.evalImag a then z.im else z.re
      | none => 0

def headState {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) (K : Fin D.mesh.count) :
    CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → ℂ :=
  fieldHead (R := R) K x.v x.G x.H (chosenPressure D x) x.κ

def shiftedState {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) (K : Fin D.mesh.count) :
    CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → ℂ :=
  T.fieldShifted K x.v x.G x.H (chosenPressure D x) x.κ

def trueData {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) (a : T.Slaved) : ℝ :=
  T.fieldData x.v x.G x.H (chosenPressure D x) x.κ a

def certificate (front : T.Node → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ) (q : Fin k → ℝ) :
    Certificate.SignedStateCertificate (AdmissibleTuple D D.coercivity q) where
  Slaved := T.Slaved
  slavedFintype := T.slavedFintype
  Free := T.Free
  freeFintype := T.freeFintype
  basePoint := T.basePoint q
  data := T.trueData
  freeMap := T.freeMap
  tree := T.tree front

end TreeEntry

def TreeStateFromInitial (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) : Prop :=
  PressureRecovered D → InitialStateBound D R e → ∀ q ∈ D.cert.params,
    ∀ front : T.Node → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ,
    AdmissibleTuple.value D.coercivity (T.basePoint q) ≤ 0 ∧
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      Certificate.IsState (AdmissibleTuple.value D.coercivity) (T.basePoint q) T.trueData T.freeMap
        (T.tree front).totalForm)

theorem treeReduction_of_tree (hS : Certificate.StateEnclosureCertificateNonneg) (D : CellLayerData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (e : ℝ) (T : TreeEntry D R) (hT : TreeConditionsGiven D R T)
    (hst : TreeStateFromInitial D R e T) : TreeReduction D R e := by
  intro hPr hI q hq v G H g hv κ F hFm hFp hF2 hR hpos
  obtain ⟨front, hnode, hpiv⟩ := hT.node_conditions_given
  obtain ⟨hb, hs⟩ := hst hPr hI q hq front
  exact hS _ _ (T.certificate front q) ⟨hb, hs, hT.root_parent, hT.only_root, hnode, hpiv⟩
    ⟨v, G, H, g, κ, F, hv, hFm, hFp, hF2, hR, hpos⟩

structure CellJunctions (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) : Prop where
  off_modes : OffModesVanish D R
  exterior : ExteriorNonneg D
  pressure : PressureRecovered D
  cell_residual : ∀ K, CellCalculus.IsResidualFormBound D R K (R.cellForm K - CellCalculus.energyLeafForm D R K)
  tree_state : TreeStateFromInitial D R e T

theorem coefficientLowerBounds_of_entries (D : CellLayerData k C nE nM) (E : CoefficientEntry C nE nM)
    (hE : CoefficientConditions D E) (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    (hadm : ∃ epsSup epsGradSup ratio : ℝ, ∀ q ∈ D.cert.params,
      CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given
        D.givenHess D.cert.weight epsSup epsGradSup ratio) :
    CoefficientLowerBounds D D.coercivity := by
  obtain ⟨e₁, e₂, e₃, ha⟩ := hadm
  refine ⟨max E.floor E.resolvedFloor, fun q hq ι p hp => ?_⟩
  have hpq : ({ D.pieces q with c := D.coercivity } : PieceWeights C nE nM) = D.pieces q := by
    rw [← hc q hq]
  simp only [CellLayerData.withFormCoercivity, hpq]
  by_cases hres : ∃ K, p ∈ (D.mesh.box K).rect ∧ ι ∈ D.mesh.resolved K ∪ D.mesh.band K
  · obtain ⟨K, hpK, hιK⟩ := hres
    obtain ⟨v1, v2, v3, v4, v5⟩ := hE.resolved_valid q hq K ι hιK p hpK
    obtain ⟨f1, f2, f3, f4, f5⟩ := hE.resolved_floor K ι hιK p hpK
    have hm : -max E.floor E.resolvedFloor ≤ -E.resolvedFloor := neg_le_neg (le_max_right _ _)
    exact ⟨hm.trans (f1.trans v1), hm.trans (f2.trans v2), hm.trans (f3.trans v3), hm.trans (f4.trans v4),
      hm.trans (f5.trans (mul_le_mul_of_nonneg_left v5 (by positivity)))⟩
  · simp only [not_exists, not_and] at hres
    obtain ⟨j, hι, hpj⟩ := hE.covers ι p hp (fun K hK => by
      have h := hres K hK
      rw [Finset.mem_union, not_or] at h
      exact h)
    have hd := TailBand.uniformCoefficientBounds (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
      D.given D.givenHess D.cert.weight e₁ e₂ e₃ (ha q hq) (E.entry j) D.azimuthOrder (E.modes j) (E.region j)
      (hE.valid q hq j) ι hι p hpj
    obtain ⟨f1, f2, f3, f4, f5⟩ := hE.floor_bound q hq j p hpj
    have hm : -max E.floor E.resolvedFloor ≤ -E.floor := neg_le_neg (le_max_left _ _)
    obtain ⟨d1, d2, d3, d4, d5, -⟩ := hd
    simp only [TailBand.modeCoef, TailBand.PointCoef.ofMode] at d1 d2 d3 d4 d5
    exact ⟨hm.trans (f1.trans d1), hm.trans (f2.trans d2), hm.trans (f3.trans d3), hm.trans (f4.trans d4),
      hm.trans (f5.trans (mul_le_mul_of_nonneg_left d5 (by positivity)))⟩

structure LayerJunctionFacts (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) : Prop where
  shape_admissible : ∀ q ∈ D.cert.params,
    InstanceSplit.ShapeAdmissibleClauses (D.cert.period q) (D.bounds q) D.cert.weightFn D.given D.cert.weight
  shape_flip : ∀ q ∈ D.cert.params, InstanceSplit.ShapeFlipClauses (D.bounds q) D.cert.weightFn
  actuator_shape : ∀ i, Instance.ActuatorShapeFacts D.azimuthOrder (X.actuatorModes i) (D.cert.actuator i)
  flip_model : Bridge.IsFlipInvariantModel D.given D.givenHess
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B

theorem instanceConsequences_of_hypothesis (hI : Instance.InstanceParts) (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e)
    (hL : LayerJunctionFacts D X) : Instance.InstanceConsequences D :=
  Instance.instanceConsequences_of_entry hI D X h.instance_entry hL.actuator_shape

theorem admissible_of_hypothesis (hI : Instance.InstanceParts) (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X) :
    ∃ epsSup epsGradSup ratio : ℝ, ∀ q ∈ D.cert.params,
      CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given
        D.givenHess D.cert.weight epsSup epsGradSup ratio := by
  obtain ⟨e₁, e₂, e₃, he⟩ := h.continuum_conditions_given.enclosure_admissible
  exact ⟨e₁, e₂, e₃, fun q hq => Instance.isAdmissibleWeak_of_parts
    ((instanceConsequences_of_hypothesis hI D X R T e h hL).weights q hq).1
    (InstanceSplit.otherAdmissibleClauses_of_split (hL.shape_admissible q hq) (he q hq))⟩

theorem pairSharesBound_of_hypothesis (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hSupp : GivenShape.CompactFieldSupportRadius)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X) :
    ∃ ePair : ℝ, PairSharesBound D R ePair ∧ ∑ K, R.kappaCost K + ePair ≤ e := by
  obtain ⟨ep, hsur, hle⟩ := h.pair_surrogate
  refine ⟨∑ K, ep K, ?_, hle⟩
  intro q hq x ζ
  obtain ⟨F, J, Hs, -, hF⟩ := h.given_shape
  exact hPair D R X.actuatorModes X.actuatorRange ep (∑ K, ep K) h.mode_class h.instance_entry.actuators
    hL.actuator_shape (GivenShape.actuatorSupportInCells_of_shape hSupp D F Hs hF) h.instance_entry.pins hsur le_rfl
    q hq x.v x.G x.H x.g x.perturbation x.κ ζ

theorem creditLeavesBound_of_hypothesis (hCredit : CreditEval.CreditLeavesBoundHolds)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) : CreditLeavesBound D R := by
  intro q hq x Pg ζ η
  exact hCredit D R h.mesh_valid h.mode_class h.credit_evaluations q hq x.v x.G x.H x.g x.perturbation Pg x.κ ζ η

theorem halfPlaneFormBound_of_hypothesis (hI : Instance.InstanceParts) (hNeg : FormNegFiniteHolds) (hInit : InitialStateHolds)
    (hS : Certificate.StateEnclosureCertificateNonneg) (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hCredit : CreditEval.CreditLeavesBoundHolds)
    (hSupp : GivenShape.CompactFieldSupportRadius)
    (hCell : CellCalculus.CellFormAssemblyStatement) (hRow : RowSharesOfInstanceHolds)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e) (hL : LayerJunctionFacts D X) (hP : CellJunctions D R e T) :
    HalfPlaneFormBound D := by
  obtain ⟨B, hB⟩ := hL.model_state
  obtain ⟨E, hE⟩ := h.continuum_conditions_given.coefficients
  have hN : FormNegFinite D D.coercivity :=
    hNeg D _ B (by have := h.azimuth_ge; omega)
      (coefficientLowerBounds_of_entries D E hE h.box_uniform.c_eq (admissible_of_hypothesis hI D X R T e h hL)) hB
  obtain ⟨ePair, hpair, hle⟩ := pairSharesBound_of_hypothesis hPair hSupp D X R T e h hL
  refine halfPlaneFormBoundWith_of_value D _ _ hN
    (treeReduction_of_tree hS D R e T h.tree_conditions hP.tree_state hP.pressure ?_)
  exact hInit D R h.mesh_valid (by rw [h.pinWeight_eq]; norm_num) h.box_uniform.model_eq h.box_uniform.c_eq hN
    (hCell D R h.cell_conditions hP.cell_residual) hP.off_modes hP.exterior (hRow D X hI.class_form h.instance_entry h.mode_class)
    (creditLeavesBound_of_hypothesis hCredit D X R T e h) h.kappaCost_nonneg e ePair hpair hle

theorem rowRestClause_of_halfPlane (hPairing : ActuatorPairingHolds) (D : CellLayerData k C nE nM)
    (hid : DensityIdentity D)
    (hadm : ∃ epsSup epsGradSup ratio : ℝ, ∀ q ∈ D.cert.params,
      CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given
        D.givenHess D.cert.weight epsSup epsGradSup ratio)
    (hact : ∀ q ∈ D.cert.params, ∀ i, Instance.ActuatorFacts (D.pieces q) (D.cert.actuator i))
    (hmodel : ∀ q ∈ D.cert.params, D.cert.model q = D.given)
    (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    (hF : HalfPlaneFormBound D) :
    CoerciveWeak.RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight := by
  intro q hq v G H g hv κ F hFm hFp hF2 hR M hM
  obtain ⟨e₁, e₂, e₃, hadm'⟩ := hadm
  have hpq : ({ D.pieces q with c := D.coercivity } : PieceWeights C nE nM) = D.pieces q := by
    rw [← hc q hq]
  have hPos : (D.withFormCoercivity D.coercivity).formPos q v G H = D.formPos q v G H := by
    simp only [CellLayerData.formPos, CellLayerData.labelDensity, CellLayerData.withFormCoercivity,
      CellLayerData.stretchPosMean, hpq]
  have hNeg : (D.withFormCoercivity D.coercivity).formNeg q v G H = D.formNeg q v G H := by
    simp only [CellLayerData.formNeg, CellLayerData.labelDensity, CellLayerData.withFormCoercivity,
      CellLayerData.stretchNegMean, hpq]
  obtain ⟨hNf, hF'⟩ := hF q hq v G H g hv κ F hFm hFp hF2 hR
  rw [hPos, hNeg] at hF'
  rw [hNeg] at hNf
  obtain ⟨hidP, hidN⟩ := hid q hq v G H g hv
  have hpair : ∀ i, periodPairing (D.cert.actuator i) M = multiplierRight (D.pieces q) v G H (D.cert.actuator i) :=
    fun i => hPairing (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.cert.symmetries D.given
      D.givenHess (hadm' q hq) (D.cert.actuator i) (hact q hq i) v G H g hv M hM
  simp only [CellLayerData.modelHess, hmodel q hq, hidP, hidN, hpair]
  have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
  refine ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hNf, ?_⟩
  have key : ENNReal.ofReal (4 * Real.pi) * (ENNReal.ofReal (D.formScalarWith D.coercivity q v G H κ F / (4 * Real.pi))
      + D.formNeg q v G H) ≤ ENNReal.ofReal (4 * Real.pi) * (D.formPos q v G H
      + ENNReal.ofReal (-D.formScalarWith D.coercivity q v G H κ F / (4 * Real.pi))) := by
    gcongr
  rw [mul_add, mul_add, ← ENNReal.ofReal_mul h4.le, ← ENNReal.ofReal_mul h4.le,
    mul_div_cancel₀ _ h4.ne', mul_div_cancel₀ _ h4.ne'] at key
  unfold CellLayerData.formScalarWith at key
  exact key


theorem densityIdentity_of_hypothesis (hBridge : Bridge.ModeDensityBridgeHolds) (hI : Instance.InstanceParts)
    (hcb : ScalarShape.ChartBoundFacts)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e)
    (hL : LayerJunctionFacts D X) : DensityIdentity D := by
  obtain ⟨e₁, e₂, e₃, hm⟩ := admissible_of_hypothesis hI D X R T e h hL
  obtain ⟨D₀, hD₀⟩ := hL.model_state
  obtain ⟨B, hB⟩ := h.bound_valueSets
  intro q hq
  exact hBridge D D₀ h.mode_class hL.flip_model hD₀ (GivenShape.boundsMeasurable_of_entry hcb D B hB)
    (fun q hq => Instance.isFlipCompatible_of_parts
      ((instanceConsequences_of_hypothesis hI D X R T e h hL).weights q hq).2.1
        (InstanceSplit.otherFlipClauses_of_split (hL.shape_flip q hq) (h.continuum_conditions_given.values_flip q hq)))
    q hq ⟨e₁, e₂, e₃, hm q hq⟩

theorem layerJunctionFacts_of_hypothesis (hJ : GivenShape.JetParts) (hSc : GivenShape.ScaledJetParts)
    (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e) (hT : GivenShape.ShapeValuesFacts D) : LayerJunctionFacts D X := by
  obtain ⟨F, S, Hs, hSR, -⟩ := h.given_shape
  have hF := GivenShape.layerShapeFacts_of_scaled hJ hSc D X F S hSR
  exact ⟨GivenShape.shapeAdmissible_of_layer D X hF hT, GivenShape.shapeFlip_of_values D hT,
    hF.actuator_shape, hF.flip_model, hF.model_state⟩

theorem rowRestClause_of_cellHypothesis (hBridge : Bridge.ModeDensityBridgeHolds) (hPairing : ActuatorPairingHolds)
    (hNeg : FormNegFiniteHolds) (hInit : InitialStateHolds) (hS : Certificate.StateEnclosureCertificateNonneg)
    (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hCredit : CreditEval.CreditLeavesBoundHolds)
    (hSupp : GivenShape.CompactFieldSupportRadius) (hCell : CellCalculus.CellFormAssemblyStatement)
    (hRow : RowSharesOfInstanceHolds)
    (hI : Instance.InstanceParts) (hcb : ScalarShape.ChartBoundFacts) (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hJ : GivenShape.JetParts) (hSc : GivenShape.ScaledJetParts)
    (hT : GivenShape.ShapeValuesFacts D)
    (hP : CellJunctions D R e T) :
    CoerciveWeak.RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight := by
  have hL := layerJunctionFacts_of_hypothesis hJ hSc D X R T e h hT
  exact rowRestClause_of_halfPlane hPairing D (densityIdentity_of_hypothesis hBridge hI hcb D X R T e h hL)
    (admissible_of_hypothesis hI D X R T e h hL)
    (fun q hq i => (instanceConsequences_of_hypothesis hI D X R T e h hL).actuators q hq i) h.box_uniform.model_eq
    h.box_uniform.c_eq (halfPlaneFormBound_of_hypothesis hI hNeg hInit hS hPair hCredit hSupp hCell hRow D X R T e h hL hP)

theorem extendedCoerciveClause_of_cellLayer (hBridge : Bridge.ModeDensityBridgeHolds) (hPairing : ActuatorPairingHolds)
    (hNeg : FormNegFiniteHolds) (hInit : InitialStateHolds) (hS : Certificate.StateEnclosureCertificateNonneg)
    (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hCredit : CreditEval.CreditLeavesBoundHolds)
    (hSupp : GivenShape.CompactFieldSupportRadius) (hCell : CellCalculus.CellFormAssemblyStatement)
    (hRow : RowSharesOfInstanceHolds)
    (hI : Instance.InstanceParts) (hcb : ScalarShape.ChartBoundFacts) (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) (h : CellHypothesis D X R T e) (hJ : GivenShape.JetParts) (hSc : GivenShape.ScaledJetParts)
    (hT : GivenShape.ShapeValuesFacts D)
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
  have hL := layerJunctionFacts_of_hypothesis hJ hSc D X R T e h hT
  obtain ⟨B, hB⟩ := hL.model_state
  exact CoerciveWeak.extendedCoerciveClause_of_pieceData_proved hrad hwup hactm hactp hnorm D.modelHess (fun _ => B)
    (fun q hq => by rw [h.box_uniform.model_eq q hq]; exact hB)
    D.pieces D.bounds h.box_uniform.c_eq h.box_uniform.cμ_eq (by rw [h.pinWeight_eq]; norm_num) hm
    (rowRestClause_of_cellHypothesis hBridge hPairing hNeg hInit hS hPair hCredit hSupp hCell hRow hI hcb D X R T e h hJ hSc hT hP) hL2 hPin

end Statements

end CertCell

end Breakdown
