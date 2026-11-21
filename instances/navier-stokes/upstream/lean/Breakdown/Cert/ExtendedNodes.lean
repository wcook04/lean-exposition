import Breakdown.Cert.ExtendedStatement
import Breakdown.Cert.Nodes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

structure IsNormalExtendedCertificate {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  certificate : IsExtendedCertificate d
  unit_weight : d.multiplierWeight = 1
  model_eq : d.model = d.profile
  gap_zero : d.gapSize = 0
  shift_zero : d.formShift = 0

namespace ExtendedCertificateData

open Cert

open scoped Classical

variable {k : ℕ} (d : ExtendedCertificateData k)

def toCertificateData : CertificateData k where
  symmetries := d.symmetries
  center := 0
  radius := 0
  period := d.period
  profile := d.profile
  pressure := 0
  multiplier := d.multiplier
  target := d.target
  actuator := d.actuator
  pin := d.pin
  slope := 0
  slopeInverse := 0
  slopeOffset := 0
  defectBound := d.defectBound
  defectBallBound := 0
  weight := d.weight
  weightFn := d.weightFn
  weightMax := d.weightMax
  coerciveL2 := d.coerciveL2
  coerciveBall := 0
  coercivePin := d.coercivePin
  coerciveTotal := d.coerciveTotal
  ballRadius := 0
  decay := d.decay
  periodMax := d.periodMax
  twist := d.twist
  actuatorBound := d.actuatorBound
  formBound := d.formBound
  defectMax := d.defectMax
  sizeBound := d.sizeBound
  supBound := d.supBound

def defectH (q : Fin k → ℝ) : HH := physToHH (d.defect q)

def heldRight (q : Fin k → ℝ) (u : XX) : HH × (Fin k → ℝ) :=
  (-(d.defectH q) - productH u u, d.targetGap q)

def heldStep (q : Fin k → ℝ) (x : XX × (Fin k → ℝ)) : XX × (Fin k → ℝ) :=
  (freeInv (d.period q) (borderedInv d.toCertificateData q (d.heldRight q x.1)).1,
    (borderedInv d.toCertificateData q (d.heldRight q x.1)).2)

structure IsHeldSolution (q : Fin k → ℝ) (f : HH) (κ : Fin k → ℝ) : Prop where
  invariant : f ∈ invariantHH d.symmetries
  equation : f + convection d.toCertificateData q (freeInv (d.period q) f)
    + actuatorH d.toCertificateData κ
    + productH (freeInv (d.period q) f) (freeInv (d.period q) f) + d.defectH q = 0
  pins : pinMap d.toCertificateData (freeInv (d.period q) f) = d.targetGap q
  size : sizeZ d.weightFn (freeInv (d.period q) f) κ ≤ 2 * d.sizeBound
  sup : supGrad (freeInv (d.period q) f) ≤ ENNReal.ofReal d.supBound

def multiplierOf (q : Fin k → ℝ) : Fin k → ℝ :=
  d.multiplier q + (if h : ∃ κ, ∃ f, d.IsHeldSolution q f κ then h.choose else 0)

end ExtendedCertificateData

namespace Cert

def ExtendedUnitWeightHolds : Prop :=
  ∀ {k : ℕ} {d : ExtendedCertificateData k}, IsExtendedCertificate d →
    IsExtendedCertificate d.withUnitWeight

def ExtendedAtProfileHolds : Prop :=
  ∀ {k : ℕ} {d : ExtendedCertificateData k}, IsExtendedCertificate d →
    IsExtendedCertificate d.atProfile

def ExtendedNormalOrbitHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    d.multiplierWeight = 1 → d.model = d.profile → d.gapSize = 0 → d.formShift = 0 →
    WeakPeriodicSimilarityProfileExists

def RowNormHolds : Prop :=
  ∀ {m : ℕ} (e : Fin m → ℝ → Space → Space) (τ : Fin m → ℝ) (B : ℝ),
    (∀ a, IsPeriodicField (e a)) → (∀ a b, periodPairing (e a) (e b) = if a = b then 1 else 0) →
    (∀ a, 0 ≤ τ a) → (∀ a, τ a ≤ B ^ 2) → 0 ≤ B →
    ∀ F F', IsPeriodicField F → IsPeriodicField F' →
      rowNorm e τ (fun σ y => F σ y + F' σ y) ≤ rowNorm e τ F + rowNorm e τ F' ∧
      rowNorm e τ (fun σ y => -F σ y) = rowNorm e τ F ∧
      rowNorm e τ F ≤ B * periodNorm F

def ExtendedConvectionHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    (∃ T, ConvectionSpec d.toCertificateData q T) ∧
    (∃ M, ∀ u, ‖convection d.toCertificateData q u‖ ≤ M * ‖gradCLM u‖) ∧
    ∀ u v G H, IsReadingOf u v G H → ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (G z.1 z.2 (d.profile q z.1 z.2)
        + fderiv ℝ (d.profile q z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) =
        inner ℝ (convection d.toCertificateData q u) (testInHH φ)

def ExtendedInvarianceHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    (∀ u : XX, IsInvariantXX d.symmetries u →
      convection d.toCertificateData q u ∈ invariantHH d.symmetries ∧
      productH u u ∈ invariantHH d.symmetries) ∧
    (∀ κ, actuatorH d.toCertificateData κ ∈ invariantHH d.symmetries) ∧
    d.defectH q ∈ invariantHH d.symmetries

def ExtendedConvectionContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    ContinuousOn (fun q => convection d.toCertificateData q) d.params

def ExtendedDataHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    IsPeriodicField (d.defect q) ∧
    (∀ φ, IsSpaceTimeTestField φ → inner ℝ (d.defectH q) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)) ∧
    ‖d.defectH q‖ ≤ d.defectBound q ∧
    (∀ κ φ, IsSpaceTimeTestField φ → inner ℝ (actuatorH d.toCertificateData κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) ∧
    (∀ κ, ‖actuatorH d.toCertificateData κ‖ ≤ d.actuatorBound * vecNorm κ) ∧
    (∃ T, PinSpec d.toCertificateData T) ∧
    ∀ u v G H, IsReadingOf u v G H → ∀ i, pinMap d.toCertificateData u i = pinValue (d.pin i) G

def ExtendedDataContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    ContinuousOn d.targetGap d.params ∧
    ∀ φ, IsSpaceTimeTestField φ → ContinuousOn (fun q => inner ℝ (d.defectH q) (testInHH φ)) d.params

def ExtendedCoerciveBorderedHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    ∀ f ∈ invariantHH d.symmetries, ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space), IsPeriodicField F →
    (∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (bordered d.toCertificateData q (f, κ)).1 (testInHH φ)) →
    sizeZ d.weightFn (freeInv (d.period q) f) κ ≤
      d.coerciveL2 * periodNorm F + d.rows F
        + d.coercivePin * vecNorm (pinMap d.toCertificateData (freeInv (d.period q) f))

def ExtendedFrozenBridgeHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    ∀ f ∈ invariantHH d.symmetries, ∀ᵐ t : TimeCircle,
      -d.formBound * (‖secondPart (sliceOf (freeInv (d.period q) f) t)‖ ^ 2
        + sliceWeightedGrad d.weightFn (gradPart (sliceOf (freeInv (d.period q) f) t))) ≤
      ‖secondPart (sliceOf (freeInv (d.period q) f) t)‖ ^ 2
        + (1 / 4 : ℝ) * ‖gradPart (sliceOf (freeInv (d.period q) f) t)‖ ^ 2
        + inner ℝ (solField (sliceConvection (d.profile q (circleRep t))
            (gradPart (sliceOf (freeInv (d.period q) f) t))))
          (secondPart (sliceOf (freeInv (d.period q) f) t))

def ExtendedSupBoundHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    ∀ f ∈ invariantHH d.symmetries, ∀ κ : Fin k → ℝ,
    supGrad (freeInv (d.period q) f) < ⊤ ∧
    (supGrad (freeInv (d.period q) f)).toReal ^ 2 ≤
      (1 / d.weight + 2 * (d.period q / d.twist) * d.formBound)
          * energyW d.weightFn (freeInv (d.period q) f)
        + 2 * (d.period q / d.twist)
          * (‖(bordered d.toCertificateData q (f, κ)).1‖ + d.actuatorBound * vecNorm κ)
          * Real.sqrt (energyW d.weightFn (freeInv (d.period q) f))

def ExtendedConvectionCompactHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params,
    IsCompactOperator ((convection d.toCertificateData q).comp (freeInv (d.period q)))

def ExtendedBorderedInvertibleHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    (∃ T, BorderedInvSpec d.toCertificateData q T) ∧
    ∀ x y : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries → y.1 ∈ invariantHH d.symmetries →
      bordered d.toCertificateData q x = bordered d.toCertificateData q y → x = y

def ExtendedHeldMetricHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    IsClosed (heldSet d.toCertificateData) ∧
    (∃ c, 0 < c ∧ ∀ x ∈ heldSet d.toCertificateData, ∀ y ∈ heldSet d.toCertificateData,
      c * ‖x - y‖ ≤ heldDist d.toCertificateData x y) ∧
    (∀ x ∈ heldSet d.toCertificateData, ∀ y ∈ heldSet d.toCertificateData,
      ∀ z ∈ heldSet d.toCertificateData,
      heldDist d.toCertificateData x z ≤ heldDist d.toCertificateData x y
        + heldDist d.toCertificateData y z) ∧
    ∀ x ∈ heldSet d.toCertificateData, ∀ y ∈ heldSet d.toCertificateData,
      ∀ u : ℕ → XX × (Fin k → ℝ), (∀ n, u n ∈ heldSet d.toCertificateData) →
      Tendsto u atTop (𝓝 y) → ∀ ε : ℝ, (∀ᶠ n in atTop, heldDist d.toCertificateData x (u n) ≤ ε) →
        heldDist d.toCertificateData x y ≤ ε

def ExtendedHeldMapsToHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    Set.MapsTo (d.heldStep q) (heldSet d.toCertificateData) (heldSet d.toCertificateData)

def ExtendedHeldContractsHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    ∃ θ < 1, ∀ x ∈ heldSet d.toCertificateData, ∀ y ∈ heldSet d.toCertificateData,
      heldDist d.toCertificateData (d.heldStep q x) (d.heldStep q y) ≤
        θ * heldDist d.toCertificateData x y

def ExtendedHeldExistsUniqueHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    ∃ f κ, d.IsHeldSolution q f κ ∧ ∀ f' κ', d.IsHeldSolution q f' κ' → f' = f ∧ κ' = κ

def ExtendedHeldLimitHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ),
    (∀ n, p n ∈ d.params) → q ∈ d.params → Tendsto p atTop (𝓝 q) →
    ∀ (f : ℕ → HH) (κ : ℕ → Fin k → ℝ), (∀ n, d.IsHeldSolution (p n) (f n) (κ n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ κ₀, d.IsHeldSolution q f₀ κ₀ ∧
      Tendsto (fun n => κ (φ n)) atTop (𝓝 κ₀)

def ExtendedMultiplierContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d →
    ContinuousOn d.multiplierOf d.params

def ExtendedAdjointPairingHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, IsPeriodicField (d.adjoint j q) ∧
      ∀ F, IsPeriodicField F →
        periodPairing F (d.adjoint j q) = inner ℝ (physToHH F) (physToHH (d.adjoint j q))

def ExtendedAdjointEnclosureHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    ∀ f κ, d.IsHeldSolution q f κ → ∀ j ∈ d.adjointSet,
      |∑ l, d.frame l j * κ l + periodPairing (d.defect q) (d.adjoint j q)
        + ∑ l, d.coupling q j l * d.targetGap q l| ≤
        d.adjointQuad j * (2 * d.sizeBound) ^ 2 + 2 * d.sizeBound * Real.sqrt (d.adjointDefect j ^ 2
          + (vecNorm (d.actuatorAdjointError q j) / d.multiplierWeight) ^ 2)

def ExtendedStiffEnclosureHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d → ∀ q ∈ d.params,
    ∀ f κ, d.IsHeldSolution q f κ →
      Real.sqrt (∑ j ∈ d.adjointSetᶜ, (∑ i, d.frame i j * κ i) ^ 2) ≤
        2 * d.sizeBound * d.stiffNorm / d.multiplierWeight

def ExtendedExistsZeroHeldHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsNormalExtendedCertificate d →
    ∃ q ∈ d.params, ∃ f κ, d.IsHeldSolution q f κ ∧ d.multiplier q + κ = 0

def ExtendedHeldWeakEquationHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params, ∀ f κ,
    d.IsHeldSolution q f κ → d.multiplier q + κ = 0 →
    ∀ v G H, IsReadingOf (freeInv (d.period q) f) v G H → ∀ φ, IsSpaceTimeTestField φ →
      Integrable (sigmaSimilarityIntegrand (d.period q) (fun σ y => d.profile q σ y + v σ y)
        (fun σ y => fderiv ℝ (d.profile q σ) y + G σ y) φ) ∧
      ∫ z, sigmaSimilarityIntegrand (d.period q) (fun σ y => d.profile q σ y + v σ y)
        (fun σ y => fderiv ℝ (d.profile q σ) y + G σ y) φ z = 0

def ExtendedHeldNonzeroHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params, ∀ f κ,
    d.IsHeldSolution q f κ → ∀ v G H, IsReadingOf (freeInv (d.period q) f) v G H →
      ¬ (∀ᵐ z : ℝ × Space, d.profile q z.1 z.2 + v z.1 z.2 = 0)

def ExtendedSigmaProfileOfHeldHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d → ∀ q ∈ d.params, ∀ f κ,
    d.IsHeldSolution q f κ → d.multiplier q + κ = 0 → ∃ P W G H C, IsSigmaProfile P W G H C

end Cert

end Breakdown
