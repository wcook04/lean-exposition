import Breakdown.Cert.Basic
import Breakdown.Cert.StConclusion

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

def IsPeriodicField (F : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume ∧ IsTimePeriodic F ∧
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤

def IsAdmissibleWeight (w : Space → ℝ) (w₀ : ℝ) : Prop :=
  0 < w₀ ∧ Measurable w ∧ (∀ y, w₀ ≤ w y) ∧ ∃ C, ∀ y, w y ≤ C

def IsInvariantXX (Γ : Set Symmetry) (u : XX) : Prop := gradCLM u ∈ invariantHH Γ

def sliceOf (u : XX) (t : TimeCircle) : XBar := (u : TimeCircle → XBar) t

def gradColumn (G : GradField) (j : Fin 3) : ℝ → Space → Space := fun σ y => G σ y (unitVector j)

def ProjectionHolds : Prop :=
  (∃ T, ProjSpec T) ∧ (∀ F, ‖solProj F‖ ≤ ‖F‖) ∧
    (∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x)) ∧
    ∀ x : HBar, solProj (toPhysH x) = x

def TestPairingHolds : Prop :=
  ∀ F, IsPeriodicField F → ∀ φ, IsSpaceTimeTestField φ →
    inner ℝ (physToHH F) (testInHH φ) = ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2)

def GraphClosedHolds : Prop := ∀ q : XBar, IsHalfSspOf (gradPart q) (secondPart q)

def ReadingExistsHolds : Prop :=
  ∀ u : XX, ∃ v G H, IsReadingOf u v G H ∧
    periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) ≤ ENNReal.ofReal (‖secondCLM u‖ ^ 2)

def ReadingEnergyHolds : Prop :=
  ∀ (w : Space → ℝ) (w₀ : ℝ), IsAdmissibleWeight w w₀ → ∀ u v G H, IsReadingOf u v G H →
    weightedEnergy w G H = energyW w u ∧
    (periodLIntegral (fun σ y => matSq (G σ y))).toReal = ‖gradCLM u‖ ^ 2 ∧
    ∀ χ : ℝ → Space → (Space →L[ℝ] Space),
      AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) volume → IsTimePeriodic χ →
      periodLIntegral (fun σ y => matSq (χ σ y)) < ⊤ →
      pinValue χ G = ∫ t, pinSlice (χ (circleRep t)) (gradPart (sliceOf u t))

def PropagatorBoundHolds : Prop :=
  (∀ τ, 0 < τ → ∀ x : HBar, ‖slicePropagator τ x‖ ≤
    Real.exp (-(τ / 4)) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ)) * ‖x‖) ∧
  ∀ x : HBar, ContinuousOn (fun τ => slicePropagator τ x) (Set.Ioi 0)

def GradInvHolds : Prop :=
  ∀ P, 0 < P → (∀ f : HH, IntegrableOn (propagatorIntegrand P f) (Set.Ioi 0)) ∧
    ∃ T, GradInvSpec P T

def FreeInvHolds : Prop :=
  ∀ P, 0 < P → (∃ T, FreeInvSpec P T) ∧ ∀ f : HH,
    ‖secondCLM (freeInv P f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (freeInv P f)‖ ^ 2 ≤ ‖f‖ ^ 2

def FreeEnergyLocalHolds : Prop :=
  ∀ P, 0 < P → ∀ f : HH, ∃ y : ℝ → ℝ, Continuous y ∧ (∀ σ, y (σ + 1) = y σ) ∧
    (∀ᵐ σ : ℝ, y σ = ‖gradPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2) ∧
    ∀ a b, a ≤ b → (1 / (2 * P)) * (y b - y a) =
      ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * y σ)

def FreeEquivariantHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ), 0 < P → ∀ f ∈ invariantHH Γ, IsInvariantXX Γ (freeInv P f)

def FreePerturbationHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ), 0 < P → ∀ f ∈ invariantHH Γ, ∀ v G H,
    IsReadingOf (freeInv P f) v G H →
    ∃ g, IsPerturbation Γ P v G H g ∧ ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ)

def PeriodContinuityHolds : Prop :=
  ∀ (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH), 0 < P₀ → (∀ n, 0 < P n) →
    Tendsto P atTop (𝓝 P₀) → (∃ C, ∀ n, ‖f n‖ ≤ C) →
    (∀ y : HH, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) →
    ∀ y : XX, Tendsto (fun n => inner ℝ (freeInv (P n) (f n)) y) atTop
      (𝓝 (inner ℝ (freeInv P₀ f₀) y))

def SliceSupBoundHolds : Prop :=
  ∀ q : XBar, ∀ᵐ y, ‖(velocity (gradPart q) : Space → Space) y‖ ^ 2 ≤
    (1 / (2 * Real.pi)) * ‖gradPart q‖ * ‖secondPart q‖

def SliceReadingHolds : Prop :=
  ∀ P, 0 < P → ∀ f : HH, ∃ v G H, IsReadingOf (freeInv P f) v G H ∧
    (∀ σ, IsWeakGradient (v σ) (G σ)) ∧ (∀ σ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0) ∧
    (∃ B, ∀ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) ≤ ENNReal.ofReal B ∧
      ∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2) ≤ ENNReal.ofReal B) ∧
    periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) < ⊤

def ProductBoundHolds : Prop :=
  ∀ (w : Space → ℝ) (w₀ : ℝ), IsAdmissibleWeight w w₀ → ∀ u u' : XX, supGrad u' < ⊤ →
    IsPeriodicField (productField u u') ∧
    periodNorm (productField u u') ≤ supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad u').toReal ∧
    ‖productH u u'‖ ≤ supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad u').toReal

def ProductPairingHolds : Prop :=
  ∀ u u' : XX, supGrad u' < ⊤ → ∀ φ, IsSpaceTimeTestField φ →
    inner ℝ (productH u u') (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (productField u u' z.1 z.2) (φ z.1 z.2)

def ProductSubHolds : Prop :=
  ∀ u u' : XX, supGrad u < ⊤ → supGrad u' < ⊤ →
    productH u u - productH u' u' = productH (u - u') u + productH u' (u - u') ∧
    ∀ᵐ z : ℝ × Space, productField u u z.1 z.2 - productField u' u' z.1 z.2 =
      productField (u - u') u z.1 z.2 + productField u' (u - u') z.1 z.2

def ConvectionHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    (∃ T, ConvectionSpec d p T) ∧ (∃ M, ∀ u, ‖convection d p u‖ ≤ M * ‖gradCLM u‖) ∧
    ∀ u v G H, IsReadingOf u v G H → ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) =
        inner ℝ (convection d p u) (testInHH φ)

def InvarianceHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    (∀ u : XX, IsInvariantXX d.symmetries u → convection d p u ∈ invariantHH d.symmetries ∧
      productH u u ∈ invariantHH d.symmetries) ∧
    (∀ κ, actuatorH d κ ∈ invariantHH d.symmetries) ∧ defectH d p ∈ invariantHH d.symmetries

def ConvectionContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ContinuousOn (fun p => convection d p) d.box

def DataHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    (∀ φ, IsSpaceTimeTestField φ → inner ℝ (defectH d p) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
        (d.multiplier p) z.1 z.2) (φ z.1 z.2)) ∧
    ‖defectH d p‖ ≤ d.defectBound p ∧
    (∀ κ φ, IsSpaceTimeTestField φ → inner ℝ (actuatorH d κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) ∧
    (∀ κ, ‖actuatorH d κ‖ ≤ d.actuatorBound * vecNorm κ) ∧
    (∃ T, PinSpec d T) ∧
    ∀ u v G H, IsReadingOf u v G H → ∀ i, pinMap d u i = pinValue (d.pin i) G

def DataContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ContinuousOn (targetGap d) d.box ∧
    ∀ φ, IsSpaceTimeTestField φ → ContinuousOn (fun p => inner ℝ (defectH d p) (testInHH φ)) d.box

def CoerciveBorderedHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    ∀ f ∈ invariantHH d.symmetries, ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space), IsPeriodicField F →
    (∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (bordered d p (f, κ)).1 (testInHH φ)) →
    sizeZ d.weightFn (freeInv (d.period p) f) κ ≤
      d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F
        + d.coercivePin * vecNorm (pinMap d (freeInv (d.period p) f))

def FrozenBridgeHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    ∀ f ∈ invariantHH d.symmetries, ∀ᵐ t : TimeCircle,
      -d.formBound * (‖secondPart (sliceOf (freeInv (d.period p) f) t)‖ ^ 2
        + sliceWeightedGrad d.weightFn (gradPart (sliceOf (freeInv (d.period p) f) t))) ≤
      ‖secondPart (sliceOf (freeInv (d.period p) f) t)‖ ^ 2
        + (1 / 4 : ℝ) * ‖gradPart (sliceOf (freeInv (d.period p) f) t)‖ ^ 2
        + inner ℝ (solField (sliceConvection (d.profile p (circleRep t))
            (gradPart (sliceOf (freeInv (d.period p) f) t))))
          (secondPart (sliceOf (freeInv (d.period p) f) t))

def SupBoundHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    ∀ f ∈ invariantHH d.symmetries, ∀ κ : Fin k → ℝ,
    supGrad (freeInv (d.period p) f) < ⊤ ∧
    (supGrad (freeInv (d.period p) f)).toReal ^ 2 ≤
      (1 / d.weight + 2 * (d.period p / d.twist) * d.formBound)
          * energyW d.weightFn (freeInv (d.period p) f)
        + 2 * (d.period p / d.twist) * (‖(bordered d p (f, κ)).1‖ + d.actuatorBound * vecNorm κ)
          * Real.sqrt (energyW d.weightFn (freeInv (d.period p) f))

def TimeModulusHolds : Prop :=
  ∀ a b R : ℝ, 0 < a → 0 < R → ∃ rate : ℝ → ℝ, Tendsto rate (𝓝[>] 0) (𝓝 0) ∧
    ∀ P ∈ Set.Icc a b, ∀ f : HH, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      periodBallNorm R (fun σ y => (readingOf (freeInv P f)).1 (σ + δ) y
        - (readingOf (freeInv P f)).1 σ y) ≤ rate δ * ‖f‖ ∧
      ∀ j, periodBallNorm R (fun σ y => gradColumn (readingOf (freeInv P f)).2.1 j (σ + δ) y
        - gradColumn (readingOf (freeInv P f)).2.1 j σ y) ≤ rate δ * ‖f‖

def SpaceModulusHolds : Prop :=
  ∀ R : ℝ, 0 < R → ∀ (u : XX) (h : Space),
    periodBallNorm R (fun σ y => (readingOf u).1 σ (y + h) - (readingOf u).1 σ y) ≤
      ‖h‖ * ‖gradCLM u‖ ∧
    ∀ j, periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ (y + h)
      - gradColumn (readingOf u).2.1 j σ y) ≤ ‖h‖ * ‖secondCLM u‖

def TranslationCriterionHolds : Prop :=
  ∀ (F : ℕ → ℝ → Space → Space) (R C : ℝ) (rate : ℝ → ℝ), 0 < R → Tendsto rate (𝓝[>] 0) (𝓝 0) →
    (∀ n, AEStronglyMeasurable (fun z : ℝ × Space => F n z.1 z.2) volume) →
    (∀ n, IsTimePeriodic (F n)) →
    (∀ n, periodBallLIntegral (R + 1) (fun σ y => ‖F n σ y‖ ^ 2) ≤ ENNReal.ofReal C) →
    (∀ n, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      periodBallNorm R (fun σ y => F n (σ + δ) y - F n σ y) ≤ rate δ) →
    (∀ n, ∀ h : Space, 0 < ‖h‖ → ‖h‖ ≤ 1 →
      periodBallNorm R (fun σ y => F n σ (y + h) - F n σ y) ≤ rate ‖h‖) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      periodBallNorm R (fun σ y => F (φ m) σ y - F (φ n) σ y) < ε

def LocalCompactnessHolds : Prop :=
  ∀ a b : ℝ, 0 < a → ∀ (P : ℕ → ℝ) (f : ℕ → HH), (∀ n, P n ∈ Set.Icc a b) →
    (∃ C, ∀ n, ‖f n‖ ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ R > 0, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      periodBallNorm R (fun σ y => (readingOf (freeInv (P (φ m)) (f (φ m)))).1 σ y
        - (readingOf (freeInv (P (φ n)) (f (φ n)))).1 σ y) < ε ∧
      ∀ j, periodBallNorm R (fun σ y => gradColumn (readingOf (freeInv (P (φ m)) (f (φ m)))).2.1 j σ y
        - gradColumn (readingOf (freeInv (P (φ n)) (f (φ n)))).2.1 j σ y) < ε

def ConvectionCompactHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    IsCompactOperator ((convection d p).comp (freeInv (d.period p)))

def BorderedInvertibleHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    (∃ T, BorderedInvSpec d p T) ∧
    ∀ x y : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries → y.1 ∈ invariantHH d.symmetries →
      bordered d p x = bordered d p y → x = y

def ContractionFixedPointHolds : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [CompleteSpace E] (S : Set E) (D : E → E → ℝ) (Ξ : E → E)
    (c θ : ℝ), IsClosed S → S.Nonempty → Set.MapsTo Ξ S S → 0 < c → θ < 1 →
    (∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ D x y) →
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, D x z ≤ D x y + D y z) →
    (∀ x ∈ S, ∀ y ∈ S, ∀ u : ℕ → E, (∀ n, u n ∈ S) → Tendsto u atTop (𝓝 y) → ∀ ε : ℝ,
      (∀ᶠ n in atTop, D x (u n) ≤ ε) → D x y ≤ ε) →
    (∀ x ∈ S, ∀ y ∈ S, D (Ξ x) (Ξ y) ≤ θ * D x y) →
    ∃ x ∈ S, Ξ x = x ∧ ∀ y ∈ S, Ξ y = y → y = x

def HeldMetricHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → IsClosed (heldSet d) ∧
    (∃ c, 0 < c ∧ ∀ x ∈ heldSet d, ∀ y ∈ heldSet d, c * ‖x - y‖ ≤ heldDist d x y) ∧
    (∀ x ∈ heldSet d, ∀ y ∈ heldSet d, ∀ z ∈ heldSet d,
      heldDist d x z ≤ heldDist d x y + heldDist d y z) ∧
    ∀ x ∈ heldSet d, ∀ y ∈ heldSet d, ∀ u : ℕ → XX × (Fin k → ℝ), (∀ n, u n ∈ heldSet d) →
      Tendsto u atTop (𝓝 y) → ∀ ε : ℝ, (∀ᶠ n in atTop, heldDist d x (u n) ≤ ε) → heldDist d x y ≤ ε

def HeldMapsToHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box,
    Set.MapsTo (heldStep d p) (heldSet d) (heldSet d)

def HeldContractsHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box, ∃ θ < 1,
    ∀ x ∈ heldSet d, ∀ y ∈ heldSet d, heldDist d (heldStep d p x) (heldStep d p y) ≤ θ * heldDist d x y

def HeldExistsUniqueHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box, ∃ f κ,
    IsHeldSolution d p f κ ∧ ∀ f' κ', IsHeldSolution d p f' κ' → f' = f ∧ κ' = κ

def HeldLimitHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ),
    (∀ n, p n ∈ d.box) → q ∈ d.box → Tendsto p atTop (𝓝 q) →
    ∀ (f : ℕ → HH) (κ : ℕ → Fin k → ℝ), (∀ n, IsHeldSolution d (p n) (f n) (κ n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ κ₀, IsHeldSolution d q f₀ κ₀ ∧
      Tendsto (fun n => κ (φ n)) atTop (𝓝 κ₀)

def MultiplierContinuityHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ContinuousOn (multiplierOf d) d.box

def ExistsZeroHeldHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d →
    ∃ p ∈ d.box, ∃ f κ, IsHeldSolution d p f κ ∧ d.multiplier p + κ = 0

def HeldWeakEquationHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box, ∀ f κ,
    IsHeldSolution d p f κ → d.multiplier p + κ = 0 →
    ∀ v G H, IsReadingOf (freeInv (d.period p) f) v G H → ∀ φ, IsSpaceTimeTestField φ →
      Integrable (sigmaSimilarityIntegrand (d.period p) (fun σ y => d.profile p σ y + v σ y)
        (fun σ y => fderiv ℝ (d.profile p σ) y + G σ y) φ) ∧
      ∫ z, sigmaSimilarityIntegrand (d.period p) (fun σ y => d.profile p σ y + v σ y)
        (fun σ y => fderiv ℝ (d.profile p σ) y + G σ y) φ z = 0

def HeldNonzeroHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box, ∀ f κ,
    IsHeldSolution d p f κ → ∀ v G H, IsReadingOf (freeInv (d.period p) f) v G H →
      ¬ (∀ᵐ z : ℝ × Space, d.profile p z.1 z.2 + v z.1 z.2 = 0)

def SigmaProfileOfHeldHolds : Prop :=
  ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → ∀ p ∈ d.box, ∀ f κ,
    IsHeldSolution d p f κ → d.multiplier p + κ = 0 → ∃ P W G H C, IsSigmaProfile P W G H C

def TestDenseHolds : Prop :=
  ∀ f : HH, (∀ φ, IsSpaceTimeTestField φ → inner ℝ f (testInHH φ) = 0) → f = 0

end Breakdown.Cert
