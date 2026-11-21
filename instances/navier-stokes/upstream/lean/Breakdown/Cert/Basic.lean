import Breakdown.Cert.Statement
import Breakdown.FreqTr.Basic

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown.Cert

open Freq

open scoped Classical

instance factZeroLtOneReal : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

abbrev TimeCircle := AddCircle (1 : ℝ)

def circleRep (t : TimeCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 t).1

def onCircle {β : Type*} (f : ℝ → β) : TimeCircle → β := fun t => f (circleRep t)

def circleLpOrZero {E : Type*} [NormedAddCommGroup E] (f : TimeCircle → E) :
    Lp (α := TimeCircle) E 2 :=
  if h : MemLp f 2 volume then h.toLp f else 0

abbrev HBar := Freq.X

def halfOrderGraph : Submodule ℝ (WithLp 2 (Freq.X × Freq.X)) :=
  (Submodule.span ℝ {q | IsHalfSspOf (WithLp.fst q) (WithLp.snd q)}).topologicalClosure

instance : CompleteSpace halfOrderGraph :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

abbrev XBar := ↥halfOrderGraph

def gradPart : XBar →L[ℝ] Freq.X := (WithLp.fstL 2 ℝ Freq.X Freq.X).comp halfOrderGraph.subtypeL

def secondPart : XBar →L[ℝ] HBar := (WithLp.sndL 2 ℝ Freq.X Freq.X).comp halfOrderGraph.subtypeL

abbrev HH := Lp (α := TimeCircle) HBar 2

abbrev XX := Lp (α := TimeCircle) XBar 2

def gradCLM : XX →L[ℝ] HH := ContinuousLinearMap.compLpL 2 volume gradPart

def secondCLM : XX →L[ℝ] HH := ContinuousLinearMap.compLpL 2 volume secondPart

def sliceWeightedGrad (w : Space → ℝ) (h : Freq.X) : ℝ :=
  ∫ y, w y * ∑ j : Fin 3, ‖(partialX j h : Space → Space) y‖ ^ 2

def energyW (w : Space → ℝ) (u : XX) : ℝ :=
  ‖secondCLM u‖ ^ 2 + ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))

def sizeZ {k : ℕ} (w : Space → ℝ) (u : XX) (κ : Fin k → ℝ) : ℝ :=
  Real.sqrt (energyW w u + ∑ i, κ i ^ 2)

def supGrad (u : XX) : ℝ≥0∞ := eLpNorm (fun t => gradPart ((u : TimeCircle → XBar) t)) ⊤ volume

def toPhysH : HBar →L[ℝ] L2R := toPhys ∘L Sig.subtypeL

def solenoidalSymbol (ξ : Space) : CSpace →L[ℝ] CSpace :=
  ContinuousLinearMap.id ℝ CSpace - longitudinal ξ

def ProjSpec (T : L2R →L[ℝ] HBar) : Prop :=
  ∀ F, ((T F : HBar) : L2C) = fieldOp id solenoidalSymbol (freqTrR (complexify F))

def solProj : L2R →L[ℝ] HBar := if h : ∃ T, ProjSpec T then h.choose else 0

def solField (F : Space → Space) : HBar := solProj (toLpOrZero 2 F)

def physToHH (F : ℝ → Space → Space) : HH := circleLpOrZero (onCircle fun σ => solField (F σ))

def periodize (φ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := ∑' n : ℤ, φ (σ + n) y

def testInHH (φ : ℝ → Space → Space) : HH := physToHH (periodize φ)

def smoothH (t : ℝ) : HBar →L[ℝ] Freq.X :=
  restrictX (fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace))

def slicePropagator (τ : ℝ) : HBar →L[ℝ] Freq.X :=
  (dilX (Real.exp (-τ))).comp (smoothH (1 - Real.exp (-τ)))

def shiftLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) :
    Lp (α := TimeCircle) E 2 →L[ℝ] Lp (α := TimeCircle) E 2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
    (measurePreserving_add_right volume (a : TimeCircle))).toContinuousLinearMap

def propagatorIntegrand (P : ℝ) (f : HH) (τ : ℝ) : HH :=
  ContinuousLinearMap.compLpL 2 volume (slicePropagator τ) (shiftLp (-(τ / P)) f)

def GradInvSpec (P : ℝ) (T : HH →L[ℝ] HH) : Prop :=
  ∀ f, T f = ∫ τ in Set.Ioi (0 : ℝ), propagatorIntegrand P f τ

def gradInv (P : ℝ) : HH →L[ℝ] HH := if h : ∃ T, GradInvSpec P T then h.choose else 0

def FreeInvSpec (P : ℝ) (T : HH →L[ℝ] XX) : Prop := ∀ f, gradCLM (T f) = gradInv P f

def freeInv (P : ℝ) : HH →L[ℝ] XX := if h : ∃ T, FreeInvSpec P T then h.choose else 0

def sliceConvection (W : Space → Space) (h : Freq.X) : Space → Space := fun y =>
  ∑ j : Fin 3, (W y) j • (partialX j h : Space → Space) y + fderiv ℝ W y ((velocity h : Space → Space) y)

def ConvectionSpec {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (T : XX →L[ℝ] HH) : Prop :=
  ∀ u : XX, ((T u : HH) : TimeCircle → HBar) =ᵐ[volume]
    fun t => solField (sliceConvection (d.profile p (circleRep t)) (gradPart ((u : TimeCircle → XBar) t)))

def convection {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) : XX →L[ℝ] HH :=
  if h : ∃ T, ConvectionSpec d p T then h.choose else 0

def actuatorSlice {k : ℕ} (d : CertificateData k) (i : Fin k) : HH := physToHH (d.actuator i)

def actuatorH {k : ℕ} (d : CertificateData k) : (Fin k → ℝ) →L[ℝ] HH :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (actuatorSlice d i)

def pinSlice (χ : Space → (Space →L[ℝ] Space)) (h : Freq.X) : ℝ :=
  ∫ y, ∑ j : Fin 3, inner ℝ ((partialX j h : Space → Space) y) (χ y (unitVector j))

def PinSpec {k : ℕ} (d : CertificateData k) (T : XX →L[ℝ] (Fin k → ℝ)) : Prop :=
  ∀ u i, T u i = ∫ t, pinSlice (d.pin i (circleRep t)) (gradPart ((u : TimeCircle → XBar) t))

def pinMap {k : ℕ} (d : CertificateData k) : XX →L[ℝ] (Fin k → ℝ) :=
  if h : ∃ T, PinSpec d T then h.choose else 0

def productSlice (h h' : Freq.X) : Space → Space := fun y =>
  ∑ j : Fin 3, ((velocity h : Space → Space) y) j • (partialX j h' : Space → Space) y

def productH (u w : XX) : HH :=
  circleLpOrZero fun t => solField (productSlice (gradPart ((u : TimeCircle → XBar) t))
    (gradPart ((w : TimeCircle → XBar) t)))

def defectH {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) : HH :=
  physToHH (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator (d.multiplier p))

def targetGap {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) : Fin k → ℝ :=
  fun i => d.target p i - pinValue (d.pin i) (fun σ y => fderiv ℝ (d.profile p σ) y)

abbrev VelField := ℝ → Space → Space

abbrev GradField := ℝ → Space → (Space →L[ℝ] Space)

abbrev SecondField := ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)

structure IsReadingOf (u : XX) (v : VelField) (G : GradField) (H : SecondField) : Prop where
  measurable_velocity : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume
  measurable_gradient : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume
  measurable_second : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume
  periodic_velocity : IsTimePeriodic v
  periodic_gradient : IsTimePeriodic G
  periodic_second : IsTimePeriodic H
  velocity_eq : ∀ᵐ σ : ℝ, v σ =ᵐ[volume]
    (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)
  weak_gradient : ∀ᵐ σ : ℝ, IsWeakGradient (v σ) (G σ)
  weak_second : ∀ᵐ σ : ℝ, ∀ j : Fin 3,
    IsWeakGradient (fun y => G σ y (unitVector j)) (fun y => (H σ y).flip (unitVector j))
  trace_eq : ∀ᵐ σ : ℝ, (fun y => secondDerivTrace (H σ y)) =ᵐ[volume]
    fun y => -(toPhysH (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y

def readingOf (u : XX) : VelField × GradField × SecondField :=
  if h : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 then h.choose
  else (0, 0, 0)

def productField (u w : XX) : ℝ → Space → Space :=
  fun σ y => (readingOf w).2.1 σ y ((readingOf u).1 σ y)

def rotHH (R : Space ≃ₗᵢ[ℝ] Space) : HH →L[ℝ] HH :=
  ContinuousLinearMap.compLpL 2 volume ((rotX R).toContinuousLinearEquiv : Freq.X →L[ℝ] Freq.X)

def invariantHH (Γ : Set Symmetry) : Submodule ℝ HH :=
  ⨅ γ ∈ Γ, LinearMap.ker (((shiftLp γ.2 : HH →L[ℝ] HH) - rotHH γ.1 : HH →L[ℝ] HH) : HH →ₗ[ℝ] HH)

def bordered {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) :
    (HH × (Fin k → ℝ)) →L[ℝ] (HH × (Fin k → ℝ)) :=
  ((ContinuousLinearMap.fst ℝ HH (Fin k → ℝ))
      + (convection d p).comp ((freeInv (d.period p)).comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ)))
      + (actuatorH d).comp (ContinuousLinearMap.snd ℝ HH (Fin k → ℝ))).prod
    ((pinMap d).comp ((freeInv (d.period p)).comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ))))

def BorderedInvSpec {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ)
    (T : (HH × (Fin k → ℝ)) →L[ℝ] (HH × (Fin k → ℝ))) : Prop :=
  ∀ y : HH × (Fin k → ℝ), y.1 ∈ invariantHH d.symmetries →
    (T y).1 ∈ invariantHH d.symmetries ∧ bordered d p (T y) = y

def borderedInv {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) :
    (HH × (Fin k → ℝ)) →L[ℝ] (HH × (Fin k → ℝ)) :=
  if h : ∃ T, BorderedInvSpec d p T then h.choose else 0

def heldRight {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) : HH × (Fin k → ℝ) :=
  (-(defectH d p) - productH u u, targetGap d p)

def heldStep {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (x : XX × (Fin k → ℝ)) :
    XX × (Fin k → ℝ) :=
  (freeInv (d.period p) (borderedInv d p (heldRight d p x.1)).1, (borderedInv d p (heldRight d p x.1)).2)

def heldSet {k : ℕ} (d : CertificateData k) : Set (XX × (Fin k → ℝ)) :=
  {x | gradCLM x.1 ∈ invariantHH d.symmetries ∧ sizeZ d.weightFn x.1 x.2 ≤ 2 * d.sizeBound ∧ supGrad x.1 ≤ ENNReal.ofReal d.supBound}

def heldDist {k : ℕ} (d : CertificateData k) (x y : XX × (Fin k → ℝ)) : ℝ :=
  max (sizeZ d.weightFn (x.1 - y.1) (x.2 - y.2))
    (2 * d.sizeBound / d.supBound * (supGrad (x.1 - y.1)).toReal)

structure IsHeldSolution {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (f : HH)
    (κ : Fin k → ℝ) : Prop where
  invariant : f ∈ invariantHH d.symmetries
  equation : f + convection d p (freeInv (d.period p) f) + actuatorH d κ
    + productH (freeInv (d.period p) f) (freeInv (d.period p) f) + defectH d p = 0
  pins : pinMap d (freeInv (d.period p) f) = targetGap d p
  size : sizeZ d.weightFn (freeInv (d.period p) f) κ ≤ 2 * d.sizeBound
  sup : supGrad (freeInv (d.period p) f) ≤ ENNReal.ofReal d.supBound

def multiplierOf {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) : Fin k → ℝ :=
  d.multiplier p + (if h : ∃ κ, ∃ f, IsHeldSolution d p f κ then h.choose else 0)

end Breakdown.Cert
