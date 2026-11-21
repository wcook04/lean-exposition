import Breakdown.CellReduction.AdjointEntryDefs
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

def mixedNorm (f : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ, (∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ (6 / 5 : ℝ))) ^ (5 / 3 : ℝ)

def timeCutoff (ψ : ℝ → ℝ) (ζ : ℝ → Space → Space) (s : ℝ) (y : Space) : Space := ψ s • ζ s y

def CurlPotentialExistsHolds : Prop :=
  ∀ (C γ : ℝ) (ζ : ℝ → Space → Space),
    IsAdjointField ζ C γ → ∃ (A : ℝ → Space → Space) (C' β : ℝ), IsCurlPotential ζ A C' β

def TestFieldDensityHolds : Prop :=
  ∀ (C γ β : ℝ) (ζ A : ℝ → Space → Space) (ψ : ℝ → ℝ),
    IsAdjointField ζ C γ → IsCurlPotential ζ A C β → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ∃ φ : ℕ → ℝ → Space → Space, (∀ n, IsSpaceTimeTestField (φ n)) ∧
      (∃ a b : ℝ, ∀ n s y, s ∉ Set.Icc a b → φ n s y = 0) ∧
      Tendsto (fun n => ∫⁻ z : ℝ × Space,
        ENNReal.ofReal (‖φ n z.1 z.2 - timeCutoff ψ ζ z.1 z.2‖ ^ 2)) atTop (nhds 0) ∧
      Tendsto (fun n => ∫⁻ z : ℝ × Space,
        ENNReal.ofReal (matSq (fderiv ℝ (φ n z.1) z.2 - fderiv ℝ (timeCutoff ψ ζ z.1) z.2))) atTop (nhds 0) ∧
      Tendsto (fun n => mixedNorm (fun s y => φ n s y - timeCutoff ψ ζ s y)) atTop (nhds 0) ∧
      Tendsto (fun n => mixedNorm (fun s y =>
        timeDerivative (φ n) s y - timeDerivative (timeCutoff ψ ζ) s y)) atTop (nhds 0) ∧
      Tendsto (fun n => mixedNorm (fun s y =>
        fderiv ℝ (φ n s) y y - fderiv ℝ (timeCutoff ψ ζ s) y y)) atTop (nhds 0)

def RepresentationHolds : Prop :=
  ∀ {k : ℕ} (Γ : Set Symmetry) (P D C γ β : ℝ) (W ζ A : ℝ → Space → Space)
    (b : Fin k → ℝ → Space → Space)
    (v g F : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsFlowPiece W D → IsAdjointField ζ C γ → IsCurlPotential ζ A C β →
    IsPerturbation Γ P v G H g →
    AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
    IsRightSide W b 0 v G g F →
    periodPairing F ζ = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      (inner ℝ (v σ y) (adjointTransport P W ζ σ y) + matInner (G σ y) (fderiv ℝ (ζ σ) y))

def PotentialBoundHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P w₀ C γ : ℝ) (v g T : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (K : ℝ → Space → (Space →L[ℝ] Space)) (p : PotentialData) (n : PotentialNumbers),
    0 < w₀ → IsPerturbation Γ P v G H g → IsResidualField T K C γ → IsPotentialData p C →
    PotentialNorms p n → RemainderDualBound (remainderField w₀ T K p) n.remainder →
    |periodInnerIntegral v T + periodMatrixIntegral G K| ≤
      potentialDefect w₀ n * Real.sqrt (weightedEnergy (fun _ => w₀) G H)

def RemainderPlainHolds : Prop :=
  ∀ (R : ℝ → Space → Space) (ρ : ℝ), RemainderBounded R ρ → RemainderDualBound R ρ

def RemainderAzimuthalHolds : Prop :=
  ∀ (R : ℝ → Space → Space) (ρ : ℝ), AzimuthalBounded R ρ → RemainderDualBound R ρ

def DualBoundedBoundHolds : Prop :=
  ∀ (R : ℝ → Space → Space) (ρ : ℝ), DualBounded R ρ → RemainderDualBound R ρ

def PinChargeHolds : Prop :=
  ∀ {k : ℕ} (Γ : Set Symmetry) (P w₀ C R₀ ε ρ cn : ℝ) (v g : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)) (pd : PinData k) (c : Fin k → ℝ),
    0 < w₀ → IsPerturbation Γ P v G H g → IsPinData χ pd C R₀ →
    (∀ l, periodLIntegral (fun σ y => matSq (χ l σ y)) < ⊤) → 0 ≤ ε → 0 ≤ ρ →
    Real.sqrt (∑ l, c l ^ 2) ≤ cn →
    periodLIntegral (fun σ y => ‖∑ l, c l • (pd.potential l σ y - pd.generator l σ y)‖ ^ 2) ≤
      ENNReal.ofReal (ε ^ 2) →
    periodLIntegral (fun σ y => matSq (∑ l, c l • (χ l σ y - fderiv ℝ (pd.potential l σ) y))) ≤
      ENNReal.ofReal (ρ ^ 2 * ∑ l, c l ^ 2) →
    |(∑ l, c l * pinValue (χ l) G)
        - ∑ l, c l * periodMatrixIntegral G (fun σ y =>
          fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y))| ≤
      (ε + cn * ρ / Real.sqrt w₀) * Real.sqrt (weightedEnergy (fun _ => w₀) G H)

def FreeShiftBoundHolds : Prop :=
  ∀ {k : ℕ} (Γ : Set Symmetry) (P D C γ : ℝ) (v g ζ : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (S : Finset (Fin k))
    (f : Fin k → ℝ → Space → Space) (q ϱ δ : Fin k → ℝ) (ν μ : ℝ),
    IsPerturbation Γ P v G H g → IsAdjointField ζ C γ →
    (∀ i ∈ S, IsFlowPiece (f i) D) → (∀ i ∈ S, 0 < ϱ i) → (∀ i ∈ S, 0 ≤ δ i) → 0 ≤ ν → 0 ≤ μ →
    periodLIntegral (fun σ y => (∑ i ∈ S, ϱ i * ‖f i σ y‖ ^ 2) * ‖ζ σ y‖ ^ 2) ≤ ENNReal.ofReal (ν ^ 2) →
    (∀ i ∈ S, RemainderDualBound (fun σ y => transposeApply (fderiv ℝ (f i σ) y) (ζ σ y)) (δ i)) →
    ∑ i ∈ S, ϱ i * δ i ^ 2 ≤ μ ^ 2 →
    |periodInnerIntegral v (advectionShift (fun σ y => ∑ i ∈ S, q i • f i σ y) ζ)| ≤
      Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * (ν + μ) * gradientNorm G

structure AdjointDefectStructure {k : ℕ} (d : ExtendedCertificateData k) (j : Fin k)
    (r : AdjointDefectEntry k) : Prop where
  adjoint_eq : ∀ q ∈ d.params, d.adjoint j q = r.field
  coupling_eq : ∀ q ∈ d.params, ∀ l, d.coupling q j l = r.pinCoef l
  field_class : ∃ C γ, IsAdjointField r.field C γ
  field_potential : ∃ A C β, IsCurlPotential r.field A C β
  pieces : ∃ D, (∀ q ∈ d.params, IsFlowPiece (r.centre q) D) ∧ (∀ i ∈ r.fittedSet, IsFlowPiece (r.fitted i) D) ∧
    ∀ q ∈ d.params, ∀ i ∈ r.fittedSetᶜ, IsFlowPiece (r.free q i) D
  profile_split : ∀ q ∈ d.params, ∀ σ y, d.profile q σ y = r.centre q σ y
    + (∑ i ∈ r.fittedSet, q i • r.fitted i σ y) + ∑ i ∈ r.fittedSetᶜ, q i • r.free q i σ y
  period_split : ∀ q ∈ d.params, 1 / d.period q = 1 / r.centrePeriod + ∑ i, q i * r.periodRate i

structure AdjointPotentialFacts {k : ℕ} (d : ExtendedCertificateData k) (j : Fin k)
    (r : AdjointDefectEntry k) : Prop where
  potentials : ∃ C, IsPotentialData r.centrePotential C ∧
    ∀ i ∈ r.fittedSet, IsPotentialData (r.fittedPotential i) C
  pins : ∃ C R₀, IsPinData d.pin r.pins C R₀

def AdjointDefectBridgeHolds : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k) (r : Fin k → AdjointDefectEntry k),
    d.weightFn = (fun _ => d.weight) → 0 < d.weight →
    (∀ j ∈ d.adjointSet, AdjointDefectStructure d j (r j)) →
    (∀ j ∈ d.adjointSet, AdjointPotentialFacts d j (r j)) →
    (∀ j ∈ d.adjointSet, AdjointDefectBounded d j (r j)) →
    ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ v G H g,
      IsPerturbation d.symmetries (d.period q) v G H g → ∀ F : ℝ → Space → Space,
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile q) d.actuator 0 v G g F →
        |periodPairing F (d.adjoint j q) - ∑ l, d.coupling q j l * pinValue (d.pin l) G| ≤
          d.adjointDefect j * Real.sqrt (weightedEnergy d.weightFn G H)

end AdjointDefect

end Breakdown
