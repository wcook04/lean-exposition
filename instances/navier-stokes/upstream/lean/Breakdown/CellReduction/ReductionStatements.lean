import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

def OperatorSquareBoundHolds : Prop :=
  ∀ A : Space →L[ℝ] Space, ‖A‖ ^ 2 ≤ matSq A

def StrainOfSymmetricPartHolds : Prop :=
  ∀ (A : Space →L[ℝ] Space) (S : ℝ), ‖(1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)‖ ≤ S →
    ∀ u : Space, -S * ‖u‖ ^ 2 ≤ inner ℝ (A u) u

def MatrixFactsHolds : Prop :=
  OperatorSquareBoundHolds ∧ StrainOfSymmetricPartHolds

def SliceSupNormHolds : Prop :=
  ∀ (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsWeakGradient w G →
    (∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j))) →
    (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (matSq (G y))) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) < ⊤ →
    ∀ᵐ y, ‖w y‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ z, matSq (G z)) *
      Real.sqrt (∫ z, ‖secondDerivTrace (H z)‖ ^ 2)

def PerturbationSliceHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g →
    ∀ᵐ σ, IsWeakGradient (v σ) (G σ) ∧
      (∀ j : Fin 3, IsWeakGradient (fun y => G σ y (unitVector j))
        (fun y => (H σ y).flip (unitVector j))) ∧
      (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (matSq (G σ y))) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2)) < ⊤

def SliceEnergySupHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P w₀ : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    0 < w₀ → IsPerturbation Γ P v G H g →
    ∀ᵐ σ, ∀ᵐ y, ‖v σ y‖ ^ 2 ≤ supBoundFactor w₀ ^ 2 *
      ((∫ z, ‖secondDerivTrace (H σ z)‖ ^ 2) + w₀ * (∫ z, matSq (G σ z)))

def ProfileEnergySupHolds : Prop :=
  ∀ (Γ : Set Symmetry) (w₀ : ℝ) (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    0 < w₀ → IsProfileField Γ w G H →
    ∀ᵐ y, ‖w y‖ ^ 2 ≤ supBoundFactor w₀ ^ 2 * stationaryEnergy (fun _ => w₀) G H

def PeriodGradientEnergyHolds : Prop :=
  ∀ (w₀ : ℝ) (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    0 < w₀ →
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) < ⊤ →
    w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal ≤ weightedEnergy (fun _ => w₀) G H

def EnergyBoundsHolds : Prop :=
  SliceEnergySupHolds ∧ ProfileEnergySupHolds ∧ PeriodGradientEnergyHolds

def CubicWeightProductHolds : Prop :=
  ∀ (w : Space → Space) (G : Space → (Space →L[ℝ] Space)) (A : Space → ℝ),
    IsWeakGradient w G →
    (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (matSq (G y))) < ⊤ →
    AEStronglyMeasurable A volume →
    (∫⁻ y, ENNReal.ofReal (A y ^ 2 * ‖w y‖ ^ 2)) ≤
      ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (|A y| ^ 3)) ^ ((2 : ℝ) / 3) *
        (∫⁻ y, ENNReal.ofReal (matSq (G y)))

def PeriodSumBoundHolds : Prop :=
  ∀ (n : ℕ) (F : ℝ → Space → ℝ) (f : Fin n → ℝ → Space → ℝ) (c : Fin n → ℝ) (E : ℝ),
    0 ≤ E → (∀ a, 0 ≤ c a) →
    (∀ a, AEMeasurable (fun z : ℝ × Space => f a z.1 z.2) volume) →
    (∀ a σ y, 0 ≤ f a σ y) → (∀ σ y, 0 ≤ F σ y) → (∀ σ y, F σ y ≤ ∑ a, f a σ y) →
    (∀ a, periodLIntegral (fun σ y => f a σ y ^ 2) ≤ ENNReal.ofReal (c a ^ 2 * E)) →
    periodLIntegral (fun σ y => F σ y ^ 2) ≤ ENNReal.ofReal ((∑ a, c a) ^ 2 * E)

def PeriodPairingBoundHolds : Prop :=
  ∀ (F M : ℝ → Space → Space) (B : ℝ), 0 ≤ B →
    periodLIntegral (fun σ y => ‖F σ y‖ * ‖M σ y‖) ≤ ENNReal.ofReal B →
    |periodPairing F M| ≤ B

def StationaryPairingBoundHolds : Prop :=
  ∀ (F M : Space → Space) (B : ℝ), 0 ≤ B →
    (∫⁻ y, ENNReal.ofReal (‖F y‖ * ‖M y‖)) ≤ ENNReal.ofReal B →
    |(∫ y, inner ℝ (F y) (M y))| ≤ B

def SliceIntegrateHolds : Prop :=
  ∀ (f h : ℝ → Space → ℝ) (c : ℝ), 0 ≤ c →
    (∀ᵐ σ, (∫⁻ y, ENNReal.ofReal (f σ y)) ≤ ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (h σ y))) →
    periodLIntegral f ≤ ENNReal.ofReal c * periodLIntegral h

def PeriodGlueHolds : Prop :=
  PeriodSumBoundHolds ∧ PeriodPairingBoundHolds ∧ StationaryPairingBoundHolds ∧ SliceIntegrateHolds

def ConvectionIdentityHolds : Prop :=
  ∀ (Γ : Set Symmetry) (W w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (C : ℝ),
    ContDiff ℝ 1 W → (∀ y, ‖W y‖ ≤ C) → (∀ y, ‖fderiv ℝ W y‖ ≤ C) →
    (∀ y, divergenceAt W y = 0) → IsProfileField Γ w G H →
    (∫ y, inner ℝ (G y (W y)) (-secondDerivTrace (H y))) =
      ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y (ContinuousLinearMap.adjoint (G y) (unitVector i)))
        (ContinuousLinearMap.adjoint (G y) (unitVector i))

def FrozenIntegrandHolds : Prop :=
  ∀ (Γ : Set Symmetry) (C : ℝ) (W w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    ContDiff ℝ 1 W → (∀ y, ‖W y‖ ≤ C / (1 + ‖y‖)) → (∀ y, ‖fderiv ℝ W y‖ ≤ C / (1 + ‖y‖) ^ 2) →
    IsProfileField Γ w G H →
    Integrable (fun y => inner ℝ (G y (W y)) (-secondDerivTrace (H y))) ∧
      Integrable (fun y => inner ℝ (fderiv ℝ W y (w y)) (-secondDerivTrace (H y)))

structure BridgeStanding {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  weight_pos : 0 < d.weight
  weightFn_const : d.weightFn = fun _ => d.weight
  model_state : ∀ q ∈ d.params, ∃ (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ),
    CoerciveWeak.IsWeakSecondDerivState (d.model q) HW D
  profile_smooth : ∀ q ∈ d.params, ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2)
  profile_decay : ∀ q ∈ d.params, ∃ D : ℝ, ∀ σ y, ‖d.profile q σ y‖ ≤ D / (1 + ‖y‖) ∧
    ‖fderiv ℝ (d.profile q σ) y‖ ≤ D / (1 + ‖y‖) ^ 2
  adjoint_measurable : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    AEStronglyMeasurable (fun z : ℝ × Space => d.adjoint j q z.1 z.2) volume

def GapTransferClause {k : ℕ} (d : ExtendedCertificateData k) : Prop :=
  ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    periodLIntegral (fun σ y => ‖G σ y (d.profile q σ y - d.model q σ y)
      + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y) (v σ y)‖ ^ 2) ≤
      ENNReal.ofReal (d.gapSize ^ 2 * weightedEnergy d.weightFn G H)

def FormShiftClause {k : ℕ} (d : ExtendedCertificateData k) : Prop :=
  ∀ q ∈ d.params, ∀ σ w G H, IsProfileField d.symmetries w G H →
    -d.formShift * stationaryEnergy d.weightFn G H ≤
      frozenForm (d.profile q σ) w G H - frozenForm (d.model q σ) w G H

def FrozenFormClause {k : ℕ} (d : ExtendedCertificateData k) : Prop :=
  ∀ q ∈ d.params, ∀ σ w G H, IsProfileField d.symmetries w G H →
    -d.modelFormBound * stationaryEnergy d.weightFn G H ≤ frozenForm (d.model q σ) w G H

def AdjointQuadraticClause {k : ℕ} (d : ExtendedCertificateData k) : Prop :=
  ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ v G H g,
    IsPerturbation d.symmetries (d.period q) v G H g →
      |periodPairing (fun σ y => G σ y (v σ y)) (d.adjoint j q)| ≤
        d.adjointQuad j * weightedEnergy d.weightFn G H

structure ShiftPieces (k : ℕ) where
  count : ℕ
  piece : Fin count → (Fin k → ℝ) → ℝ → Space → Space
  pieceGrad : Fin count → (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space)
  cubicForm : Fin count → Bool
  supNum : Fin count → ℝ
  gradNum : Fin count → ℝ

def PieceGradBound (cubic : Bool) (D : Space → (Space →L[ℝ] Space)) (n : ℝ) : Prop :=
  if cubic then (∫⁻ y, ENNReal.ofReal (‖D y‖ ^ 3)) ≤ ENNReal.ofReal (n ^ 3)
  else (∫⁻ y, ENNReal.ofReal (‖D y‖ ^ 2)) ≤ ENNReal.ofReal (n ^ 2)

structure ShiftPiecesValid {k : ℕ} (d : ExtendedCertificateData k) (r : ShiftPieces k) : Prop where
  decompose : ∀ q ∈ d.params, ∀ σ y, d.profile q σ y - d.model q σ y = ∑ a, r.piece a q σ y
  decompose_grad : ∀ q ∈ d.params, ∀ σ y,
    fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y = ∑ a, r.pieceGrad a q σ y
  piece_measurable : ∀ a, ∀ q ∈ d.params, StronglyMeasurable (fun z : ℝ × Space => r.piece a q z.1 z.2)
  pieceGrad_measurable : ∀ a, ∀ q ∈ d.params,
    StronglyMeasurable (fun z : ℝ × Space => r.pieceGrad a q z.1 z.2)
  supNum_nonneg : ∀ a, 0 ≤ r.supNum a
  gradNum_nonneg : ∀ a, 0 ≤ r.gradNum a
  piece_sup : ∀ a, ∀ q ∈ d.params, ∀ σ y, ‖r.piece a q σ y‖ ≤ r.supNum a
  piece_grad : ∀ a, ∀ q ∈ d.params, ∀ σ, PieceGradBound (r.cubicForm a) (r.pieceGrad a q σ) (r.gradNum a)

def SmoothShiftPiecesHolds : Prop :=
  ∀ (k : ℕ) (d : ExtendedCertificateData k) (r : ShiftPieces k), BridgeStanding d →
    (∀ a, ∀ q ∈ d.params, ContDiff ℝ 1 (fun z : ℝ × Space => r.piece a q z.1 z.2)) →
    (∀ a q σ y, r.pieceGrad a q σ y = fderiv ℝ (r.piece a q σ) y) →
    (∀ q ∈ d.params, ∀ σ y, d.profile q σ y - d.model q σ y = ∑ a, r.piece a q σ y) →
    (∀ q ∈ d.params, ∀ σ y,
      fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y = ∑ a, r.pieceGrad a q σ y) ∧
    (∀ a, ∀ q ∈ d.params, StronglyMeasurable (fun z : ℝ × Space => r.piece a q z.1 z.2)) ∧
    (∀ a, ∀ q ∈ d.params, StronglyMeasurable (fun z : ℝ × Space => r.pieceGrad a q z.1 z.2))

structure GapTransferBounded {k : ℕ} (d : ExtendedCertificateData k) (r : ShiftPieces k) : Prop where
  valid : ShiftPiecesValid d r
  sum_le : (∑ a, (gapGradCoeff d.weight (r.cubicForm a) * r.gradNum a
    + r.supNum a / Real.sqrt d.weight)) ≤ d.gapSize

structure FormShiftBounded {k : ℕ} (d : ExtendedCertificateData k) (r : ShiftPieces k) : Prop where
  valid : ShiftPiecesValid d r
  sum_le : (∑ a, (shiftGradCoeff d.weight (r.cubicForm a) * r.gradNum a
    + r.supNum a / (2 * Real.sqrt d.weight))) ≤ d.formShift

def GapSupTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P w₀ s : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g δ : ℝ → Space → Space),
    0 < w₀ → 0 ≤ s → IsPerturbation Γ P v G H g → (∀ σ y, ‖δ σ y‖ ≤ s) →
    periodLIntegral (fun σ y => ‖G σ y (δ σ y)‖ ^ 2) ≤
      ENNReal.ofReal ((s / Real.sqrt w₀) ^ 2 * weightedEnergy (fun _ => w₀) G H)

def GapGradTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P w₀ n : ℝ) (cubic : Bool) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (D : ℝ → Space → (Space →L[ℝ] Space)),
    0 < w₀ → 0 ≤ n → IsPerturbation Γ P v G H g →
    StronglyMeasurable (fun z : ℝ × Space => D z.1 z.2) → (∀ σ, PieceGradBound cubic (D σ) n) →
    periodLIntegral (fun σ y => ‖D σ y (v σ y)‖ ^ 2) ≤
      ENNReal.ofReal ((gapGradCoeff w₀ cubic * n) ^ 2 * weightedEnergy (fun _ => w₀) G H)

def ShiftSupTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (w₀ s : ℝ) (w δ : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    0 < w₀ → 0 ≤ s → IsProfileField Γ w G H → (∀ y, ‖δ y‖ ≤ s) →
    (∫⁻ y, ENNReal.ofReal (‖G y (δ y)‖ * ‖secondDerivTrace (H y)‖)) ≤
      ENNReal.ofReal (s / (2 * Real.sqrt w₀) * stationaryEnergy (fun _ => w₀) G H)

def ShiftGradTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (w₀ n : ℝ) (cubic : Bool) (w : Space → Space) (D G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    0 < w₀ → 0 ≤ n → IsProfileField Γ w G H → StronglyMeasurable D → PieceGradBound cubic D n →
    (∫⁻ y, ENNReal.ofReal (‖D y (w y)‖ * ‖secondDerivTrace (H y)‖)) ≤
      ENNReal.ofReal (shiftGradCoeff w₀ cubic * n * stationaryEnergy (fun _ => w₀) G H)

def StrainTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (w₀ S C : ℝ) (W w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    0 < w₀ → 0 ≤ S → ContDiff ℝ 1 W → (∀ y, ‖W y‖ ≤ C) → (∀ y, ‖fderiv ℝ W y‖ ≤ C) →
    (∀ y, divergenceAt W y = 0) → (∀ y (u : Space), -S * ‖u‖ ^ 2 ≤ inner ℝ (fderiv ℝ W y u) u) →
    IsProfileField Γ w G H →
    -(S / w₀) * stationaryEnergy (fun _ => w₀) G H ≤ (∫ y, inner ℝ (G y (W y)) (-secondDerivTrace (H y)))

def AdjointQuadTermHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P w₀ z : ℝ) (cubic : Bool) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g ζ : ℝ → Space → Space),
    0 < w₀ → 0 ≤ z → IsPerturbation Γ P v G H g →
    AEStronglyMeasurable (fun p : ℝ × Space => ζ p.1 p.2) volume →
    (∀ σ, AdjointSizeBound cubic (ζ σ) z) →
    periodLIntegral (fun σ y => ‖G σ y (v σ y)‖ * ‖ζ σ y‖) ≤
      ENNReal.ofReal (adjointQuadCoeff w₀ cubic * z * weightedEnergy (fun _ => w₀) G H)

def GapTransferBridgeHolds : Prop :=
  ∀ (k : ℕ) (d : ExtendedCertificateData k) (r : ShiftPieces k),
    BridgeStanding d → GapTransferBounded d r → GapTransferClause d

def FormShiftBridgeHolds : Prop :=
  ∀ (k : ℕ) (d : ExtendedCertificateData k) (r : ShiftPieces k),
    BridgeStanding d → FormShiftBounded d r → FormShiftClause d

def FrozenFormBridgeHolds : Prop :=
  ∀ (k : ℕ) (d : ExtendedCertificateData k) (r : ModelFormNumbers),
    BridgeStanding d → FrozenFormBounded d r → FrozenFormClause d

def AdjointQuadraticBridgeHolds : Prop :=
  ∀ (k : ℕ) (d : ExtendedCertificateData k) (r : AdjointQuadNumbers k),
    BridgeStanding d → AdjointQuadraticBounded d r → AdjointQuadraticClause d

end CertReduction

end Breakdown
