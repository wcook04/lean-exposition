import Breakdown.Cert.CoerciveStatement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

def rowNorm {m : ℕ} (e : Fin m → ℝ → Space → Space) (τ : Fin m → ℝ) (F : ℝ → Space → Space) : ℝ :=
  Real.sqrt (∑ a, τ a * periodPairing F (e a) ^ 2)

def weakDefectField {k : ℕ} (P : ℝ) (W : ℝ → Space → Space)
    (Hs : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (b : Fin k → ℝ → Space → Space) (lam : Fin k → ℝ) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => W s y) σ + (1 / 2 : ℝ) • W σ y + (1 / 2 : ℝ) • fderiv ℝ (W σ) y y
    - secondDerivTrace (Hs σ y) + advectionAt (W σ) y + ∑ i, lam i • b i σ y + g σ y

structure ExtendedCertificateData (k : ℕ) where
  symmetries : Set Symmetry
  period : (Fin k → ℝ) → ℝ
  profile : (Fin k → ℝ) → ℝ → Space → Space
  profileSecondDeriv : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)
  pressureGrad : (Fin k → ℝ) → ℝ → Space → Space
  multiplier : (Fin k → ℝ) → Fin k → ℝ
  target : (Fin k → ℝ) → Fin k → ℝ
  actuator : Fin k → ℝ → Space → Space
  pin : Fin k → ℝ → Space → (Space →L[ℝ] Space)
  multiplierWeight : ℝ
  model : (Fin k → ℝ) → ℝ → Space → Space
  gapSize : ℝ
  formShift : ℝ
  rowCount : ℕ
  rowField : Fin rowCount → ℝ → Space → Space
  rowWeight : Fin rowCount → ℝ
  rowBound : ℝ
  weight : ℝ
  weightFn : Space → ℝ
  weightMax : ℝ
  coerciveL2 : ℝ
  coercivePin : ℝ
  coerciveTotal : ℝ
  decay : ℝ
  periodMax : ℝ
  twist : ℕ
  actuatorBound : ℝ
  modelFormBound : ℝ
  formBound : ℝ
  defectBound : (Fin k → ℝ) → ℝ
  defectRowBound : (Fin k → ℝ) → ℝ
  defectMax : ℝ
  sizeBound : ℝ
  supBound : ℝ
  frame : Matrix (Fin k) (Fin k) ℝ
  scale : Fin k → ℝ
  radius : Fin k → ℝ
  stiffRadius : ℝ
  adjointSet : Finset (Fin k)
  adjoint : Fin k → (Fin k → ℝ) → ℝ → Space → Space
  coupling : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ
  adjointDefect : Fin k → ℝ
  adjointL2 : Fin k → ℝ
  adjointQuad : Fin k → ℝ
  adjointOffset : Fin k → ℝ
  stiffNorm : ℝ
  stiffOffset : ℝ

namespace ExtendedCertificateData

variable {k : ℕ} (d : ExtendedCertificateData k)

def params : Set (Fin k → ℝ) :=
  {q | (∀ j ∈ d.adjointSet, |q j| ≤ d.radius j) ∧
    ∑ j ∈ d.adjointSetᶜ, (d.scale j * q j) ^ 2 ≤ d.stiffRadius ^ 2}

def transferLoss : ℝ := (d.coerciveL2 + d.rowBound) * d.gapSize

def rows (F : ℝ → Space → Space) : ℝ := rowNorm d.rowField d.rowWeight F

def defect (q : Fin k → ℝ) : ℝ → Space → Space :=
  weakDefectField (d.period q) (d.profile q) (d.profileSecondDeriv q) (d.pressureGrad q) d.actuator
    (d.multiplier q)

def targetGap (q : Fin k → ℝ) (i : Fin k) : ℝ :=
  d.target q i - pinValue (d.pin i) (fun σ y => fderiv ℝ (d.profile q σ) y)

def adjustedMultiplier (q : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ i, d.frame i j * d.multiplier q i - periodPairing (d.defect q) (d.adjoint j q)
    - ∑ l, d.coupling q j l * d.targetGap q l

def actuatorAdjointError (q : Fin k → ℝ) (j : Fin k) : Fin k → ℝ :=
  fun l => periodPairing (d.actuator l) (d.adjoint j q) - d.frame l j

end ExtendedCertificateData

structure IsExtendedCertificate {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  radius_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j
  stiffRadius_nonneg : 0 ≤ d.stiffRadius
  scale_ne_zero : ∀ j, d.scale j ≠ 0
  weight_pos : 0 < d.weight
  weightFn_measurable : Measurable d.weightFn
  weightFn_lower : ∀ y, d.weight ≤ d.weightFn y
  weightFn_upper : ∀ y, d.weightFn y ≤ d.weightMax
  weightFn_invariant : ∀ γ ∈ d.symmetries, ∀ y, d.weightFn (γ.1 y) = d.weightFn y
  multiplierWeight_pos : 0 < d.multiplierWeight
  coerciveL2_nonneg : 0 ≤ d.coerciveL2
  coercivePin_nonneg : 0 ≤ d.coercivePin
  rowBound_nonneg : 0 ≤ d.rowBound
  gapSize_nonneg : 0 ≤ d.gapSize
  formShift_nonneg : 0 ≤ d.formShift
  transfer_lt : d.transferLoss < 1
  coerciveTotal_ge : d.coerciveL2 + d.rowBound ≤ (1 - d.transferLoss) * d.coerciveTotal
  coerciveTotal_pos : 0 < d.coerciveTotal
  actuatorBound_nonneg : 0 ≤ d.actuatorBound
  modelFormBound_nonneg : 0 ≤ d.modelFormBound
  formBound_ge : d.modelFormBound + d.formShift ≤ d.formBound
  sizeBound_nonneg : 0 ≤ d.sizeBound
  supBound_pos : 0 < d.supBound
  period_continuous : ContinuousOn d.period d.params
  period_pos : ∀ q ∈ d.params, 0 < d.period q
  period_le : ∀ q ∈ d.params, d.period q ≤ d.periodMax
  twist_pos : 0 < d.twist
  twist_mem : d.twist = 1 ∨ (d.twist = 2 ∧ ∃ Q, (Q, (1 / 2 : ℝ)) ∈ d.symmetries)
  multiplier_continuous : ContinuousOn d.multiplier d.params
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
  actuator_measurable : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume
  actuator_periodic : ∀ i, IsTimePeriodic (d.actuator i)
  actuator_invariant : ∀ i, ∀ γ ∈ d.symmetries, ∀ᵐ z : ℝ × Space,
    d.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (d.actuator i z.1 z.2)
  actuator_norm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
    ENNReal.ofReal (d.actuatorBound ^ 2)
  pin_measurable : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.pin i z.1 z.2) volume
  pin_finite : ∀ i, periodLIntegral (fun σ y => matSq (d.pin i σ y)) < ⊤
  model_smooth : ∀ q ∈ d.params, ContDiff ℝ 1 (fun z : ℝ × Space => d.model q z.1 z.2)
  model_periodic : ∀ q ∈ d.params, IsTimePeriodic (d.model q)
  gap_transfer : ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    periodLIntegral (fun σ y => ‖G σ y (d.profile q σ y - d.model q σ y)
      + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y) (v σ y)‖ ^ 2) ≤
      ENNReal.ofReal (d.gapSize ^ 2 * weightedEnergy d.weightFn G H)
  form_shift : ∀ q ∈ d.params, ∀ σ w G H, IsProfileField d.symmetries w G H →
    -d.formShift * stationaryEnergy d.weightFn G H ≤
      frozenForm (d.profile q σ) w G H - frozenForm (d.model q σ) w G H
  rowField_measurable : ∀ a, AEStronglyMeasurable (fun z : ℝ × Space => d.rowField a z.1 z.2) volume
  rowField_periodic : ∀ a, IsTimePeriodic (d.rowField a)
  rowField_finite : ∀ a, periodLIntegral (fun σ y => ‖d.rowField a σ y‖ ^ 2) < ⊤
  rowField_orthonormal : ∀ a b, periodPairing (d.rowField a) (d.rowField b) = if a = b then 1 else 0
  rowWeight_nonneg : ∀ a, 0 ≤ d.rowWeight a
  rowWeight_le : ∀ a, d.rowWeight a ≤ d.rowBound ^ 2
  coercive : ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.model q) d.actuator κ v G g F →
      Real.sqrt (weightedEnergy d.weightFn G H + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) ≤
        d.coerciveL2 * periodNorm F + d.rows F + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)
  frozen_form : ∀ q ∈ d.params, ∀ σ w G H, IsProfileField d.symmetries w G H →
    -d.modelFormBound * stationaryEnergy d.weightFn G H ≤ frozenForm (d.model q σ) w G H
  defect_nonneg : ∀ q ∈ d.params, 0 ≤ d.defectBound q ∧ 0 ≤ d.defectRowBound q
  defect_l2 : ∀ q ∈ d.params,
    periodLIntegral (fun σ y => ‖d.defect q σ y‖ ^ 2) ≤ ENNReal.ofReal (d.defectBound q ^ 2)
  defect_rows : ∀ q ∈ d.params, d.rows (d.defect q) ≤ d.defectRowBound q
  defect_le : ∀ q ∈ d.params, d.defectBound q ≤ d.defectMax
  size : ∀ q ∈ d.params, d.coerciveL2 * d.defectBound q + d.defectRowBound q
    + d.coercivePin * vecNorm (d.targetGap q) ≤ (1 - d.transferLoss) * d.sizeBound
  small_first : 2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound < 1
  small_second : 4 * d.sizeBound ^ 2 * ((1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
      + 2 * (d.periodMax / d.twist) * (d.actuatorBound / d.multiplierWeight)
      + 2 * (d.periodMax / d.twist) / d.coerciveTotal) ≤ d.supBound ^ 2
  small_third : 4 * (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound) * d.sizeBound ^ 2
    + 4 * (d.periodMax / d.twist) * d.sizeBound * (d.defectMax
      + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound
      + 2 * (d.actuatorBound / d.multiplierWeight) * d.sizeBound) ≤ d.supBound ^ 2
  frame_unit : IsUnit d.frame
  adjoint_measurable : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    AEStronglyMeasurable (fun z : ℝ × Space => d.adjoint j q z.1 z.2) volume
  adjoint_periodic : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, IsTimePeriodic (d.adjoint j q)
  adjoint_l2 : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ σ,
    ∫⁻ y, ENNReal.ofReal (‖d.adjoint j q σ y‖ ^ 2) ≤ ENNReal.ofReal (d.adjointL2 j ^ 2)
  adjointL2_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointL2 j
  adjointDefect_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointDefect j
  adjointQuad_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointQuad j
  adjoint_quadratic : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ v G H g,
    IsPerturbation d.symmetries (d.period q) v G H g →
      |periodPairing (fun σ y => G σ y (v σ y)) (d.adjoint j q)| ≤
        d.adjointQuad j * weightedEnergy d.weightFn G H
  adjoint_defect : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ v G H g,
    IsPerturbation d.symmetries (d.period q) v G H g → ∀ F : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.profile q) d.actuator 0 v G g F →
      |periodPairing F (d.adjoint j q) - ∑ l, d.coupling q j l * pinValue (d.pin l) G| ≤
        d.adjointDefect j * Real.sqrt (weightedEnergy d.weightFn G H)
  adjoint_offset : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    |d.adjustedMultiplier q j - d.scale j * q j| ≤ d.adjointOffset j
  adjoint_inclusion : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    d.adjointQuad j * (2 * d.sizeBound) ^ 2 + 2 * d.sizeBound * Real.sqrt (d.adjointDefect j ^ 2
      + (vecNorm (d.actuatorAdjointError q j) / d.multiplierWeight) ^ 2) + d.adjointOffset j ≤
      |d.scale j| * d.radius j
  stiffNorm_nonneg : 0 ≤ d.stiffNorm
  stiff_norm : ∀ x : Fin k → ℝ, ∑ j ∈ d.adjointSetᶜ, (∑ i, d.frame i j * x i) ^ 2 ≤
    d.stiffNorm ^ 2 * ∑ i, x i ^ 2
  stiff_offset : ∀ q ∈ d.params, Real.sqrt (∑ j ∈ d.adjointSetᶜ,
    (∑ i, d.frame i j * d.multiplier q i - d.scale j * q j) ^ 2) ≤ d.stiffOffset
  stiff_inclusion : 2 * d.sizeBound * d.stiffNorm / d.multiplierWeight + d.stiffOffset ≤ d.stiffRadius
  nontrivial : ∀ q ∈ d.params, 4 * d.sizeBound ^ 2 / d.weight <
    (periodLIntegral (fun σ y => matSq (fderiv ℝ (d.profile q σ) y))).toReal

def ExtendedCertificateHypothesis : Prop :=
  ∃ (k : ℕ) (d : ExtendedCertificateData k), IsExtendedCertificate d

namespace ExtendedCertificateData

variable {k : ℕ} (d : ExtendedCertificateData k)

def withUnitWeight : ExtendedCertificateData k :=
  { d with
    actuator := fun i σ y => (1 / d.multiplierWeight) • d.actuator i σ y
    multiplier := fun q i => d.multiplierWeight * d.multiplier q i
    multiplierWeight := 1
    actuatorBound := d.actuatorBound / d.multiplierWeight
    frame := (1 / d.multiplierWeight) • d.frame
    stiffNorm := d.stiffNorm / d.multiplierWeight }

def atProfile : ExtendedCertificateData k :=
  { d with
    model := d.profile
    gapSize := 0
    formShift := 0
    coerciveL2 := d.coerciveL2 / (1 - d.transferLoss)
    coercivePin := d.coercivePin / (1 - d.transferLoss)
    rowWeight := fun a => d.rowWeight a / (1 - d.transferLoss) ^ 2
    rowBound := d.rowBound / (1 - d.transferLoss)
    modelFormBound := d.formBound
    defectRowBound := fun q => d.defectRowBound q / (1 - d.transferLoss) }

end ExtendedCertificateData

end Breakdown
