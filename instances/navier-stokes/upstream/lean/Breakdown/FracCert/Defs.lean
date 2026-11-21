import Breakdown.Frac.Defs
import Breakdown.Held.Statements

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

def entrySq (G : Space →L[ℝ] Space) : ℝ := ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2

def entryInner (G K : Space →L[ℝ] Space) : ℝ := ∑ i : Fin 3, inner ℝ (G (unitVector i)) (K (unitVector i))

def secondTrace (H : Space →L[ℝ] Space →L[ℝ] Space) : Space := ∑ j : Fin 3, H (unitVector j) (unitVector j)

def turnStep (m : ℕ) (y : Space) : Space :=
  EuclideanSpace.single 0 (Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1) +
    EuclideanSpace.single 1 (Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1) +
    EuclideanSpace.single 2 (y 2)

def mirror (y : Space) : Space :=
  EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) + EuclideanSpace.single 2 (-(y 2))

def IsClassField (m : ℕ) (v : Space → Space) : Prop :=
  (∀ᵐ y ∂volume, v (turnStep m y) = turnStep m (v y)) ∧ ∀ᵐ y ∂volume, v (mirror y) = mirror (v y)

def IsClassScalar (m : ℕ) (w : Space → ℝ) : Prop :=
  (∀ y, w (turnStep m y) = w y) ∧ ∀ y, w (mirror y) = w y

def IsTestVectorField (φ : Space → Space) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

def IsTestScalar (φ : Space → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

def IsWeakGradientOf (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) : Prop :=
  ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
    ∫ y, (fderiv ℝ φ y (unitVector j)) • v y = -∫ y, φ y • G y (unitVector j)

def IsWeakSecondDerivOf (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    Prop :=
  ∀ φ : Space → ℝ, IsTestScalar φ → ∀ i j : Fin 3,
    ∫ y, (fderiv ℝ φ y (unitVector j)) • G y (unitVector i) = -∫ y, φ y • H y (unitVector j) (unitVector i)

def IsLocalSquareIntegrable (f : Space → ℝ) : Prop := ∀ K : Set Space, IsCompact K → IntegrableOn f K

def IsGradientField (Q : Space → Space) : Prop :=
  ∃ q : Space → ℝ, IsLocalSquareIntegrable (fun y => q y ^ 2) ∧ IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2) ∧
    AEStronglyMeasurable Q volume ∧
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j)

def IsSolenoidalL2 (ζ : Space → Space) : Prop :=
  MemLp ζ 2 volume ∧ ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, inner ℝ (ζ y) (gradientAt φ y) = 0

def l2Norm (F : Space → Space) : ℝ := Real.sqrt (∫ y, ‖F y‖ ^ 2)

def l2Pair (F E : Space → Space) : ℝ := ∫ y, inner ℝ (F y) (E y)

def projectedNorm (F : Space → Space) : ℝ :=
  sInf {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => F y + Q y) 2 volume ∧ r = l2Norm (fun y => F y + Q y)}

structure IsSecondOrderField (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  measurable_velocity : AEStronglyMeasurable v volume
  measurable_gradient : AEStronglyMeasurable G volume
  measurable_second : AEStronglyMeasurable H volume
  velocity_six : MemLp v 6 volume
  gradient_two : Integrable (fun y => entrySq (G y))
  second_two : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
  weak_gradient : IsWeakGradientOf v G
  weak_second : IsWeakSecondDerivOf G H
  divergence : ∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector i) = 0
  symmetric : IsClassField m v

def IsWeakFractionalPower (α : ℝ) (v P : Space → Space) : Prop :=
  MemLp P 2 volume ∧ ∀ φ : Space → Space, IsTestVectorField φ →
    ∫ y, inner ℝ (P y) (φ y) = ∫ y, inner ℝ (v y) (fractionalPowerAt α φ y)

def driftField (α a : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  (1 - 1 / (2 * α)) • v y + (1 / (2 * α)) • G y y + a • (G y (axialTurn y) - axialTurn (v y))

def weightedEnergy (wt : Space → ℝ) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  (∫ y, ‖secondTrace (H y)‖ ^ 2) + ∫ y, wt y * entrySq (G y)

def sizeNorm (μ : ℝ) {k : ℕ} (wt : Space → ℝ) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) : ℝ :=
  Real.sqrt (weightedEnergy wt G H + μ ^ 2 * ∑ i, κ i ^ 2)

def pinValue (χ : Space → (Space →L[ℝ] Space)) (G : Space → (Space →L[ℝ] Space)) : ℝ :=
  ∫ y, entryInner (G y) (χ y)

def vecNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

def symProduct (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  (1 / 2 : ℝ) • (G y (W y) + DW y (v y))

def rowSize {N : ℕ} (e : Fin N → Space → Space) (τw : Fin N → ℝ) (F : Space → Space) : ℝ :=
  Real.sqrt (∑ i, τw i * (l2Pair F (e i)) ^ 2)

def rowSeminorm {N : ℕ} (e : Fin N → Space → Space) (τw : Fin N → ℝ) (F : Space → Space) : ℝ :=
  sInf {r | ∃ Q, IsGradientField Q ∧ r = rowSize e τw (fun y => F y + Q y)}

def boundConst (sc th cp t x y z : ℝ) : ℝ :=
  (cp ^ (-(1 / 2 : ℝ))) * ((1 / 2) * ((sc * x + 2 * th * y) / (1 - th ^ 2)) +
    Real.sqrt ((1 / 4) * ((sc * x + 2 * th * y) / (1 - th ^ 2)) ^ 2 + (y ^ 2 + t * z ^ 2) / (1 - th ^ 2)))

def radiusOf (KN L ρ : ℝ) : ℝ := 2 * ρ / (1 + Real.sqrt (1 - 4 * KN * L * ρ))

def box {k : ℕ} (rad : Fin k → ℝ) : Set (Fin k → ℝ) := {p | ∀ i, |p i| ≤ rad i}

def negSecondTrace (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) : Space := -secondTrace (H y)

structure FracCertData (k N : ℕ) where
  order : ℕ
  splitVisc : ℝ
  coercivity : ℝ
  reducedCoercivity : ℝ
  pinWeight : ℝ
  rowMax : ℝ
  multiplierScale : ℝ
  weight : Space → ℝ
  weightMin : ℝ
  weightMax : ℝ
  radius : Fin k → ℝ
  activeSet : Finset (Fin k)
  slope : Fin k → ℝ
  ellipsoidRadius : ℝ
  frame : Matrix (Fin k) (Fin k) ℝ
  frameDefect : ℝ
  rotationRate : (Fin k → ℝ) → ℝ
  multiplier : (Fin k → ℝ) → Fin k → ℝ
  profile : (Fin k → ℝ) → Space → Space
  profileSecond : (Fin k → ℝ) → Space → (Space →L[ℝ] Space →L[ℝ] Space)
  profilePower : (Fin k → ℝ) → Space → Space
  actuator : Fin k → Space → Space
  pin : Fin k → Space → (Space →L[ℝ] Space)
  smoothPin : Fin k → Space → (Space →L[ℝ] Space)
  pinGap : ℝ
  row : Fin N → Space → Space
  rowWeight : Fin N → ℝ
  modelForm : (Fin k → ℝ) → (Space → Space) → (Fin k → ℝ) → ℝ
  modelField : (Fin k → ℝ) → (Space → Space) → (Fin k → ℝ) → Space → Space
  modelPin : (Fin k → ℝ) → (Space → Space) → Fin k → ℝ
  potLoss : ℝ
  rowLoss : ℝ
  pinLoss : ℝ
  lowLoss : ℝ
  formScale : ℝ
  splitBound : ℝ
  productConst : ℝ
  defectBound : ℝ
  defectRowBound : ℝ
  sizeBound : ℝ
  adjoint : Fin k → (Fin k → ℝ) → Space → Space
  adjointSharp : Fin k → (Fin k → ℝ) → Space → Space
  adjointPin : Fin k → (Fin k → ℝ) → Fin k → ℝ
  adjointLocal : Fin k → (Fin k → ℝ) → ℝ
  adjointSpread : Fin k → (Fin k → ℝ) → ℝ
  adjointQuad : Fin k → (Fin k → ℝ) → ℝ

namespace FracCertData

variable {k N : ℕ} (d : FracCertData k N)

def gradProfile (p : Fin k → ℝ) : Space → (Space →L[ℝ] Space) := fun y => fderiv ℝ (d.profile p) y

def localField (α : ℝ) (p : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) (y : Space) : Space :=
  driftField α (d.rotationRate p) v G y - d.splitVisc • secondTrace (H y)
    + (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y + ∑ i, κ i • d.actuator i y

def splitField (P : Space → Space) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) : Space :=
  P y + d.splitVisc • secondTrace (H y)

def energy (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  weightedEnergy d.weight G H

def size (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : Fin k → ℝ) : ℝ :=
  sizeNorm d.multiplierScale d.weight G H κ

def splitEnergy (P : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  Real.sqrt (l2Pair (d.splitField P H) (negSecondTrace H) +
    d.reducedCoercivity * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y)))

def pins (G : Space → (Space →L[ℝ] Space)) : Fin k → ℝ := fun i => pinValue (d.pin i) G

def defect (α : ℝ) (p : Fin k → ℝ) (y : Space) : Space :=
  driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y + d.profilePower p y
    + d.gradProfile p y (d.profile p y) + ∑ i, d.multiplier p i • d.actuator i y

def rows (F : Space → Space) : ℝ := rowSize d.row d.rowWeight F

def rowsModGrad (F : Space → Space) : ℝ := rowSeminorm d.row d.rowWeight F

def reducedGap : ℝ := d.reducedCoercivity - d.lowLoss

def contraction : ℝ :=
  Real.sqrt ((d.splitBound + d.rowLoss / Real.sqrt d.reducedGap) ^ 2
    + d.pinWeight * d.pinLoss ^ 2 / d.reducedGap)

def boundFn (x y z : ℝ) : ℝ := boundConst d.formScale d.contraction d.reducedGap d.pinWeight x y z

def rowConst : ℝ := d.boundFn 1 (Real.sqrt d.rowMax) 0

def heldRadius : ℝ := radiusOf d.rowConst d.productConst d.sizeBound

def testBox : Set (Fin k → ℝ) := Held.testSet d.activeSet d.radius d.slope d.ellipsoidRadius

def adjointError (j : Fin k) (p : Fin k → ℝ) : Fin k → ℝ :=
  fun l => l2Pair (d.actuator l) (d.adjoint j p) - d.frame l j

def adjustedMultiplier (α : ℝ) (p : Fin k → ℝ) (j : Fin k) : ℝ :=
  (d.frameᵀ *ᵥ d.multiplier p) j - l2Pair (d.defect α p) (d.adjoint j p) - d.slope j * p j

end FracCertData

structure IsFracCert (α : ℝ) {k N : ℕ} (d : FracCertData k N) : Prop where
  order_ge : 3 ≤ d.order
  coercivity_pos : 0 < d.coercivity
  coercivity_lt : d.coercivity < d.splitVisc
  pinWeight_pos : 0 < d.pinWeight
  rowMax_pos : 0 < d.rowMax
  multiplierScale_pos : 0 < d.multiplierScale
  weight_measurable : Measurable d.weight
  weightMin_pos : 0 < d.weightMin
  weight_lower : ∀ y, d.weightMin ≤ d.weight y
  weight_upper : ∀ y, d.weight y ≤ d.weightMax
  weight_class : IsClassScalar d.order d.weight
  radius_nonneg : ∀ j, 0 ≤ d.radius j
  slope_ne_zero : ∀ j, d.slope j ≠ 0
  ellipsoidRadius_nonneg : 0 ≤ d.ellipsoidRadius
  ellipsoid_le : ∀ j ∉ d.activeSet, d.ellipsoidRadius ≤ |d.slope j| * d.radius j
  frame_near : ∀ z : Fin k → ℝ, |∑ j, (d.frame *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ d.frameDefect * ∑ j, z j ^ 2
  frameDefect_lt : d.frameDefect < 1
  rotationRate_continuous : ContinuousOn d.rotationRate (box d.radius)
  multiplier_continuous : ContinuousOn d.multiplier (box d.radius)
  profile_smooth : ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p)
  profile_second : ∀ p ∈ box d.radius, IsWeakSecondDerivOf (d.gradProfile p) (d.profileSecond p) ∧
    AEStronglyMeasurable (d.profileSecond p) volume
  profile_divergence : ∀ p ∈ box d.radius, ∀ y, divergenceAt (d.profile p) y = 0
  profile_class : ∀ p ∈ box d.radius, IsClassField d.order (d.profile p)
  profile_bounds : ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ y,
    ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖d.gradProfile p y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
      (∀ᵐ z ∂volume, ‖d.profileSecond p z‖ ≤ C * (1 + ‖z‖) ^ (-(3 : ℝ)))
  profile_drift : ∀ p ∈ box d.radius,
    MemLp (driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p)) 2 volume
  profile_power : ∀ p ∈ box d.radius, IsWeakFractionalPower α (d.profile p) (d.profilePower p)
  profile_continuous : ∀ p ∈ box d.radius, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p' ∈ box d.radius,
    dist p' p < δ → ∫ y, entrySq (d.gradProfile p' y - d.gradProfile p y) < ε
  actuator_two : ∀ i, MemLp (d.actuator i) 2 volume
  actuator_class : ∀ i, IsClassField d.order (d.actuator i)
  pin_measurable : ∀ i, AEStronglyMeasurable (d.pin i) volume ∧ AEStronglyMeasurable (d.smoothPin i) volume
  pin_two : ∀ i, Integrable (fun y => entrySq (d.pin i y)) ∧ Integrable (fun y => entrySq (d.smoothPin i y))
  pinGap_bound : ∑ l, ∫ y, entrySq (d.smoothPin l y - d.pin l y) ≤ d.pinGap ^ 2
  pinGap_nonneg : 0 ≤ d.pinGap
  row_two : ∀ a, MemLp (d.row a) 2 volume
  row_orthonormal : ∀ a b, l2Pair (d.row a) (d.row b) = if a = b then 1 else 0
  row_support : ∀ a, ∃ R : ℝ, ∀ y, R < ‖y‖ → d.row a y = 0
  row_class : ∀ a, IsClassField d.order (d.row a)
  rowWeight_pos : ∀ a, 0 < d.rowWeight a
  rowWeight_le : ∀ a, d.rowWeight a ≤ d.rowMax
  model_regular : ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ κ : Fin k → ℝ,
    AEStronglyMeasurable (d.modelField p v κ) volume ∧
      IsLocalSquareIntegrable (fun y => ‖d.modelField p v κ y‖ ^ 2)
  model_lower : ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ κ : Fin k → ℝ,
    ∀ Q, IsGradientField Q →
      d.coercivity * d.size G H κ ^ 2 ≤ d.modelForm p v κ + d.rows (fun y => d.modelField p v κ y + Q y) ^ 2
        + d.pinWeight * ∑ i, d.modelPin p v i ^ 2
  model_form : ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
    IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume → ∀ κ : Fin k → ℝ,
      d.modelForm p v κ - d.potLoss * d.size G H κ ^ 2 ≤ l2Pair (d.localField α p v G H κ) (negSecondTrace H)
  model_field : ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
    IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume → ∀ κ : Fin k → ℝ,
      ∃ Q, IsGradientField Q ∧
        d.rows (fun y => d.localField α p v G H κ y - d.modelField p v κ y + Q y) ≤ d.rowLoss * d.size G H κ
  model_pin : ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
    IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume → ∀ κ : Fin k → ℝ,
      vecNorm (fun i => d.modelPin p v i - d.pins G i) ≤ d.pinLoss * d.size G H κ
  losses_nonneg : 0 ≤ d.potLoss ∧ 0 ≤ d.rowLoss ∧ 0 ≤ d.pinLoss
  reduced_pos : 0 < d.reducedCoercivity
  reduced_le : d.reducedCoercivity ≤ d.coercivity - d.potLoss
  lowLoss_bound : ∀ κ₀ : ℝ, 0 < κ₀ →
    max (d.splitVisc - κ₀ ^ (2 * (α - 1))) 0 ≤ d.lowLoss * (1 + d.weightMin / κ₀ ^ 2)
  reducedGap_pos : 0 < d.reducedGap
  formScale_nonneg : 0 ≤ d.formScale
  formScale_bound : ∀ κ₀ : ℝ, 0 < κ₀ →
    1 ≤ d.formScale ^ 2 * (κ₀ ^ (2 * (α - 1)) - d.splitVisc + d.reducedCoercivity * (1 + d.weightMin / κ₀ ^ 2))
  splitBound_nonneg : 0 ≤ d.splitBound
  split_rows : ∀ v G H, IsSecondOrderField d.order v G H → ∀ P, IsWeakFractionalPower α v P →
    d.rows (d.splitField P H) ≤ d.splitBound * d.splitEnergy P G H
  contraction_lt : d.contraction < 1
  productConst_nonneg : 0 ≤ d.productConst
  productConst_bound : ∀ u Gu Hu, IsSecondOrderField d.order u Gu Hu → ∀ w Gw Hw, IsSecondOrderField d.order w Gw Hw →
    l2Norm (symProduct u Gu w Gw) ≤ d.productConst * Real.sqrt (d.energy Gu Hu) * Real.sqrt (d.energy Gw Hw)
  defect_norm : ∀ p ∈ box d.radius, projectedNorm (d.defect α p) ≤ d.defectBound
  defect_rows : ∀ p ∈ box d.radius, d.rowsModGrad (d.defect α p) ≤ d.defectRowBound
  size_ge : d.boundFn d.defectBound d.defectRowBound 0 ≤ d.sizeBound
  size_small : 4 * d.rowConst * d.productConst * d.sizeBound < 1
  adjoint_solenoidal : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p) ∧
    IsClassField d.order (d.adjoint j p) ∧ MemLp (d.adjointSharp j p) 2 volume
  adjoint_local : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
    IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume →
      |l2Pair (d.localField α p v G H 0) (d.adjoint j p) + l2Pair (negSecondTrace H) (d.adjointSharp j p)
        - ∑ l, d.adjointPin j p l * pinValue (d.smoothPin l) G| ≤ d.adjointLocal j p * Real.sqrt (d.energy G H)
  adjoint_spread : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
    IsWeakFractionalPower α v P →
      |l2Pair (d.splitField P H) (d.adjoint j p) - l2Pair (negSecondTrace H) (d.adjointSharp j p)|
        ≤ d.adjointSpread j p * Real.sqrt (d.energy G H)
  adjointQuad_nonneg : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, 0 ≤ d.adjointQuad j p
  adjoint_quad : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ u G H, IsSecondOrderField d.order u G H →
    |l2Pair (fun y => G y (u y)) (d.adjoint j p)| ≤ d.adjointQuad j p * d.energy G H
  active_inclusion : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ p' ∈ d.testBox,
    d.adjointQuad j p * d.heldRadius ^ 2 + d.heldRadius * Real.sqrt ((d.adjointLocal j p + d.adjointSpread j p
      + vecNorm (d.adjointPin j p) * d.pinGap / Real.sqrt d.weightMin) ^ 2
      + vecNorm (d.adjointError j p) ^ 2 / d.multiplierScale ^ 2) + |d.adjustedMultiplier α p' j|
      ≤ |d.slope j| * d.radius j
  stiff_inclusion : ∀ p' ∈ d.testBox, Real.sqrt (1 + d.frameDefect) * d.heldRadius / d.multiplierScale +
    Real.sqrt (∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.multiplier p') j - d.slope j * p' j) ^ 2) ≤ d.ellipsoidRadius
  nontrivial : ∀ p ∈ box d.radius, d.heldRadius / Real.sqrt d.weightMin < Real.sqrt (∫ y, entrySq (d.gradProfile p y))

def FracCertificateHypothesis (α : ℝ) : Prop := ∃ (k N : ℕ) (d : FracCertData k N), IsFracCert α d

end SteadyCert

end Breakdown
