import Breakdown.FracCert.Defs
import Breakdown.FracCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

def curlGradSq (H : Space →L[ℝ] Space →L[ℝ] Space) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * H (unitVector a) (unitVector j) l) ^ 2

def fullSecondSq (H : Space →L[ℝ] Space →L[ℝ] Space) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ‖H (unitVector a) (unitVector b)‖ ^ 2

def jForm (S Gm Dv : Space →L[ℝ] Space) (v : Space) : ℝ :=
  -inner ℝ (curlOf Dv) (S (curlOf Dv)) +
    ∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * (Gm v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry Gm l j)
        * entry Dv i l

def smoothingForm (lam : ℝ) (φ : Space → Space) : ℝ :=
  sInf {r | ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)), MemLp ψ 2 volume ∧
    AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧ IsWeakGradientOf ψ Dψ ∧
    r = (∫ y, ‖φ y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y)}

namespace FracCellData

variable {k N : ℕ} (c : FracCellData k N)

def modelFieldOf (α : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) (y : Space) : Space :=
  driftField α c.modelRate v G y - c.splitVisc • secondTrace (H y) + crossVec (curlOf (G y)) (c.modelVelocity y)
    + crossVec (c.modelCurl y) (v y) + ∑ i, κ i • c.modelActuator i y

def formOf (α : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) : ℝ :=
  c.coercivity * weightedEnergy c.weight G H
    + (c.innerWeight - c.coercivity) * (∫ y, fullSecondSq (H y))
    + (c.splitVisc - c.innerWeight) * (∫ y, curlGradSq (H y))
    + (∫ y, ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
        + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y)))
    + (∫ y, jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y))
    + ∑ i, κ i * (∫ y, entryInner (G y) (c.modelActuatorGrad i y))

def pinOf (G : Space → (Space →L[ℝ] Space)) (i : Fin k) : ℝ := pinValue (c.modelPinField i) G

def quadForm (α : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) (Q : Space → Space) : ℝ :=
  c.formOf α v G H κ - c.coercivity * weightedEnergy c.weight G H
    + c.toFracCertData.rows (fun y => c.modelFieldOf α v G H κ y + Q y) ^ 2
    + c.pinWeight * ∑ i, c.pinOf G i ^ 2 - c.coercivity * c.multiplierScale ^ 2 * ∑ i, κ i ^ 2

open Classical in
def chosenGrad (m : ℕ) (v : Space → Space) : Space → (Space →L[ℝ] Space) :=
  if h : ∃ G H, IsSecondOrderField m v G H then h.choose else fun _ => 0

open Classical in
def chosenSecond (m : ℕ) (v : Space → Space) : Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  if h : ∃ G H, IsSecondOrderField m v G H then h.choose_spec.choose else fun _ => 0

def toCertData (α : ℝ) : FracCertData k N :=
  { c.toFracCertData with
    modelForm := fun _ v κ => c.formOf α v (chosenGrad c.order v) (chosenSecond c.order v) κ
    modelField := fun _ v κ => c.modelFieldOf α v (chosenGrad c.order v) (chosenSecond c.order v) κ
    modelPin := fun _ v i => c.pinOf (chosenGrad c.order v) i }

end FracCellData

structure IsFracCertBase (α : ℝ) {k N : ℕ} (d : FracCertData k N) : Prop where
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

structure IsFracCell (α : ℝ) {k N : ℕ} (c : FracCellData k N) : Prop where
  base : IsFracCertBase α c.toFracCertData
  innerWeight_nonneg : 0 ≤ c.innerWeight
  innerWeight_le : c.innerWeight ≤ c.splitVisc
  cellRegion_measurable : MeasurableSet c.cellRegion
  cellRegion_bounded : Bornology.IsBounded c.cellRegion
  cellRegion_class : ∀ y ∈ c.cellRegion, turnStep c.order y ∈ c.cellRegion ∧ mirror y ∈ c.cellRegion
  cellWeight_measurable : Measurable c.cellWeight
  cellWeight_nonneg : ∀ y, 0 ≤ c.cellWeight y
  cellWeight_le : ∀ y, c.cellWeight y ≤ c.rowMax
  cellWeight_support : ∀ y ∉ c.cellRegion, c.cellWeight y = 0
  rows_dominated : ∀ F : Space → Space, MemLp F 2 volume →
    c.toFracCertData.rows F ^ 2 ≤ ∫ y, c.cellWeight y * ‖F y‖ ^ 2
  row_in_cells : ∀ a, ∀ y ∉ c.cellRegion, c.row a y = 0
  centre_smooth : ContDiff ℝ 1 c.centre
  centre_second : IsWeakSecondDerivOf c.centreGrad c.centreSecond ∧ AEStronglyMeasurable c.centreSecond volume
  centre_divergence : ∀ y, divergenceAt c.centre y = 0
  centre_class : IsClassField c.order c.centre
  centre_bounds : ∃ C : ℝ, ∀ y, ‖c.centre y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
    ‖c.centreGrad y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))
  model_measurable : AEStronglyMeasurable c.modelVelocity volume ∧ AEStronglyMeasurable c.modelCurl volume ∧
    AEStronglyMeasurable c.modelStrain volume ∧ AEStronglyMeasurable c.modelCurlGrad volume
  model_bounded : ∃ C : ℝ, ∀ y ∈ c.cellRegion, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C ∧
    ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C
  model_in_cells : ∀ y ∉ c.cellRegion, c.modelVelocity y = 0 ∧ c.modelCurl y = 0
  model_outside : ∀ y ∉ c.cellRegion, c.modelStrain y = c.centreStrain y ∧ c.modelCurlGrad y = c.centreCurlGrad y
  modelStrain_symmetric : ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)
  modelCurlGrad_trace : ∀ y, ∑ i : Fin 3, entry (c.modelCurlGrad y) i i = 0
  modelActuator_data : ∀ i, MemLp (c.modelActuator i) 2 volume ∧ ∀ y ∉ c.cellRegion, c.modelActuator i y = 0
  modelActuatorGrad_data : ∀ i, AEStronglyMeasurable (c.modelActuatorGrad i) volume ∧
    Integrable (fun y => entrySq (c.modelActuatorGrad i y)) ∧ ∀ y ∉ c.cellRegion, c.modelActuatorGrad i y = 0
  modelPin_data : ∀ i, AEStronglyMeasurable (c.modelPinField i) volume ∧
    Integrable (fun y => entrySq (c.modelPinField i y)) ∧ ∀ y ∉ c.cellRegion, c.modelPinField i y = 0
  actuator_gradient : ∀ i, IsWeakGradientOf (c.actuator i) (c.actuatorGrad i) ∧
    AEStronglyMeasurable (c.actuatorGrad i) volume ∧ Integrable (fun y => entrySq (c.actuatorGrad i y))
  actuator_in_cells : ∀ i, ∀ y ∉ c.cellRegion, c.actuator i y = 0
  pin_in_cells : ∀ i, ∀ y ∉ c.cellRegion, c.pin i y = 0
  form_nonneg : ∀ v G H, IsSecondOrderField c.order v G H → ∀ κ : Fin k → ℝ, ∀ Q, IsGradientField Q →
    IsClassField c.order Q → 0 ≤ c.quadForm α v G H κ Q
  centreLoss_bound : ∀ p ∈ box c.radius, ∀ v G H, IsSecondOrderField c.order v G H →
    l2Norm (fun y => (2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
      (fun z => c.gradProfile p z - c.centreGrad z) v G y) ≤ c.centreLoss * Real.sqrt (c.energy G H)
  rateLoss_bound : ∀ p ∈ box c.radius, ∀ v G H, IsSecondOrderField c.order v G H →
    c.toFracCertData.rows (fun y => (c.rotationRate p - c.modelRate) • (G y (axialTurn y) - axialTurn (v y)))
      ≤ c.rateLoss * Real.sqrt (c.energy G H)
  strainLoss_bound : ∀ y (u : Space), inner ℝ u (c.strainError y u) ≤ c.strainLoss * ‖u‖ ^ 2
  curlGradLoss_bound : ∀ v G H, IsSecondOrderField c.order v G H →
    Real.sqrt (∫ y, ‖c.curlGradError y‖ ^ 2 * ‖v y‖ ^ 2) ≤ c.curlGradLoss * Real.sqrt (∫ y, entrySq (G y))
  velocityLoss_bound : ∀ y, Real.sqrt (c.cellWeight y) * ‖c.velocityError y‖ ≤ c.velocityLoss
  curlLoss_bound : ∀ v G H, IsSecondOrderField c.order v G H →
    Real.sqrt (∫ y, c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2) ≤ c.curlLoss * Real.sqrt (∫ y, entrySq (G y))
  actuatorGradLoss_bound : ∑ i, (∫ y, entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y)) ≤ c.actuatorGradLoss ^ 2
  actuatorLoss_bound : ∑ i, c.toFracCertData.rows (fun y => c.actuator i y - c.modelActuator i y) ^ 2
    ≤ c.actuatorLoss ^ 2
  pinFieldLoss_bound : ∑ i, (∫ y, entrySq (c.pin i y - c.modelPinField i y)) ≤ c.pinFieldLoss ^ 2
  losses_nonneg' : 0 ≤ c.centreLoss ∧ 0 ≤ c.rateLoss ∧ 0 ≤ c.strainLoss ∧ 0 ≤ c.curlGradLoss ∧
    0 ≤ c.velocityLoss ∧ 0 ≤ c.curlLoss ∧ 0 ≤ c.actuatorGradLoss ∧ 0 ≤ c.actuatorLoss ∧ 0 ≤ c.pinFieldLoss
  potLoss_ge : c.centreLoss + (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) / c.weightMin
    + c.actuatorGradLoss / (2 * c.multiplierScale * Real.sqrt c.weightMin) ≤ c.potLoss
  rowLoss_ge : Real.sqrt c.rowMax * c.centreLoss + c.rateLoss
    + (c.velocityLoss + c.curlLoss) / Real.sqrt c.weightMin + c.actuatorLoss / c.multiplierScale ≤ c.rowLoss
  pinLoss_ge : c.pinFieldLoss / Real.sqrt c.weightMin ≤ c.pinLoss
  rowWeight_block : ∀ a b, c.blockIndex a = c.blockIndex b → c.rowWeight a = c.rowWeight b
  spectral_bound : ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
    smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, c.spectralBound (c.blockIndex b) lam * x b ^ 2
  baseCoef_nonneg : 0 ≤ c.baseCoef
  levelCoef_nonneg : ∀ i, 0 ≤ c.levelCoef i
  levelRate_pos : ∀ i, 0 < c.levelRate i
  cutoff_ge : c.splitVisc ^ (1 / (α - 1)) ≤ c.cutoff
  symbol_fit : ∀ x : ℝ, 0 < x → x ≤ c.cutoff → c.ratioSymbol α x ≤ c.levelSum x
  symbol_end : c.gapSymbol α c.cutoff ^ 2 / (c.gapSymbol α c.cutoff + c.reducedCoercivity) ≤ c.levelSum c.cutoff
  spectral_tail : ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam → c.spectralBound (c.blockIndex a) lam ≤ c.tailConst * lam ^ (-(1 / 2 : ℝ))
  splitBound_ge : ∀ a, c.rowWeight a * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex a) (c.levelRate i)
    + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) ≤ c.splitBound ^ 2

def FracCellCertificateHypothesis (α : ℝ) : Prop := ∃ (k N : ℕ) (c : FracCellData k N), IsFracCell α c

end CellCert

end Breakdown
