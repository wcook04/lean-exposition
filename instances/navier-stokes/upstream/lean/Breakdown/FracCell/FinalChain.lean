import Breakdown.FracCell.CertificateOfCell
import Breakdown.FracCell.SpectralAssembly
import Breakdown.FracCell.CellAnalysisAssembly
import Breakdown.FracCell.ExteriorPart
import Breakdown.FracCell.ExteriorNonneg
import Breakdown.FracCell.ExteriorPointwise
import Breakdown.FracCell.RayWeak
import Breakdown.FracCell.RaySmooth
import Breakdown.FracCell.RayLine
import Breakdown.Frac.Main
import Breakdown.FracCell.CellSystemFinalDefs
import Breakdown.FracCell.SystemBridgesMatrix
import Breakdown.FracCell.SystemBridgesSplit
import Breakdown.FracCell.SystemBridgesSums
import Breakdown.FracCell.GivenModelMixClauses
import Breakdown.FracCell.MeshDelayVanish
import Breakdown.FracCell.MeshRowFar
import Breakdown.FracCell.SystemBridgeAdjointDual
import Breakdown.FracCell.GivenAuxDual
import Breakdown.FracCell.SystemBridgeCentreKernel
import Breakdown.FracCell.SystemBridgeSumWeights
import Breakdown.FracCell.GivenProfileBounds
import Breakdown.FracCell.GivenProfileDrift
import Breakdown.FracCell.GivenProfilePower
import Breakdown.FracCell.CylinderComp
import Breakdown.FracCell.MeshAssembly
import Breakdown.FracCell.MeshEdgeJump
import Breakdown.FracCell.MeshFarCoef
import Breakdown.FracCell.MeshRootZero
import Breakdown.FracCell.MeshSkeleton
import Breakdown.FracCell.MeshStreamInd
import Breakdown.FracCell.GivenModelCover
import Breakdown.FracCell.GivenModelRowshapeOpen
import Breakdown.FracCell.ReductionFarFarFloor_of
import Breakdown.FracCell.ReductionFarTailBounds_of_columns
import Breakdown.FracCell.ReductionFarTurnBound_of
import Breakdown.FracCell.MeshGaugeLinear
import Breakdown.FracCell.MeshDataAffine
import Breakdown.FracCell.MeshMomentLinear
import Breakdown.FracCell.ReductionAdjointAdjointRepresentation
import Breakdown.FracCell.ReductionAdjointWeightedInverseSquare
import Breakdown.FracCell.ReductionAdjointFrameInverseSquare
import Breakdown.FracCell.ReductionAdjointAdjointLocal_of_dual
import Breakdown.FracCell.SystemBridgeAdjointKernel
import Breakdown.FracCell.SystemBridgeRowTurn
import Breakdown.FracCell.GivenProfileCentre
import Breakdown.FracCell.GivenProfileRate
import Breakdown.FracCell.GivenProfileSmooth
import Breakdown.FracCell.GivenAuxAdjoint
import Breakdown.FracCell.GivenAuxPin
import Breakdown.FracCell.GivenModelModel
import Breakdown.FracCell.GivenModelRegion
import Breakdown.FracCell.GivenModelRows
import Breakdown.FracCell.ReductionLossKernelBound_of_cellSums
import Breakdown.FracCell.GivenAuxActuator
import Breakdown.FracCell.GivenProfileCentreTrace
import Breakdown.FracCell.ReductionLossRowModeGradientParts
import Breakdown.FracCell.GivenModelRowTraces
import Breakdown.FracCell.GivenModelRowsInBlock
import Breakdown.FracCell.GivenModelRegular
import Breakdown.FracCell.GivenModelModelModes
import Breakdown.FracCell.GivenModelRowshape
import Breakdown.FracCell.ReductionPointwiseExtendBases_of
import Breakdown.FracCell.ReductionPointwiseOrthoFamily
import Breakdown.FracCell.ReductionPointwiseResolvedPointwise_of
import Breakdown.FracCell.ReductionPointwiseUnresolvedPointwise_of
import Breakdown.FracCell.ReductionPointwiseWeightClauses_of
import Breakdown.FracCell.ReductionLossProductConst_of_supNorm
import Breakdown.FracCell.ReductionLossSupNorm
import Breakdown.FracCell.ReductionLossAdjointQuad_of_potential
import Breakdown.FracCell.ReductionLossKernelPotential
import Breakdown.FracCell.ReductionLossCentreLoss_of_kernel
import Breakdown.FracCell.ReductionLossCurlGradLoss_of_kernel
import Breakdown.FracCell.ReductionLossCurlLoss_of_kernel
import Breakdown.FracCell.ReductionLossRateLoss_of_rows
import Breakdown.FracCell.ReductionLossStrainLoss_of_opNorm
import Breakdown.FracCell.ReductionAdjointAdjointSpread_of_power
import Breakdown.FracCell.ReductionAdjointPowerPairing
import Breakdown.FracCell.ReductionAdjointInverseSquareConst_two


open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.FinalChain

open SteadyCert Assembly _root_.Breakdown.CellCert.Finite

theorem order_bounds : (1 : ℝ) < 501 / 500 ∧ (501 / 500 : ℝ) < 5 / 4 := by
  constructor <;> norm_num

theorem breakdown_of_cellHypothesis (h : FracCellCertificateHypothesis (501 / 500)) :
    FractionalBreakdownOnSpace (501 / 500) ∧ FractionalBreakdownOnTorus (501 / 500) := by
  have hp := SteadyCert.fracCertificate_profile_proved (501 / 500) order_bounds.1 order_bounds.2
    (fracCertificateHypothesis_of_cell (501 / 500) order_bounds.1 order_bounds.2 h)
  exact ⟨fractional_breakdown_on_space_proved _ order_bounds.1 order_bounds.2 hp,
    fractional_breakdown_on_torus_proved _ order_bounds.1 order_bounds.2 hp⟩

structure IsCellRest (α : ℝ) {k N : ℕ} (c : FracCellData k N) : Prop where
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
  baseCoef_nonneg : 0 ≤ c.baseCoef
  levelCoef_nonneg : ∀ i, 0 ≤ c.levelCoef i
  levelRate_pos : ∀ i, 0 < c.levelRate i
  cutoff_ge : c.splitVisc ^ (1 / (α - 1)) ≤ c.cutoff
  symbol_fit : ∀ x : ℝ, 0 < x → x ≤ c.cutoff → c.ratioSymbol α x ≤ c.levelSum x
  symbol_end : c.gapSymbol α c.cutoff ^ 2 / (c.gapSymbol α c.cutoff + c.reducedCoercivity) ≤ c.levelSum c.cutoff
  splitBound_ge : ∀ a, c.rowWeight a * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex a) (c.levelRate i)
    + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) ≤ c.splitBound ^ 2

structure IsCellSplitRest (α : ℝ) {k N : ℕ} (c : FracCellData k N) (S : CellSplit k N) : Prop where
  cell_measurable : ∀ K, MeasurableSet (S.cell K)
  cells_apart : ∀ K L, K ≠ L → volume (S.cell K ∩ S.cell L) = 0
  cells_cover : (⋃ K, S.cell K) = c.cellRegion
  row_support : ∀ a, ∀ y ∉ S.cell (S.rowCell a), c.row a y = 0
  moment_zero : S.moment 0 = 0
  moment_additive : ∀ x x', IsAdmissible c x → IsAdmissible c x' → S.moment (x + x') = S.moment x + S.moment x'
  moment_homogeneous : ∀ (r : ℝ) x, IsAdmissible c x → S.moment (r • x) = r • S.moment x
  kappa_slot_injective : Function.Injective S.kappaSlot
  kappa_slot_value : ∀ x, IsAdmissible c x → ∀ i, S.moment x (S.kappaSlot i) = x.2.2.2.1 i
  kappa_slot_free : ∀ i j, S.freeMap (S.kappaSlot i) j = 0
  delay_vanish : ∀ j, ∀ x, IsAdmissible c x → ∀ ζ : Fin k → ℝ, quadValue (S.delayForm j) (S.stateOf x ζ) = 0

structure CellEntry (N k slots : ℕ) where
  box : CellAnalysis.CellBox
  scalars : CellAnalysis.CellScalars
  bases : CellAnalysis.CellBases
  classes : CellAnalysis.CellClasses
  rows : CellAnalysis.CellRows N slots k
  coords : CellCoordinates.CellCoords k slots

structure IsCellFacts (α : ℝ) {k N : ℕ} (c : FracCellData k N) (S : CellSplit k N) (K₂ : Fin S.cellCount)
    (r : CellEntry N k S.slots) : Prop where
  data : CellAnalysis.IsCellData α c r.box r.scalars r.bases r.classes r.rows
  coords : CellCoordinates.IsCellCoords α c S K₂ r.box r.scalars r.bases r.classes r.rows r.coords
  solid : S.cell K₂ =ᵐ[volume] r.box.solid
  rows_here : ∀ a, S.rowCell a = K₂ ↔ a ∈ r.rows.rowSet

theorem isFormData_of_rest {α : ℝ} {k N : ℕ} {c : FracCellData k N} (h : IsCellRest α c) : IsFormData α c where
  base := h.base
  cellRegion_bounded := h.cellRegion_bounded
  centre_bounds := h.centre_bounds
  model_measurable := h.model_measurable
  model_bounded := h.model_bounded
  model_outside := h.model_outside
  modelActuatorGrad_data := h.modelActuatorGrad_data
  modelPin_data := h.modelPin_data

theorem isFracCell_of_rest {α : ℝ} {k N : ℕ} {c : FracCellData k N} (h : IsCellRest α c)
    (hform : ∀ v G H, IsSecondOrderField c.order v G H → ∀ κ : Fin k → ℝ, ∀ Q, IsGradientField Q →
      IsClassField c.order Q → 0 ≤ c.quadForm α v G H κ Q)
    (hspec : ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, c.spectralBound (c.blockIndex b) lam * x b ^ 2)
    (htail : ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      c.spectralBound (c.blockIndex a) lam ≤ c.tailConst * lam ^ (-(1 / 2 : ℝ))) : IsFracCell α c where
  base := h.base
  innerWeight_nonneg := h.innerWeight_nonneg
  innerWeight_le := h.innerWeight_le
  cellRegion_measurable := h.cellRegion_measurable
  cellRegion_bounded := h.cellRegion_bounded
  cellRegion_class := h.cellRegion_class
  cellWeight_measurable := h.cellWeight_measurable
  cellWeight_nonneg := h.cellWeight_nonneg
  cellWeight_le := h.cellWeight_le
  cellWeight_support := h.cellWeight_support
  rows_dominated := h.rows_dominated
  row_in_cells := h.row_in_cells
  centre_smooth := h.centre_smooth
  centre_second := h.centre_second
  centre_divergence := h.centre_divergence
  centre_class := h.centre_class
  centre_bounds := h.centre_bounds
  model_measurable := h.model_measurable
  model_bounded := h.model_bounded
  model_in_cells := h.model_in_cells
  model_outside := h.model_outside
  modelStrain_symmetric := h.modelStrain_symmetric
  modelCurlGrad_trace := h.modelCurlGrad_trace
  modelActuator_data := h.modelActuator_data
  modelActuatorGrad_data := h.modelActuatorGrad_data
  modelPin_data := h.modelPin_data
  actuator_gradient := h.actuator_gradient
  actuator_in_cells := h.actuator_in_cells
  pin_in_cells := h.pin_in_cells
  centreLoss_bound := h.centreLoss_bound
  rateLoss_bound := h.rateLoss_bound
  strainLoss_bound := h.strainLoss_bound
  curlGradLoss_bound := h.curlGradLoss_bound
  velocityLoss_bound := h.velocityLoss_bound
  curlLoss_bound := h.curlLoss_bound
  actuatorGradLoss_bound := h.actuatorGradLoss_bound
  actuatorLoss_bound := h.actuatorLoss_bound
  pinFieldLoss_bound := h.pinFieldLoss_bound
  losses_nonneg' := h.losses_nonneg'
  potLoss_ge := h.potLoss_ge
  rowLoss_ge := h.rowLoss_ge
  pinLoss_ge := h.pinLoss_ge
  rowWeight_block := h.rowWeight_block
  baseCoef_nonneg := h.baseCoef_nonneg
  levelCoef_nonneg := h.levelCoef_nonneg
  levelRate_pos := h.levelRate_pos
  cutoff_ge := h.cutoff_ge
  symbol_fit := h.symbol_fit
  symbol_end := h.symbol_end
  splitBound_ge := h.splitBound_ge
  form_nonneg := hform
  spectral_bound := hspec
  spectral_tail := htail

theorem isFracCell_of_layers {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (h : IsCellRest α c) (S : CellSplit k N) (hS : S.IsCellSplit c α) (T : Finite.TreeCertificate S.slots k)
    (hT : Finite.IsTreeCertificate T)
    (hcells : ∃ e : T.Cell ≃ Fin S.cellCount ⊕ Fin S.delayCount,
      ∀ K, T.cellForm K = Sum.elim S.cellMatrix S.delayForm (e K))
    (hglobal : T.globalForm = S.globalMatrix c) (sd : Spectral.SpectralData) (hsd : Spectral.IsSpectralData c sd)
    (hsb : c.spectralBound = sd.blockSpectral)
    (htail : ∀ a, sd.tailFormula c.cutoff (c.blockIndex a) ≤ c.tailConst) : IsFracCell α c := by
  have hblocks := Spectral.spectral_of_blocks c sd hsd
  refine isFracCell_of_rest h
    (formNonneg_of_tree α hα₁ hα₂ c (isFormData_of_rest h) S hS T hT hcells hglobal) ?_ ?_
  · rw [hsb]
    exact hblocks.1
  · intro a lam hlam
    rw [hsb]
    have hlam0 : 0 ≤ lam := le_trans hsd.cutoff_pos.le hlam
    exact le_trans (hblocks.2 a lam hlam)
      (mul_le_mul_of_nonneg_right (htail a) (Real.rpow_nonneg hlam0 _))

theorem isCellSplit_of_cells
    {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c)
    (S : CellSplit k N) (hS : IsCellSplitRest α c S) (e : Exterior.ExteriorData) (he : Exterior.IsExteriorData α c e)
    (cell : Fin S.cellCount → CellEntry N k S.slots) (hcell : ∀ K₂, IsCellFacts α c S K₂ (cell K₂)) :
    S.IsCellSplit c α where
  cell_measurable := hS.cell_measurable
  cells_apart := hS.cells_apart
  cells_cover := hS.cells_cover
  row_support := hS.row_support
  moment_zero := hS.moment_zero
  moment_additive := hS.moment_additive
  moment_homogeneous := hS.moment_homogeneous
  kappa_slot_injective := hS.kappa_slot_injective
  kappa_slot_value := hS.kappa_slot_value
  kappa_slot_free := hS.kappa_slot_free
  delay_vanish := hS.delay_vanish
  cell_bound := fun K₂ => CellCoordinates.cellBound_closed
    α hα₁ hα₂ c hc S hS.kappa_slot_value hS.kappa_slot_free K₂ (cell K₂).box (cell K₂).scalars (cell K₂).bases
    (cell K₂).classes (cell K₂).rows (hcell K₂).data (cell K₂).coords (hcell K₂).coords (hcell K₂).solid
    (hcell K₂).rows_here
  exterior_bound := Exterior.exteriorPartNonneg_of
    (Exterior.exteriorNonneg_of (Exterior.rayWeak_of (Exterior.raySmooth_of Exterior.rayLine)) Exterior.exteriorPointwise)
    α hα₁ hα₂ c hc e he S hS.cells_cover

theorem breakdown_of_layers
    {k N : ℕ} (c : FracCellData k N) (h : IsCellRest (501 / 500) c)
    (S : CellSplit k N) (hS : IsCellSplitRest (501 / 500) c S)
    (e : Exterior.ExteriorData) (he : Exterior.IsExteriorData (501 / 500) c e)
    (cell : Fin S.cellCount → CellEntry N k S.slots) (hcell : ∀ K₂, IsCellFacts (501 / 500) c S K₂ (cell K₂))
    (T : TreeCertificate S.slots k) (hT : IsTreeCertificate T)
    (hcells : ∃ eq : T.Cell ≃ Fin S.cellCount ⊕ Fin S.delayCount,
      ∀ K, T.cellForm K = Sum.elim S.cellMatrix S.delayForm (eq K))
    (hglobal : T.globalForm = S.globalMatrix c) (sd : Spectral.SpectralData) (hsd : Spectral.IsSpectralData c sd)
    (hsb : c.spectralBound = sd.blockSpectral)
    (htail : ∀ a, sd.tailFormula c.cutoff (c.blockIndex a) ≤ c.tailConst) :
    FractionalBreakdownOnSpace (501 / 500) ∧ FractionalBreakdownOnTorus (501 / 500) :=
  breakdown_of_cellHypothesis ⟨k, N, c, isFracCell_of_layers order_bounds.1 order_bounds.2 c h S
    (isCellSplit_of_cells order_bounds.1 order_bounds.2 c
      (isFormData_of_rest h) S hS e he cell hcell) T hT hcells hglobal sd hsd hsb htail⟩

end Breakdown.CellCert.FinalChain

namespace Breakdown.CellCert.FinalCellSystem

open CellSystem

section

open MeasureTheory
open scoped Matrix
open CellSystem

open SteadyCert Assembly Reduction GivenModel CellAnalysis

namespace CellDataBoxInternal

theorem scalars_of {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData)
    (aS lowConst s₀ g₀ w₀ : ℝ) (hK : IsCellBox K) (hF : IsWeightForm c K S W)
    (hT : IsWeightTests (501 / 500) c K S W) (hR : IsResolvedTests (501 / 500) c S W aS lowConst)
    (hz : ∀ n ∉ S.resolved, ∀ p, S.localMatrix n p = 0)
    (hs : S.strainBound = fun _ => s₀) (hg : S.meanGradBound = fun _ => g₀) (hw : S.waveGradBound = fun _ => w₀)
    (hax : K.IsAxis → W.J = 0) (hdeg : 3 ≤ S.degLow ∧ S.degLow + 2 ≤ S.degHigh ∧ S.degHigh + 1 ≤ S.degNear)
    (hgn : 0 ≤ g₀ ∧ 0 ≤ w₀)
    (hsl : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ θ : ℝ, ∀ u : Space,
      inner ℝ (c.modelStrain (cylPoint p.1 θ p.2) u) u ≤ s₀ * ‖u‖ ^ 2) :
    IsCellScalars (501 / 500) c K S := by
  obtain ⟨hul, hep, hel, hvn, hvl, hsym, htn, htz, hsw, haw, hvw⟩ :=
    weightClauses_of (501 / 500) c K S W hK hF hT
  obtain ⟨hloc, hres⟩ := resolvedPointwise_of (501 / 500) c K S W aS lowConst hK hF hT hR
  have hdr := scalarsRegular_of_const K hK S (fun _ => strainScalarMatrix aS) hR.local_form s₀ g₀ w₀ hs hg hw
  refine
  { resolved_symm := ?_
    band_symm := ?_
    zero_resolved := ?_
    disjoint := ?_
    axis_resolved := ?_
    unresolved_large := hul
    splitLength_pos := hT.splitLength_pos
    strain_le := fun p hp h0 θ u => by rw [hs]; exact hsl p hp h0 θ u
    data_regular := hdr
    grad_bounds_nonneg := fun _ => by rw [hg, hw]; exact hgn
    energyWeight_pos := hep
    energyWeight_le := hel
    vorticityWeight_nonneg := hvn
    vorticityWeight_le := hvl
    weights_symm := hsym
    localMatrix_selfAdjoint := ?_
    localMatrix_le := hloc
    resolved_pointwise := hres
    unresolved_pointwise := unresolvedPointwise_of (501 / 500) c K S W hK hF hT
    tailShift_nonneg := htn
    tailShift_zero := htz
    weightFloor_pos := hT.floor_pos
    sym_weight := hsw
    anti_weight := haw
    vel_weight := hvw
    degrees := hdeg }
  · intro n
    rw [hF.resolved_eq]
    simp only [Finset.mem_Icc]
    omega
  · intro n
    rw [hF.band_eq]
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    push_cast
    omega
  · rw [hF.resolved_eq]
    simp
  · rw [hF.band_eq, hF.resolved_eq]
    exact Finset.disjoint_sdiff
  · intro h
    rw [hF.resolved_eq, hax h]
    simp
  · intro n p
    by_cases hn : n ∈ S.resolved
    · rw [hR.local_form n hn p]
      show (Matrix.diagonal _)ᴴ = Matrix.diagonal _
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      simp only [Pi.star_apply]
      split_ifs <;> simp
    · rw [hz n hn p]
      exact Matrix.isHermitian_zero

end CellDataBoxInternal

theorem cellDataBox_holds : CellDataBoxStatement := by
  intro k N c D A M MD RD X h K₂
  have hf := h.cells K₂
  have hK : IsCellBox (X.cell K₂).box := h.given.mesh.boxes (X.cell K₂).meshCell
  exact ⟨hK,
    CellDataBoxInternal.scalars_of c _ _ _ _ _ _ _ _ hK hf.weight_form hf.weight_tests hf.resolved_tests
      hf.local_zero hf.strain_const hf.mean_const hf.wave_const hf.axis_resolved_test hf.degrees
      hf.grad_consts_nonneg hf.strain_le,
    (extendBases_of orthoFamily_spec _ _ _ hK hf.given_bases).1⟩

end

section

open MeasureTheory
open CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior CellAnalysis CellCoordinates
open Breakdown.FracInternal.GivenModelModelFrame Breakdown.FracInternal.GivenModelModelModes

private theorem model_mirror_of_instance {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hI : IsModelInstance c M D) (K : CellBox) (hK : K.solid ⊆ c.cellRegion) :
    ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
      c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
      (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
      (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
      ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
        (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u))) := by
  intro y hy hz
  have hyR : y ∈ M.region := hI.region_eq ▸ hK hy
  have hmR : mirror y ∈ M.region := (mem_region_mirror M y).2 hyR
  have hyC : y ∉ M.regionᶜ := fun h => h hyR
  have hmC : mirror y ∉ M.regionᶜ := fun h => h hmR
  refine ⟨?_, ?_, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hI.velocity_eq]
    unfold ModelData.velocityField
    rw [piecewise_mirror_vec M _ _ 1 y (fun K _ => vectorOf_mirror _ _ hz), one_smul]
  · rw [hI.curl_eq]
    unfold ModelData.curlField
    rw [piecewise_mirror_vec M _ _ (-1) y (fun K _ => pseudoOf_mirror _ _ hz), neg_one_smul]
  · intro u
    rw [hI.strain_eq]
    unfold ModelData.strainField
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      Set.indicator_of_notMem hmC, Set.indicator_of_notMem hyC,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, add_zero, add_zero,
      piecewise_mirror_op M _ _ 1 y (fun K _ u => tensorOf_mirror _ _ hz u) u, one_smul]
  · intro u
    rw [hI.curlGrad_eq]
    unfold ModelData.curlGradField
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      Set.indicator_of_notMem hmC, Set.indicator_of_notMem hyC,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, add_zero, add_zero,
      piecewise_mirror_op M _ _ (-1) y (fun K _ u => pseudoTensorOf_mirror _ _ hz u) u, neg_one_smul]
  · intro u
    rw [hI.actuatorGrad_eq i]
    unfold ModelData.actuatorGradField
    rw [piecewise_mirror_op M _ _ 1 y (fun K _ u => tensorOf_mirror _ _ hz u) u, one_smul]
  · intro u
    rw [hI.pinField_eq i]
    unfold ModelData.pinFieldField
    rw [piecewise_mirror_op M _ _ 1 y (fun K _ u => tensorOf_mirror _ _ hz u) u, one_smul]

theorem cellDataModel_of (hCst : CentreSmoothOfStatement) (hC2 : CentreSecondOfStatement)
    (hCSy : CentreSecondSymmOfStatement) (hMo : ModelClausesStatement) (hMA : ModelAuxClausesStatement) :
    CellDataModelStatement := by
  intro k N c D A M MD RD X h K₂
  have hS := h.given
  have hF := h.cells K₂
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  have hCR' : IsCentreRegular c :=
    ⟨hCst D c hS.profile hS.centre_instance, (hC2 D c hS.profile hS.centre_instance).2,
      hCSy D c hS.profile hS.centre_instance⟩
  obtain ⟨-, -, -, -, mSym, mTr⟩ := hMo c M MD hS.mesh hS.model hS.model_instance hCR'
  obtain ⟨maAct, -, -, -, -⟩ := hMA c M MD hS.mesh hS.model_instance
  have hsolid : (X.cell K₂).box.solid ⊆ c.cellRegion :=
    solidInRegion_of c M RD (X.cell K₂).meshCell (X.cell K₂).rows hF.rows_instance
  have hbox : IsCellBox (X.cell K₂).box := hS.mesh.boxes (X.cell K₂).meshCell
  exact {
    weight_axisymmetric := fun p hp θ => (weight_clauses c X.weightValue h.inst.weight_eq h.inst.weightValue_pos
      h.inst.weightMin_eq h.inst.weightMax_eq).2.2.2.2.2 _ p hp θ
    model_mirror := model_mirror_of_instance c M MD hS.model_instance _ hsolid
    solid_in_region := hsolid
    model_strain_symm := mSym
    actuator_memLp := fun i => (maAct i).1
    curlGrad_traceFree := fun _ _ _ _ => mTr _
    class_regular := classesRegular_of_affine _ hbox _ _ _ _ _ _ _ _ _
      (fun i p => (hF.dev_affine i p).1) (fun i p => (hF.dev_affine i p).2.1)
      (fun i p => (hF.dev_affine i p).2.2.1) (fun i p => (hF.dev_affine i p).2.2.2)
    linear_modes := by
      intro n hn p _ hp1 i
      have hβ : ∀ β : Fin (MD.harmonicCount + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n := fun β =>
        ⟨fun e => hn (e ▸ (hF.harmonics_in_yModes β).1), fun e => hn (e ▸ (hF.harmonics_in_yModes β).2)⟩
      refine ⟨?_, ?_⟩
      · rw [hS.model_instance.actuatorGrad_eq i]
        exact modes_zero M c.order hm (MD.actuatorGrad i) p.1 p.2 hp1 n hβ
      · rw [hS.model_instance.pinField_eq i]
        exact modes_zero M c.order hm (MD.pinField i) p.1 p.2 hp1 n hβ }

end

section

open CellSystem

open GivenModel

theorem cellDataRows_holds : CellDataRowsStatement := by
  intro k N c D A M MD RD X h K₂
  have hI := (h.cells K₂).rows_instance
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  exact {
    rows_in_cell := rowsInCell_of c M RD _ _ h.given.mesh h.given.rows hI
    row_modes := rowModes_of c M RD _ _ h.given.mesh h.given.rows hI hm
    row_mode_of := rowModeOf_of c M RD _ _ h.given.mesh h.given.rows hI hm
    rowWeight_pos := fun a _ => by
      rw [h.given.rows_instance.rowWeight_eq]
      exact h.given.rows.cellWeight_pos _ }

end

section

open MeasureTheory
open CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior CellAnalysis CellCoordinates

private lemma null_of_escape {C S : Set Space} (hC : Convex ℝ C) (hS : S ⊆ C) (v : Space → Space)
    (hv : ∀ y ∈ S, ∀ t : ℝ, 0 < t → y + t • v y ∉ C) : volume S = 0 := by
  refine measure_mono_null ?_ (hC.addHaar_frontier volume)
  intro y hy
  refine ⟨subset_closure (hS hy), fun hint => ?_⟩
  have hcont : Continuous fun t : ℝ => y + t • v y := by fun_prop
  have hmem : interior C ∈ nhds ((fun t : ℝ => y + t • v y) 0) := by
    show interior C ∈ nhds (y + (0 : ℝ) • v y)
    rw [zero_smul, add_zero]
    exact isOpen_interior.mem_nhds hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont.continuousAt.preimage_mem_nhds hmem)
  have hhalf : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  exact hv y hy (ε / 2) (by positivity) (interior_subset (hball hhalf))

private lemma coord_null (i : Fin 3) (a : ℝ) : volume {y : Space | y i = a} = 0 := by
  refine null_of_escape (C := {y : Space | y i ≤ a}) ?_ (fun y hy => le_of_eq hy)
    (fun _ => EuclideanSpace.single i 1) ?_
  · intro x hx y hy p q hp hq hpq
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    have e : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
    linarith [mul_le_mul_of_nonneg_left hx hp, mul_le_mul_of_nonneg_left hy hq]
  · intro y hy t ht hmem
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.single_apply, if_true, mul_one] at hy hmem
    linarith

private lemma radius_null (c : ℝ) : volume {y : Space | cylRadius y = c} = 0 := by
  have hsplit : {y : Space | cylRadius y = c} ⊆
      {y : Space | cylRadius y = c ∧ 0 < y 0 ^ 2 + y 1 ^ 2} ∪ {y : Space | y 0 = 0} := by
    intro y hy
    rcases (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))).lt_or_eq with h | h
    · exact Or.inl ⟨hy, h⟩
    · right
      show y 0 = 0
      nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  refine measure_mono_null hsplit (measure_union_null ?_ (coord_null 0 0))
  refine null_of_escape (C := {y : Space | y 0 ^ 2 + y 1 ^ 2 ≤ c ^ 2}) ?_ ?_
    (fun y => EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1)) ?_
  · intro x hx y hy p q hp hq hpq
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    have hP : 2 * (x 0 * y 0 + x 1 * y 1) ≤ 2 * c ^ 2 := by
      nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
    have hpq2 : (p + q) ^ 2 = 1 := by rw [hpq]; norm_num
    have e : (p * x 0 + q * y 0) ^ 2 + (p * x 1 + q * y 1) ^ 2 =
        p ^ 2 * (x 0 ^ 2 + x 1 ^ 2) + p * q * (2 * (x 0 * y 0 + x 1 * y 1)) + q ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
      ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hx (sq_nonneg p)
    have h2 := mul_le_mul_of_nonneg_left hy (sq_nonneg q)
    have h3 := mul_le_mul_of_nonneg_left hP (mul_nonneg hp hq)
    nlinarith
  · rintro y ⟨hy, -⟩
    show y 0 ^ 2 + y 1 ^ 2 ≤ c ^ 2
    rw [← hy]
    unfold cylRadius
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  · rintro y ⟨hy, hpos⟩ t ht hmem
    have hc : c ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      rw [← hy]
      unfold cylRadius
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.single_apply] at hmem
    norm_num at hmem
    rw [hc] at hmem
    nlinarith [mul_pos ht hpos, mul_pos (mul_pos ht ht) hpos]

private lemma height_null (c : ℝ) : volume {y : Space | |cylHeight y| = c} = 0 := by
  refine measure_mono_null ?_ (measure_union_null (coord_null 2 c) (coord_null 2 (-c)))
  intro y hy
  have hy' : |y 2| = c := hy
  rcases abs_eq_abs.mp (hy'.trans (abs_of_nonneg (hy' ▸ abs_nonneg _)).symm) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem solid_inter_null (K L : CellBox)
    (h : K.r₂ ≤ L.r₁ ∨ L.r₂ ≤ K.r₁ ∨ K.z₂ ≤ L.z₁ ∨ L.z₂ ≤ K.z₁) :
    volume (K.solid ∩ L.solid) = 0 := by
  rcases h with h | h | h | h
  · refine measure_mono_null ?_ (radius_null K.r₂)
    rintro y ⟨hK, hL⟩
    exact le_antisymm hK.2.1 (h.trans hL.1)
  · refine measure_mono_null ?_ (radius_null L.r₂)
    rintro y ⟨hK, hL⟩
    exact le_antisymm hL.2.1 (h.trans hK.1)
  · refine measure_mono_null ?_ (height_null K.z₂)
    rintro y ⟨hK, hL⟩
    exact le_antisymm hK.2.2.2 (h.trans hL.2.2.1)
  · refine measure_mono_null ?_ (height_null L.z₂)
    rintro y ⟨hK, hL⟩
    exact le_antisymm hL.2.2.2 (h.trans hK.2.2.1)

theorem cellsApart_holds : CellsApartStatement := by
  intro k N c D A M MD RD X h K L hKL
  rw [h.inst.cell_solid K, h.inst.cell_solid L]
  have hne : (X.cell K).meshCell ≠ (X.cell L).meshCell := fun e => hKL (h.inst.cell_bijective.1 e)
  exact solid_inter_null _ _ (h.given.mesh.interiors_disjoint _ _ hne)

theorem rowsInCellOf_holds : RowsInCellOfStatement := by
  intro k N slots c M RD K₀ R hM hR hI
  exact rowsInCell_of c M RD K₀ R hM hR hI

end

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

theorem givenParts_of_system (hRR : RotationRateContinuousOfStatement) (hMC : MultiplierContinuousOfStatement)
    (hPS : ProfileSmoothOfStatement) (hP2 : ProfileSecondOfStatement) (hPDv : ProfileDivergenceOfStatement)
    (hPC : ProfileClassOfStatement) (hPB : ProfileBoundsOfStatement) (hPDr : ProfileDriftOfStatement)
    (hPP : ProfilePowerOfStatement) (hPCo : ProfileContinuousOfStatement) (hCst : CentreSmoothOfStatement)
    (hC2 : CentreSecondOfStatement) (hCD : CentreDivergenceOfStatement) (hCC : CentreClassOfStatement)
    (hCB : CentreBoundsOfStatement) (hCSy : CentreSecondSymmOfStatement) (hAc : ActuatorOfGivenStatement)
    (hAG : ActuatorGradientOfGivenStatement) (hASu : ActuatorSupportOfGivenStatement)
    (hSP : SmoothPinOfGivenStatement) (hAS : AdjointSolenoidalOfGivenStatement)
    (hAR : AdjointRegularOfGivenStatement) (hDC : AdjointDualCoreOfGivenStatement)
    (hSR : SupportRegionOfStatement) (hCR : CellRegionClausesStatement) (hMo : ModelClausesStatement)
    (hMA : ModelAuxClausesStatement) (hRo : RowClausesStatement) (hWC : WeightClausesStatement)
    (hEC : ExteriorClausesStatement) (hBR : BallSubsetRegionStatement) (hTF : CentreTraceFreeOfStatement)
    {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X) :
    IsGivenBase (501 / 500) c.toFracCertData ∧ IsGivenCell c ∧ IsGivenExterior (501 / 500) c X.exterior ∧
      IsGivenExtra c.toFracCertData ∧ ∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0 := by
  have hS := h.given
  have hP := hS.profile.chart
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  have hord : c.order = D.chart.m := hS.profile_instance.order_eq
  obtain ⟨wMeas, wPos, wLow, wUp, wCl, -⟩ := hWC c X.weightValue h.inst.weight_eq h.inst.weightValue_pos
    h.inst.weightMin_eq h.inst.weightMax_eq
  obtain ⟨rTwo, rOrth, rSupp, rCl, rwPos, rwLe, rIn, cwMeas, cwNonneg, cwLe, cwSupp, rDom⟩ :=
    hRo c M RD hS.mesh hS.rows hS.rows_instance hm
  have hCR' : IsCentreRegular c :=
    ⟨hCst D c hS.profile hS.centre_instance, (hC2 D c hS.profile hS.centre_instance).2,
      hCSy D c hS.profile hS.centre_instance⟩
  obtain ⟨mMeas, mBdd, mIn, mOut, mSym, mTr⟩ := hMo c M MD hS.mesh hS.model hS.model_instance hCR'
  obtain ⟨maAct, maGrad, maPin, pinData, pinIn⟩ := hMA c M MD hS.mesh hS.model_instance
  obtain ⟨crMeas, crBdd, crCl⟩ := hCR c M hS.mesh hS.model_instance.region_eq
  obtain ⟨eMeas, ePos, eBetween, eHom, eEq⟩ := hEC c M hS.mesh hS.model_instance.region_eq X.exterior
    h.inst.exterior_radius h.inst.exterior_radiusMin h.inst.exterior_radiusMax
  have hAct := hAc D.chart hP A hS.aux c.toFracCertData hord hS.aux_instance.actuator_eq
  have hPSm := hPS D c.toFracCertData hS.profile hS.profile_instance
  have hPDiv := hPDv D c.toFracCertData hS.profile hS.profile_instance
  have hPBd := hPB D c.toFracCertData hS.profile hS.profile_instance
  have hregion : ∀ y ∉ c.cellRegion, ∀ i, c.actuator i y = 0 := by
    intro y hy i
    rw [hS.aux_instance.actuator_eq i]
    exact hASu D.chart hP A hS.aux c.cellRegion
      (hSR D.chart hP A hS.aux c.cellRegion M.outerSize
        (fun z hz => hS.model_instance.region_eq ▸ hBR M hS.mesh z hz) h.inst.support_inside) i y hy
  refine ⟨?_, ?_, ?_, ?_, rOrth⟩
  · exact {
      weight_measurable := wMeas
      weightMin_pos := wPos
      weight_lower := wLow
      weight_upper := wUp
      weight_class := wCl
      rotationRate_continuous := hRR D c.toFracCertData hS.profile hS.profile_instance
      multiplier_continuous := hMC D c.toFracCertData hS.profile hS.profile_instance
      profile_smooth := hPSm
      profile_second := hP2 D c.toFracCertData hS.profile hS.profile_instance
      profile_divergence := hPDiv
      profile_class := hPC D c.toFracCertData hS.profile hS.profile_instance
      profile_bounds := hPBd
      profile_drift := hPDr (501 / 500) D c.toFracCertData hS.profile hS.profile_instance h.inst.power_eq.symm
      profile_power := hPP (501 / 500) D c.toFracCertData hS.profile hS.profile_instance h.inst.power_eq.symm
      profile_continuous := hPCo D c.toFracCertData hS.profile hS.profile_instance
      actuator_two := hAct.1
      actuator_class := hAct.2
      pin_measurable := fun i => ⟨(pinData i).1, by
        rw [hS.aux_instance.smoothPin_eq i]; exact (hSP D.chart hP A hS.aux i).1⟩
      pin_two := fun i => ⟨(pinData i).2, by
        rw [hS.aux_instance.smoothPin_eq i]; exact (hSP D.chart hP A hS.aux i).2.1⟩
      row_two := rTwo
      row_orthonormal := rOrth
      row_support := rSupp
      row_class := rCl
      rowWeight_pos := rwPos
      rowWeight_le := rwLe
      adjoint_solenoidal := hAS D.chart hP A hS.aux c.toFracCertData hord hS.aux_instance.adjoint_eq
        hS.aux_instance.adjointSharp_eq }
  · exact {
      cellRegion_measurable := crMeas
      cellRegion_bounded := crBdd
      cellRegion_class := crCl
      cellWeight_measurable := cwMeas
      cellWeight_nonneg := cwNonneg
      cellWeight_le := cwLe
      cellWeight_support := cwSupp
      rows_dominated := rDom
      row_in_cells := rIn
      centre_smooth := hCst D c hS.profile hS.centre_instance
      centre_second := hC2 D c hS.profile hS.centre_instance
      centre_divergence := hCD D c hS.profile hS.centre_instance
      centre_class := hCC D c hS.profile hS.centre_instance
      centre_bounds := hCB D c hS.profile hS.centre_instance
      model_measurable := mMeas
      model_bounded := mBdd
      model_in_cells := mIn
      model_outside := mOut
      modelStrain_symmetric := mSym
      modelCurlGrad_trace := mTr
      modelActuator_data := maAct
      modelActuatorGrad_data := maGrad
      modelPin_data := maPin
      actuator_gradient := fun i => by
        rw [hS.aux_instance.actuator_eq i, hS.aux_instance.actuatorGrad_eq i]
        exact hAG D.chart hP A hS.aux i
      actuator_in_cells := fun i y hy => hregion y hy i
      pin_in_cells := pinIn }
  · exact {
      radius_measurable := eMeas
      radiusMin_pos := ePos
      radius_between := eBetween
      radius_homogeneous := eHom
      exterior_eq := eEq
      curlGrad_traceFree := fun y _ => hTF D c hS.profile hS.centre_instance y }
  · refine ⟨?_, ?_, ?_⟩
    · intro j _ p _
      rw [hS.aux_instance.adjoint_eq j p]
      exact (hDC D.chart hP A hS.aux 1 j p).2.1.1
    · intro p hp
      obtain ⟨C, hC⟩ := hPBd
      refine ⟨hPSm p hp, hPDiv p hp, C, fun y => ⟨?_, ?_⟩⟩
      · simpa [Real.rpow_neg_one] using (hC p hp y).1
      · simpa using (hC p hp y).2.1
    · intro j _ p _
      rw [hS.aux_instance.adjoint_eq j p]
      exact ⟨hAR D.chart hP A hS.aux j p, (hDC D.chart hP A hS.aux 1 j p).2.1.1⟩

theorem cellRest_of_system (hKB : KernelBoundOfCellSumsStatement) (hRM : RowModeGradientStatement)
    (hAL : AdjointLocalOfDualStatement) (hTD : RowTurnDataOfStatement) (hSW : SumWeightsOfStatement)
    (hADS : AdjointDualStructureOfStatement) (hCK : CentreKernelSplitOfStatement) (hAK : AdjointKernelOfStatement)
    {k N : ℕ} (c : FracCellData k N) (D : ProfileData k)
    (A : AuxData k) (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X)
    (hSB : IsGivenBase (501 / 500) c.toFracCertData) (hSC : IsGivenCell c) (hSX : IsGivenExtra c.toFracCertData) :
    FinalChain.IsCellRest (501 / 500) c where
  base := {
    order_ge := h.base.order_ge
    coercivity_pos := h.base.coercivity_pos
    coercivity_lt := h.base.coercivity_lt
    pinWeight_pos := h.base.pinWeight_pos
    rowMax_pos := h.base.rowMax_pos
    multiplierScale_pos := h.base.multiplierScale_pos
    weight_measurable := hSB.weight_measurable
    weightMin_pos := hSB.weightMin_pos
    weight_lower := hSB.weight_lower
    weight_upper := hSB.weight_upper
    weight_class := hSB.weight_class
    radius_nonneg := h.base.radius_nonneg
    slope_ne_zero := h.base.slope_ne_zero
    ellipsoidRadius_nonneg := h.base.ellipsoidRadius_nonneg
    ellipsoid_le := h.base.ellipsoid_le
    frame_near := h.base.frame_near
    frameDefect_lt := h.base.frameDefect_lt
    rotationRate_continuous := hSB.rotationRate_continuous
    multiplier_continuous := hSB.multiplier_continuous
    profile_smooth := hSB.profile_smooth
    profile_second := hSB.profile_second
    profile_divergence := hSB.profile_divergence
    profile_class := hSB.profile_class
    profile_bounds := hSB.profile_bounds
    profile_drift := hSB.profile_drift
    profile_power := hSB.profile_power
    profile_continuous := hSB.profile_continuous
    actuator_two := hSB.actuator_two
    actuator_class := hSB.actuator_class
    pin_measurable := hSB.pin_measurable
    pin_two := hSB.pin_two
    pinGap_bound := h.base.pinGap_bound
    pinGap_nonneg := h.base.pinGap_nonneg
    row_two := hSB.row_two
    row_orthonormal := hSB.row_orthonormal
    row_support := hSB.row_support
    row_class := hSB.row_class
    rowWeight_pos := hSB.rowWeight_pos
    rowWeight_le := hSB.rowWeight_le
    losses_nonneg := h.base.losses_nonneg
    reduced_pos := h.base.reduced_pos
    reduced_le := h.base.reduced_le
    lowLoss_bound := h.base.lowLoss_bound
    reducedGap_pos := h.base.reducedGap_pos
    formScale_nonneg := h.base.formScale_nonneg
    formScale_bound := h.base.formScale_bound
    splitBound_nonneg := h.base.splitBound_nonneg
    contraction_lt := h.base.contraction_lt
    productConst_nonneg := h.base.productConst_nonneg
    productConst_bound := productConst_of_supNorm supNorm c.toFracCertData hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper h.losses.productConst_ge
    defect_norm := h.base.defect_norm
    defect_rows := h.base.defect_rows
    size_ge := h.base.size_ge
    size_small := h.base.size_small
    adjoint_solenoidal := hSB.adjoint_solenoidal
    adjoint_local := hAL 2 (501 / 500) FinalChain.order_bounds.1 FinalChain.order_bounds.2 c.toFracCertData (inverseSquareConst_two _) hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper hSX.profile_decay (fun j hj p hp => (hSB.adjoint_solenoidal j hj p hp).1) (fun j p => adjointDualOf (501 / 500) D c.toFracCertData A c.splitVisc j p (X.adjointNumbers j p)) (fun j hj p hp => isAdjointDual_of_parts _ _ j p _ (h.losses.adjoint_numbers j hj p hp) (hADS c D A M MD RD h.given h.inst.power_eq h.losses.amp_index (X.adjointNumbers j p) j p)) h.losses.adjointLocal_ge
    adjoint_spread := adjointSpread_of_power powerPairing (501 / 500) FinalChain.order_bounds.1 FinalChain.order_bounds.2 c.toFracCertData hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper (fun j p y => fderiv ℝ (c.adjoint j p) y) (fun j p y => fderiv ℝ (fun z => fderiv ℝ (c.adjoint j p) z) y) hSX.adjoint_regular (fun j hj p hp => (hSB.adjoint_solenoidal j hj p hp).2.2) h.losses.adjointSpread_ge
    adjointQuad_nonneg := h.base.adjointQuad_nonneg
    adjoint_quad := adjointQuad_of_potential kernelPotential c.toFracCertData hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper (fun j p => adjointWeightOf c X.weightValue j p) (fun j _ => X.adjointKernel j) hSX.adjoint_measurable (fun j _ p _ y => by
      have hw : X.weightValue ≠ 0 := h.inst.weightValue_pos.ne'
      simp only [h.inst.weight_eq, adjointWeightOf]
      exact le_of_eq (by field_simp)) (fun j hj p hp => hAK c D A M MD RD X h j hj p hp) h.losses.adjointQuad_ge
    active_inclusion := h.base.active_inclusion
    stiff_inclusion := h.base.stiff_inclusion
    nontrivial := h.base.nontrivial }
  innerWeight_nonneg := h.numbers.innerWeight_nonneg
  innerWeight_le := h.numbers.innerWeight_le
  cellRegion_measurable := hSC.cellRegion_measurable
  cellRegion_bounded := hSC.cellRegion_bounded
  cellRegion_class := hSC.cellRegion_class
  cellWeight_measurable := hSC.cellWeight_measurable
  cellWeight_nonneg := hSC.cellWeight_nonneg
  cellWeight_le := hSC.cellWeight_le
  cellWeight_support := hSC.cellWeight_support
  rows_dominated := hSC.rows_dominated
  row_in_cells := hSC.row_in_cells
  centre_smooth := hSC.centre_smooth
  centre_second := hSC.centre_second
  centre_divergence := hSC.centre_divergence
  centre_class := hSC.centre_class
  centre_bounds := hSC.centre_bounds
  model_measurable := hSC.model_measurable
  model_bounded := hSC.model_bounded
  model_in_cells := hSC.model_in_cells
  model_outside := hSC.model_outside
  modelStrain_symmetric := hSC.modelStrain_symmetric
  modelCurlGrad_trace := hSC.modelCurlGrad_trace
  modelActuator_data := hSC.modelActuator_data
  modelActuatorGrad_data := hSC.modelActuatorGrad_data
  modelPin_data := hSC.modelPin_data
  actuator_gradient := hSC.actuator_gradient
  actuator_in_cells := hSC.actuator_in_cells
  pin_in_cells := hSC.pin_in_cells
  centreLoss_bound := centreLoss_of_kernel kernelPotential c hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper ⟨X.centreSup, X.centreKernel⟩ ⟨centreSupSplit_of c D A M MD RD X h, hCK c D A M MD RD X h, h.losses.centreKernel_nonneg⟩ h.losses.centre_le
  rateLoss_bound := rateLoss_of_rows hRM c hSB.weightMin_pos hSB.weight_lower hSB.weight_measurable hSB.weight_upper (turnOf RD c.order X.rateRowConst) (hTD c D A M MD RD X.rateRowConst h.given h.losses.turn_numbers) h.losses.rate_le
  strainLoss_bound := strainLoss_of_opNorm c X.strainOpBound h.losses.strain_opNorm h.losses.strain_le
  curlGradLoss_bound := curlGradLoss_of_kernel kernelPotential c X.curlGradKernel (hKB c.order _ (X.curlGradSums.toData c.order) (cellSumData_of c.order _ X.curlGradSums h.losses.curlGrad_sums_values h.losses.curlGrad_sums_bounded (hSW c D A M MD RD h.given X.weightValue h.inst.weightValue_pos X.splitStep h.losses.amp_index).1) X.curlGradKernel h.losses.curlGrad_boxes) h.losses.curlGrad_le
  velocityLoss_bound := h.numbers.velocityLoss_bound
  curlLoss_bound := curlLoss_of_kernel kernelPotential c X.curlKernel (hKB c.order _ (X.curlSums.toData c.order) (cellSumData_of c.order _ X.curlSums h.losses.curl_sums_values h.losses.curl_sums_bounded (hSW c D A M MD RD h.given X.weightValue h.inst.weightValue_pos X.splitStep h.losses.amp_index).2.1) X.curlKernel h.losses.curl_boxes) h.losses.curl_le
  actuatorGradLoss_bound := h.numbers.actuatorGradLoss_bound
  actuatorLoss_bound := h.numbers.actuatorLoss_bound
  pinFieldLoss_bound := h.numbers.pinFieldLoss_bound
  losses_nonneg' := h.numbers.losses_nonneg'
  potLoss_ge := h.numbers.potLoss_ge
  rowLoss_ge := h.numbers.rowLoss_ge
  pinLoss_ge := h.numbers.pinLoss_ge
  rowWeight_block := h.numbers.rowWeight_block
  baseCoef_nonneg := h.numbers.baseCoef_nonneg
  levelCoef_nonneg := h.numbers.levelCoef_nonneg
  levelRate_pos := h.numbers.levelRate_pos
  cutoff_ge := h.numbers.cutoff_ge
  symbol_fit := h.numbers.symbol_fit
  symbol_end := h.numbers.symbol_end
  splitBound_ge := h.numbers.splitBound_ge

theorem exterior_of_system (hBR : BallSubsetRegionStatement) {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (hSE : IsGivenExterior (501 / 500) c X.exterior) : IsExteriorData (501 / 500) c X.exterior where
  radius_measurable := hSE.radius_measurable
  radiusMin_pos := hSE.radiusMin_pos
  radius_between := hSE.radius_between
  radius_homogeneous := hSE.radius_homogeneous
  exterior_eq := hSE.exterior_eq
  innerWeight_ge := h.exterior.innerWeight_ge
  innerWeight_le := h.exterior.innerWeight_le
  curlGrad_traceFree := hSE.curlGrad_traceFree
  strainBound_measurable := by
    rw [h.inst.exterior_strain]
    exact measurable_const.div (continuous_norm.pow 2).measurable
  strain_le := h.exterior.strain_le
  curlGrad_le := h.exterior.curlGrad_le
  meanCurlGradBound_nonneg := by
    rw [h.inst.exterior_mean]
    exact fun y => div_nonneg h.exterior.consts_nonneg.1 (by positivity)
  waveCurlGradBound_nonneg := by
    rw [h.inst.exterior_wave]
    exact fun y => div_nonneg h.exterior.consts_nonneg.2 (by positivity)
  splitLength_pos := by
    rw [h.inst.exterior_split]
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hy
      rw [h.given.model_instance.region_eq]
      exact hBR M h.given.mesh 0 (by rw [norm_zero]; exact (h.inst.exterior_radiusMin ▸ hSE.radiusMin_pos).le)
    exact mul_pos two_pos (norm_pos_iff.mpr hy0)
  splitLength_measurable := by
    rw [h.inst.exterior_split]
    exact measurable_const.mul continuous_norm.measurable
  coef_lower := h.exterior.coef_lower
  wave_bound := h.exterior.wave_bound
  mean_bound := h.exterior.mean_bound
  exterior_test := h.exterior.exterior_test

theorem splitRest_of_mesh (hML : CellCoordinates.MeshMomentLinearStatement) (hGeo : SplitGeometryStatement)
    {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X) (hc : IsFormData (501 / 500) c) :
    FinalChain.IsCellSplitRest (501 / 500) c X.split := by
  obtain ⟨g1, g2, g3, g4⟩ := hGeo c D A M MD RD X h
  obtain ⟨m0, madd, msmul, mkappa⟩ :=
    hML (501 / 500) FinalChain.order_bounds.1 FinalChain.order_bounds.2 c hc X.split X.mesh h.mesh
  have hm : ∀ x, X.split.moment x = X.mesh.canonicalMoment c x := h.inst.moment_eq
  exact {
    cell_measurable := g1
    cells_apart := g2
    cells_cover := g3
    row_support := g4
    moment_zero := by rw [hm]; exact m0
    moment_additive := fun x x' hx hx' => by rw [hm, hm, hm]; exact madd x x' hx hx'
    moment_homogeneous := fun r x hx => by rw [hm, hm]; exact msmul r x hx
    kappa_slot_injective := h.split.kappa_slot_injective
    kappa_slot_value := fun x hx i => by rw [hm]; exact mkappa x hx i
    kappa_slot_free := h.split.kappa_slot_free
    delay_vanish := delayVanish_of (501 / 500) c X.split X.mesh h.mesh (fun x => by rw [hm]) }

theorem cellOfSystem_of_rest (hRP : RowPolynomialOfSystemStatement) (hRT : RowTracesOfStatement) (hRNT : RowNormalTracesOfStatement) (hD : CellDataRestStatement) (hC : CellCoordsRestStatement) (hR : RowsHereStatement) :
    CellOfSystemStatement := by
  intro k N c D A M MD RD X h K₂
  have hd := hD c D A M MD RD X h K₂
  have hc := hC c D A M MD RD X h K₂
  have hf := h.cells K₂
  have hmc := mix_clauses RD c.order c.rowMax h.given.rows
  have hrm := rowMultiplier_of_test (501 / 500) c M MD RD X.split K₂ (X.cell K₂) (X.mesh.coords K₂) hf hmc.1 hmc.2.1
  exact ⟨{
    mean_le := fun p hp h0 => by have e := hf.mean_le p hp h0; rwa [hf.mean_const]
    wave_le := fun p hp h0 θ => by have e := hf.wave_le p hp h0 θ; rwa [hf.wave_const]
    yModes_contain := hf.yModes_contain
    row_mode_resolved := hf.row_mode_resolved
    class_modes_symm := hf.class_modes_symm
    class_disjoint := hf.class_disjoint
    class_resolved := hf.class_resolved
    class_resolved_cover := hf.class_resolved_cover
    class_weights_pos := hf.class_weights_pos
    class_bounds := hf.class_bounds
    class_devs_nonneg := hf.class_devs_nonneg
    penalty_ge := hf.penalty_ge
    farShare_mem := hf.farShare_mem
    multiplier_symm := hrm.1
    multiplier_rows := hrm.2.1
    multiplier_bound := fun μ hμ => by
      have e := hrm.2.2.1 μ hμ
      unfold multiplierLHS at e
      rwa [CellAnalysis.rowFarFinite_holds c _ _ _ _ _ hd.box hd.bases (hRP c D A M MD RD X h K₂) μ]
    classRowWeight_ge := fun a ha => (hf.classRowWeight_eq a ha).ge
    reducer_bound := hrm.2.2.2
    box := hd.box
    scalars := hd.scalars
    bases := hd.bases
    weight_axisymmetric := hd.weight_axisymmetric
    model_mirror := hd.model_mirror
    solid_in_region := hd.solid_in_region
    model_strain_symm := hd.model_strain_symm
    actuator_memLp := hd.actuator_memLp
    curlGrad_traceFree := hd.curlGrad_traceFree
    class_regular := hd.class_regular
    linear_modes := hd.linear_modes
    rows_in_cell := hd.rows_in_cell
    row_modes := hd.row_modes
    row_mode_of := hd.row_mode_of
    rowWeight_pos := hd.rowWeight_pos
    class_cover := hd.class_cover
    far_bound := hd.far_bound }, {
    given_symm := hf.given_symm
    layout_valid := hf.layout_valid
    param_valid := hf.param_valid
    param_conj_closed := hf.param_conj_closed
    row_traces := hRT c M RD _ _ h.given.mesh h.given.rows hf.rows_instance (X.cell K₂).scalars (X.cell K₂).bases
      (X.mesh.coords K₂).layout hf.layout_valid hf.row_side_degree
    row_normal_traces := hRNT c M RD _ _ h.given.mesh h.given.rows hf.rows_instance (X.cell K₂).scalars (X.cell K₂).bases
      (X.mesh.coords K₂).layout hf.layout_valid hf.row_side_degree
    skeleton_free := hf.skeleton_free
    matrix_embedding := hf.matrix_embedding
    far_low := hf.far_low
    given_le_exact := hf.given_le_exact
    visc_pos := hc.visc_pos
    rows_shape := hc.rows_shape
    gauge_spec := hc.gauge_spec
    gauge_linear := hc.gauge_linear
    edge_jump := hc.edge_jump
    root_zero := hc.root_zero
    skeleton_slot := hc.skeleton_slot }, hR c D A M MD RD X h K₂⟩


theorem cellDataRest_of_groups (hB : CellDataBoxStatement) (hM : CellDataModelStatement) (hR : CellDataRowsStatement)
    (hF : CellDataFarStatement) : CellDataRestStatement := by
  intro k N c D A M MD RD X h K₂
  have b := hB c D A M MD RD X h K₂
  have m := hM c D A M MD RD X h K₂
  have r := hR c D A M MD RD X h K₂
  have f := hF c D A M MD RD X h K₂
  exact {
    box := b.box
    scalars := b.scalars
    bases := b.bases
    weight_axisymmetric := m.weight_axisymmetric
    model_mirror := m.model_mirror
    solid_in_region := m.solid_in_region
    model_strain_symm := m.model_strain_symm
    actuator_memLp := m.actuator_memLp
    curlGrad_traceFree := m.curlGrad_traceFree
    class_regular := m.class_regular
    linear_modes := m.linear_modes
    rows_in_cell := r.rows_in_cell
    row_modes := r.row_modes
    row_mode_of := r.row_mode_of
    rowWeight_pos := r.rowWeight_pos
    class_cover := f.class_cover
    far_bound := f.far_bound
    multiplier_bound := f.multiplier_bound }


theorem rowsHere_holds : RowsHereStatement := by
  intro k N c D A M MD RD X h K₂ a
  rw [(h.cells K₂).rows_instance.rowSet_eq a, ← h.inst.row_cell a]
  exact ⟨fun e => by rw [e], fun e => h.inst.cell_bijective.1 e⟩

theorem solid_measurable (K : CellBox) : MeasurableSet K.solid := by
  have hr : Continuous cylRadius := by
    unfold cylRadius
    fun_prop
  have hz : Continuous fun y : Space => |cylHeight y| := by
    unfold cylHeight
    fun_prop
  have e : K.solid = {y | K.r₁ ≤ cylRadius y} ∩ ({y | cylRadius y ≤ K.r₂} ∩
      ({y | K.z₁ ≤ |cylHeight y|} ∩ {y | |cylHeight y| ≤ K.z₂})) := by
    ext y
    exact Iff.rfl
  rw [e]
  apply IsClosed.measurableSet
  exact (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
    ((isClosed_le continuous_const hz).inter (isClosed_le hz continuous_const)))

theorem splitGeometry_of (hRIC : RowsInCellOfStatement) (hAp : CellsApartStatement) : SplitGeometryStatement := by
  intro k N c D A M MD RD X h
  have hsolid : ∀ K₂, X.split.cell K₂ = (M.box (X.cell K₂).meshCell).solid := h.inst.cell_solid
  refine ⟨fun K₂ => ?_, hAp c D A M MD RD X h, ?_, ?_⟩
  · rw [hsolid K₂]
    exact solid_measurable _
  · rw [h.given.model_instance.region_eq]
    simp only [hsolid]
    exact h.inst.cell_bijective.2.iUnion_comp (fun K => (M.box K).solid)
  · intro a y hy
    rw [hsolid, h.inst.row_cell a] at hy
    have hK := (h.cells (X.split.rowCell a)).rows_instance
    have hmem : a ∈ (X.cell (X.split.rowCell a)).rows.rowSet := by
      rw [hK.rowSet_eq a, h.inst.row_cell a]
    rw [← h.inst.row_cell a] at hy
    exact hRIC c M RD _ _ h.given.mesh h.given.rows hK a hmem y hy

theorem cellDataRows_of (hRIC : RowsInCellOfStatement) (hRMs : RowModesOfStatement) (hRMo : RowModeOfOfStatement)
    (hRo : RowClausesStatement) : CellDataRowsStatement := by
  intro k N c D A M MD RD X h K₂
  have hI := (h.cells K₂).rows_instance
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  exact {
    rows_in_cell := hRIC c M RD _ _ h.given.mesh h.given.rows hI
    row_modes := hRMs c M RD _ _ h.given.mesh h.given.rows hI hm
    row_mode_of := hRMo c M RD _ _ h.given.mesh h.given.rows hI hm
    rowWeight_pos := fun a _ => (hRo c M RD h.given.mesh h.given.rows h.given.rows_instance hm).2.2.2.2.1 a }

theorem spectral_of_system (hRB : RowsInBlockOfStatement) {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (hrows : ∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0) : Spectral.IsSpectralData c X.spectral where
  rows_orthonormal := hrows
  rows_in_blocks := fun a => by
    rw [h.inst.block_eq a]
    exact hRB c M RD h.given.mesh h.given.rows h.given.rows_instance a
  block_geometry := h.spectral.block_geometry
  off_axis := h.spectral.off_axis
  on_axis := h.spectral.on_axis
  blocks_apart := h.spectral.blocks_apart
  interval_bounded := h.spectral_bounds.interval_bounded
  axis_bounded := h.spectral_bounds.axis_bounded
  axis_gradient := h.spectral.axis_gradient
  cutoff_pos := h.spectral.cutoff_pos

def chainEntry {k N : ℕ} {M : CellMesh} (X : CellSystemData k N M) (K₂ : Fin X.split.cellCount) :
    FinalChain.CellEntry N k X.split.slots :=
  ⟨(X.cell K₂).box, (X.cell K₂).scalars, (X.cell K₂).bases, (X.cell K₂).classes, (X.cell K₂).rows, X.mesh.coords K₂⟩

theorem cellFacts_of_system (hCell : CellOfSystemStatement) {k N : ℕ} (c : FracCellData k N) (D : ProfileData k)
    (A : AuxData k) (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) (K₂ : Fin X.split.cellCount) :
    FinalChain.IsCellFacts (501 / 500) c X.split K₂ (chainEntry X K₂) where
  data := (hCell c D A M MD RD X h K₂).1
  coords := (hCell c D A M MD RD X h K₂).2.1
  solid := by
    rw [h.inst.cell_solid K₂]
    exact Filter.EventuallyEq.rfl
  rows_here := (hCell c D A M MD RD X h K₂).2.2

theorem supportRegionOf_holds : SupportRegionOfStatement := by
  intros
  first
  | exact supportRegion_of ..
  | (apply supportRegion_of <;> assumption)

theorem centreTraceFreeOf_holds : CentreTraceFreeOfStatement := by
  intros
  first
  | exact centreTraceFree_of ..
  | (apply centreTraceFree_of <;> assumption)

theorem rowModeGradient_holds : RowModeGradientStatement := by
  intros
  first
  | exact rowModeGradient ..
  | (apply rowModeGradient <;> assumption)

theorem rowTracesOf_holds : RowTracesOfStatement := by
  intros
  first
  | exact rowTraces_of ..
  | (apply rowTraces_of <;> assumption)

theorem rowNormalTracesOf_holds : RowNormalTracesOfStatement := by
  intros
  first
  | exact rowNormalTraces_of ..
  | (apply rowNormalTraces_of <;> assumption)

theorem rowsInBlockOf_holds : RowsInBlockOfStatement := by
  intros
  first
  | exact rowsInBlock_of ..
  | (apply rowsInBlock_of <;> assumption)

theorem rotationRateContinuousOf_holds : RotationRateContinuousOfStatement := by
  intros
  first
  | exact rotationRate_continuous_of ..
  | (apply rotationRate_continuous_of <;> assumption)

theorem multiplierContinuousOf_holds : MultiplierContinuousOfStatement := by
  intros
  first
  | exact multiplier_continuous_of ..
  | (apply multiplier_continuous_of <;> assumption)

theorem profileSmoothOf_holds : ProfileSmoothOfStatement := by
  intros
  first
  | exact profile_smooth_of ..
  | (apply profile_smooth_of <;> assumption)

theorem profileSecondOf_holds : ProfileSecondOfStatement := by
  intros
  first
  | exact profile_second_of ..
  | (apply profile_second_of <;> assumption)

theorem profileDivergenceOf_holds : ProfileDivergenceOfStatement := by
  intros
  first
  | exact profile_divergence_of ..
  | (apply profile_divergence_of <;> assumption)

theorem profileClassOf_holds : ProfileClassOfStatement := by
  intros
  first
  | exact profile_class_of ..
  | (apply profile_class_of <;> assumption)

theorem centreSmoothOf_holds : CentreSmoothOfStatement := by
  intros
  first
  | exact centre_smooth_of ..
  | (apply centre_smooth_of <;> assumption)

theorem centreSecondOf_holds : CentreSecondOfStatement := by
  intros
  first
  | exact centre_second_of ..
  | (apply centre_second_of <;> assumption)

theorem centreDivergenceOf_holds : CentreDivergenceOfStatement := by
  intros
  first
  | exact centre_divergence_of ..
  | (apply centre_divergence_of <;> assumption)

theorem centreClassOf_holds : CentreClassOfStatement := by
  intros
  first
  | exact centre_class_of ..
  | (apply centre_class_of <;> assumption)

theorem centreSecondSymmOf_holds : CentreSecondSymmOfStatement := by
  intros
  first
  | exact centreSecond_symm_of ..
  | (apply centreSecond_symm_of <;> assumption)

theorem actuatorOfGiven_holds : ActuatorOfGivenStatement := by
  intros
  first
  | exact actuator_of_given ..
  | (apply actuator_of_given <;> assumption)

theorem actuatorGradientOfGiven_holds : ActuatorGradientOfGivenStatement := by
  intros
  first
  | exact actuatorGradient_of_given ..
  | (apply actuatorGradient_of_given <;> assumption)

theorem actuatorSupportOfGiven_holds : ActuatorSupportOfGivenStatement := by
  intros
  first
  | exact actuatorSupport_of_given ..
  | (apply actuatorSupport_of_given <;> assumption)

theorem smoothPinOfGiven_holds : SmoothPinOfGivenStatement := by
  intros
  first
  | exact smoothPin_of_given ..
  | (apply smoothPin_of_given <;> assumption)

theorem adjointSolenoidalOfGiven_holds : AdjointSolenoidalOfGivenStatement := by
  intros
  first
  | exact adjointSolenoidal_of_given ..
  | (apply adjointSolenoidal_of_given <;> assumption)

theorem adjointRegularOfGiven_holds : AdjointRegularOfGivenStatement := by
  intros
  first
  | exact adjointRegular_of_given ..
  | (apply adjointRegular_of_given <;> assumption)

theorem cellRegionClauses_holds : CellRegionClausesStatement := by
  intros
  first
  | exact cellRegion_clauses ..
  | (apply cellRegion_clauses <;> assumption)

theorem modelClauses_holds : ModelClausesStatement := by
  intros
  first
  | exact model_clauses ..
  | (apply model_clauses <;> assumption)

theorem modelAuxClauses_holds : ModelAuxClausesStatement := by
  intros
  first
  | exact modelAux_clauses ..
  | (apply modelAux_clauses <;> assumption)

theorem rowClauses_holds : RowClausesStatement := by
  intros
  first
  | exact row_clauses ..
  | (apply row_clauses <;> assumption)

theorem weightClauses_holds : WeightClausesStatement := by
  intros
  first
  | exact weight_clauses ..
  | (apply weight_clauses <;> assumption)

theorem exteriorClauses_holds : ExteriorClausesStatement := by
  intros
  first
  | exact exterior_clauses ..
  | (apply exterior_clauses <;> assumption)

theorem ballSubsetRegion_holds : BallSubsetRegionStatement := by
  intros
  first
  | exact ball_subset_region ..
  | (apply ball_subset_region <;> assumption)

theorem kernelBoundOfCellSums_holds : KernelBoundOfCellSumsStatement := by
  intros
  first
  | exact kernelBound_of_cellSums ..
  | (apply kernelBound_of_cellSums <;> assumption)

theorem rowTurnDataOf_holds : RowTurnDataOfStatement := by
  intros
  first
  | exact rowTurnData_of ..
  | (apply rowTurnData_of <;> assumption)

theorem adjointKernelOf_holds : AdjointKernelOfStatement := by
  intros
  first
  | exact adjointKernel_of ..
  | (apply adjointKernel_of <;> assumption)

theorem meshMomentLinear_holds : CellCoordinates.MeshMomentLinearStatement :=
  meshMomentLinear meshGaugeLinear dataAffine

theorem adjointLocalOfDual_holds : AdjointLocalOfDualStatement :=
  adjointLocal_of_dual adjointRepresentation (weightedInverseSquare_of_frameBound frameInverseSquare)

section

open scoped ContDiff ENNReal
open MeasureTheory Matrix
open SteadyCert Assembly Reduction GivenFields GivenModel Exterior CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite
open CellSystem

def FormDataOfSystemStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → IsFormData (501 / 500) c

namespace CellDataFarInternal

theorem scalars_of_system {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (K₂ : Fin X.split.cellCount) :
    IsCellScalars (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars := by
  have hR := h.cells K₂
  have hK : IsCellBox (X.cell K₂).box := h.given.mesh.boxes _
  have hWF := hR.weight_form
  have hWT := hR.weight_tests
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ :=
    weightClauses_of (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).weights hK hWF hWT
  obtain ⟨q1, q2⟩ := resolvedPointwise_of (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).weights
    (X.cell K₂).strainScalar (X.cell K₂).lowConst hK hWF hWT hR.resolved_tests
  refine
    { resolved_symm := ?_
      band_symm := ?_
      zero_resolved := ?_
      disjoint := ?_
      axis_resolved := ?_
      unresolved_large := w1
      splitLength_pos := hWT.splitLength_pos
      strain_le := ?_
      data_regular := scalarsRegular_of_const (X.cell K₂).box hK (X.cell K₂).scalars
        (fun _ => strainScalarMatrix (X.cell K₂).strainScalar) hR.resolved_tests.local_form
        (X.cell K₂).strainConst (X.cell K₂).meanConst (X.cell K₂).waveConst hR.strain_const hR.mean_const
        hR.wave_const
      grad_bounds_nonneg := ?_
      energyWeight_pos := w2
      energyWeight_le := w3
      vorticityWeight_nonneg := w4
      vorticityWeight_le := w5
      weights_symm := w6
      localMatrix_selfAdjoint := ?_
      localMatrix_le := q1
      resolved_pointwise := q2
      unresolved_pointwise := unresolvedPointwise_of (501 / 500) c _ _ _ hK hWF hWT
      tailShift_nonneg := w7
      tailShift_zero := w8
      weightFloor_pos := hWT.floor_pos
      sym_weight := w9
      anti_weight := w10
      vel_weight := w11
      degrees := hR.degrees }
  · intro n
    rw [hWF.resolved_eq]
    simp only [Finset.mem_Icc]
    omega
  · intro n
    rw [hWF.band_eq]
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  · rw [hWF.resolved_eq]
    simp
  · rw [hWF.resolved_eq, hWF.band_eq]
    exact Finset.disjoint_sdiff
  · intro hax
    rw [hWF.resolved_eq, hR.axis_resolved_test hax]
    rfl
  · intro p hp hp0 θ u
    rw [hR.strain_const]
    exact hR.strain_le p hp hp0 θ u
  · intro p
    rw [hR.mean_const, hR.wave_const]
    exact hR.grad_consts_nonneg
  · intro n p
    by_cases hn : n ∈ (X.cell K₂).scalars.resolved
    · rw [hR.resolved_tests.local_form n hn p]
      unfold strainScalarMatrix
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      by_cases hi : (i : ℕ) < 9 <;> simp [hi]
    · rw [hR.local_zero n hn p]
      exact Matrix.isHermitian_zero

theorem bases_of_system {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (K₂ : Fin X.split.cellCount) : IsCellBases (X.cell K₂).box (X.cell K₂).bases :=
  (extendBases_of orthoFamily_spec (X.cell K₂).box (X.cell K₂).baseDegree (X.cell K₂).givenBases
    (h.given.mesh.boxes _) (h.cells K₂).given_bases).1

theorem solid_of_system {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (K₂ : Fin X.split.cellCount) : (X.cell K₂).box.solid ⊆ c.cellRegion := by
  intro y hy
  rw [h.given.model_instance.region_eq]
  exact Set.mem_iUnion.2 ⟨_, hy⟩

end CellDataFarInternal

open CellDataFarInternal in
theorem cellDataFar_of_form (hF : FormDataOfSystemStatement) (hCst : CentreSmoothOfStatement)
    (hC2 : CentreSecondOfStatement) (hCSy : CentreSecondSymmOfStatement) : CellDataFarStatement := by
  intro k N c D A M MD RD X h K₂
  have hR := h.cells K₂
  have hK : IsCellBox (X.cell K₂).box := h.given.mesh.boxes _
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  have hS := scalars_of_system c D A M MD RD X h K₂
  have hB := bases_of_system c D A M MD RD X h K₂
  have hsolid := solid_of_system c D A M MD RD X h K₂
  have hCR : IsCentreRegular c :=
    ⟨hCst D c h.given.profile h.given.centre_instance, (hC2 D c h.given.profile h.given.centre_instance).2,
      hCSy D c h.given.profile h.given.centre_instance⟩
  obtain ⟨t1, t2, t3⟩ := tailRegular_of c M MD h.given.mesh h.given.model h.given.model_instance hCR
    (X.cell K₂).meshCell (X.cell K₂).scalars (X.cell K₂).far
  obtain ⟨pA, pP⟩ := actuatorPoly_interior c M MD h.given.mesh h.given.model_instance hm (X.cell K₂).meshCell
    (X.cell K₂).scalars (X.cell K₂).rows hR.model_degree
  have hMaj : IsFarMajorant c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).rows
      (X.cell K₂).far :=
    { strain_bounds := tailBounds_of_columns _ _ hK hB _ _ t1 hR.far_strain_columns
      velocity_bounds := tailBounds_of_columns _ _ hK hB _ _ t2 hR.far_velocity_columns
      band_bounds := fun hb => tailBounds_of_columns _ _ hK hB _ _ t3 (hR.far_band_columns hb)
      share_pos := hR.far_share_pos
      turnBound_nonneg := hR.far_turnBound_nonneg
      turn_bound := turnBound_of c (X.cell K₂).scalars (X.cell K₂).weights (X.cell K₂).far h.base.order_ge
        hR.weight_form.band_eq hR.far_turn_ge
      floors_pos := hR.far_floors_pos
      far_floor := farFloor_of (501 / 500) c _ _ _ _ hK hR.weight_form hR.weight_tests hR.degrees.2.2
        hR.far_floor_tests
      strainWeight_ge := hR.far_strainWeight_ge
      resolvedVelocityWeight_ge := hR.far_resolvedVelocityWeight_ge
      bandVelocityWeight_ge := hR.far_bandVelocityWeight_ge
      localMatrix_const := localMatrixConst_of _ _ (fun _ => strainScalarMatrix (X.cell K₂).strainScalar)
        hR.resolved_tests.local_form
      actuator_poly := fun i n hn a b => by
        obtain ⟨P, hP, hPe⟩ := pA i n hn a b
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩
      pin_poly := fun i n hn a b => by
        obtain ⟨P, hP, hPe⟩ := pP i n hn a b
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩
      support_contains := hR.far_support_contains
      kernel_dominates := hR.far_kernel_dominates }
  obtain ⟨rF, rV⟩ := rowPolynomial_interior c M MD RD h.given.mesh h.given.model_instance h.given.rows
    (X.cell K₂).meshCell (X.cell K₂).rows hR.rows_instance hm (X.cell K₂).scalars (X.cell K₂).rowDegree
    hR.row_poly_degree
  have hPoly : IsRowPolynomial c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).rows (X.cell K₂).rowDegree :=
    { folded_poly := fun a ha n' hn i q => by
        obtain ⟨P, hP, hPe⟩ := rF a ha n' hn i q
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩
      velocity_poly := fun a ha n' hn i => by
        obtain ⟨P, hP, hPe⟩ := rV a ha n' hn i
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩ }
  refine ⟨?_, ?_, ?_⟩
  · intro n hn n' hn' hex
    refine classCover_of c M MD h.given.mesh h.given.model h.given.model_instance hm (X.cell K₂).meshCell
      (X.cell K₂).box rfl hsolid hK (X.cell K₂).scalars (X.cell K₂).classes hR.class_cover_test n hn n' hn' ?_
    obtain ⟨p, hp, hp0, hne⟩ := hex
    exact ⟨p, hp, hp0, hne⟩
  · exact farMajorant_of_coef (farCoef cylinderComp) (501 / 500) (by norm_num) (by norm_num) c
      (hF c D A M MD RD X h) _ _ _ _ _ hK hsolid hS hB hR.yModes_contain hMaj
  · intro μ hμ
    rw [rowFarFinite_closed c _ _ _ _ _ hK hB hPoly μ]
    have e := (rowMultiplier_of_test (501 / 500) c M MD RD X.split K₂ (X.cell K₂) (X.mesh.coords K₂) hR
      (mix_clauses RD c.order c.rowMax h.given.rows).1 (mix_clauses RD c.order c.rowMax h.given.rows).2.1).2.2.1 μ hμ
    unfold multiplierLHS at e
    exact e

end

section

open scoped ContDiff ENNReal
open MeasureTheory Matrix
open SteadyCert Assembly Reduction GivenFields GivenModel Exterior CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite
open CellSystem

def RowLowGradientOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (S : CellScalars), IsCellMesh M →
    IsRowData RD c.order c.rowMax → IsRowsInstance c M RD K₀ R → 0 < c.order →
    RD.degree + 2 ≤ S.degHigh →
    ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p

def RowSolenoidalOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N),
    IsCellMesh M → IsRowData R c.order c.rowMax → IsRowInstance c M R →
    ∀ a, ∀ y ∈ (M.box (R.cell a)).solid,
      ∑ i : Fin 3, inner ℝ (fderiv ℝ (c.row a) y (unitVector i)) (unitVector i) = 0

private theorem cellRowShape (hLG : RowLowGradientOfStatement) (hSol : RowSolenoidalOfStatement)
    {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X)
    (K₂ : Fin X.split.cellCount) :
    IsRowShape c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).rows := by
  have hC := h.cells K₂
  have hI := hC.rows_instance
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  have hbox : ∀ a ∈ (X.cell K₂).rows.rowSet, M.box (RD.cell a) = (X.cell K₂).box := fun a ha => by
    rw [(hI.rowSet_eq a).1 ha]
    rfl
  have hL := rowLow_of_gradient c M RD (X.cell K₂).meshCell (X.cell K₂).rows (X.cell K₂).scalars h.given.mesh
    h.given.rows hI hm hC.row_degree
    (hLG c M RD (X.cell K₂).meshCell (X.cell K₂).rows (X.cell K₂).scalars h.given.mesh h.given.rows hI hm
      hC.row_degree)
  refine
    { row_slope := fun a ha => ?_
      row_smooth := fun a ha δ hδ => ?_
      row_mirror := rowMirror_of c M RD (X.cell K₂).meshCell (X.cell K₂).rows h.given.mesh h.given.rows hI
      row_solenoidal := fun a ha y hy => ?_
      row_class := fun a _ => (row_clauses c M RD h.given.mesh h.given.rows h.given.rows_instance hm).2.2.2.1 a
      row_low_velocity := hL.1
      row_low_position := hL.2.1
      row_low_turn := hL.2.2.1
      row_low_gradient := fun a ha n i b => ?_ }
  · obtain ⟨L, hSlope⟩ := rowHalfSlope_of c M RD h.given.mesh h.given.rows h.given.rows_instance a
    rw [hbox a ha] at hSlope
    exact ⟨L, hSlope⟩
  · obtain ⟨f, hf, hfe⟩ := rowSmooth_of c M RD h.given.mesh h.given.rows h.given.rows_instance a δ hδ
    rw [hbox a ha] at hfe
    exact ⟨f, hf, hfe⟩
  · rw [← hbox a ha] at hy
    exact hSol c M RD h.given.mesh h.given.rows h.given.rows_instance a y hy
  · obtain ⟨P, hP, hPe⟩ := hL.2.2.2 a ha n i b
    exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩

theorem cellCoordsRest_of (hSlot : MeshSkeletonSlotStatement) (hForm : FormDataOfSystemStatement)
    (hLG : RowLowGradientOfStatement) (hSol : RowSolenoidalOfStatement) : CellCoordsRestStatement := by
  intro k N c D A M MD RD X h K₂
  have hα₁ : (1 : ℝ) < 501 / 500 := by norm_num
  have hα₂ : (501 / 500 : ℝ) < 5 / 4 := by norm_num
  have hF := hForm c D A M MD RD X h
  have hGL := h.inst.gauge_left K₂
  have hGR := h.inst.gauge_right K₂
  refine
    { visc_pos := lt_trans h.base.coercivity_pos h.base.coercivity_lt
      rows_shape := cellRowShape hLG hSol c D A M MD RD X h K₂
      gauge_spec := h.mesh.gauge_specs K₂
      gauge_linear := fun x y a b hx hy => ?_
      edge_jump := fun e he x hx => ?_
      root_zero := fun r hr x hx => ?_
      skeleton_slot := fun x hx j => ?_ }
  · rw [hGL, hGR]
    exact meshGaugeLinear _ hα₁ hα₂ c hF X.split X.mesh h.mesh K₂ x y a b hx hy
  · rw [hGL, hGR]
    exact meshEdgeJump _ hα₁ hα₂ c hF X.split X.mesh h.mesh K₂ e he x hx
  · rw [hGL, hGR]
    exact meshRootZero _ hα₁ hα₂ c hF X.split X.mesh h.mesh K₂ r hr x hx
  · rw [h.inst.moment_eq x, hSlot _ hα₁ hα₂ c hF X.split X.mesh h.mesh x hx K₂ j, hGL, hGR]
    rfl

theorem meshSkeletonSlot_holds : MeshSkeletonSlotStatement :=
  meshSkeletonSlot_of streamIndependence_holds fluxStream_holds

theorem rowLowGradientOf_holds : RowLowGradientOfStatement := by
  intro k N slots c M RD K₀ R S hM hR hI hm hdeg
  exact (rowLow_of c M RD K₀ R S hM hR hI hm hdeg).2.2.2

theorem rowSolenoidalOf_holds : RowSolenoidalOfStatement := by
  intro k N c M R hM hR hI
  exact rowSolenoidal_of_mixSame c M R hM hR hI (mix_clauses R c.order c.rowMax hR).2.1

end

theorem rowPolynomialOfSystem_holds : RowPolynomialOfSystemStatement := by
  intro k N c D A M MD RD X h K₂
  have hR := h.cells K₂
  have hm : 0 < c.order := lt_of_lt_of_le (by norm_num) h.base.order_ge
  obtain ⟨rF, rV⟩ := rowPolynomial_interior c M MD RD h.given.mesh h.given.model_instance h.given.rows
    (X.cell K₂).meshCell (X.cell K₂).rows hR.rows_instance hm (X.cell K₂).scalars (X.cell K₂).rowDegree
    hR.row_poly_degree
  exact
    { folded_poly := fun a ha n' hn i q => by
        obtain ⟨P, hP, hPe⟩ := rF a ha n' hn i q
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩
      velocity_poly := fun a ha n' hn i => by
        obtain ⟨P, hP, hPe⟩ := rV a ha n' hn i
        exact ⟨P, hP, fun p hp _ => hPe p hp.1 hp.2⟩ }

theorem profileBoundsOf_holds : ProfileBoundsOfStatement := by
  intros
  first
  | exact profile_bounds_of ..
  | (apply profile_bounds_of <;> assumption)

theorem profileDriftOf_holds : ProfileDriftOfStatement := by
  intros
  first
  | exact profile_drift_of ..
  | (apply profile_drift_of <;> assumption)

theorem profilePowerOf_holds : ProfilePowerOfStatement := by
  intros
  first
  | exact profile_power_of ..
  | (apply profile_power_of <;> assumption)

theorem profileContinuousOf_holds : ProfileContinuousOfStatement := by
  intros
  first
  | exact profile_continuous_of ..
  | (apply profile_continuous_of <;> assumption)

theorem centreBoundsOf_holds : CentreBoundsOfStatement := by
  intros
  first
  | exact centre_bounds_of ..
  | (apply centre_bounds_of <;> assumption)

theorem sumWeightsOf_holds : SumWeightsOfStatement := by
  intros
  first
  | exact sumWeights_of ..
  | (apply sumWeights_of <;> assumption)

theorem centreKernelSplitOf_holds : CentreKernelSplitOfStatement := by
  intros
  first
  | exact centreKernelSplit_of ..
  | (apply centreKernelSplit_of <;> assumption)

theorem adjointDualCoreOfGiven_holds : AdjointDualCoreOfGivenStatement := by
  intros
  first
  | exact adjointDualCore_of_given ..
  | (apply adjointDualCore_of_given <;> assumption)

theorem adjointDualStructureOf_holds : AdjointDualStructureOfStatement := by
  intros
  first
  | exact adjointDualStructure_of ..
  | (apply adjointDualStructure_of <;> assumption)

theorem fractional_breakdown_of_cell_system_of_parts
    {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M) (h : CellSystemCondition c D A M MD RD X) :
    FractionalBreakdownOnSpace (501 / 500) ∧ FractionalBreakdownOnTorus (501 / 500) := by
  have hForm : FormDataOfSystemStatement := by
    intro k N c D A M MD RD X h
    obtain ⟨hSB, hSC, -, hSX, -⟩ := givenParts_of_system rotationRateContinuousOf_holds multiplierContinuousOf_holds profileSmoothOf_holds profileSecondOf_holds profileDivergenceOf_holds profileClassOf_holds profileBoundsOf_holds profileDriftOf_holds profilePowerOf_holds profileContinuousOf_holds centreSmoothOf_holds centreSecondOf_holds centreDivergenceOf_holds centreClassOf_holds centreBoundsOf_holds centreSecondSymmOf_holds actuatorOfGiven_holds actuatorGradientOfGiven_holds actuatorSupportOfGiven_holds smoothPinOfGiven_holds adjointSolenoidalOfGiven_holds adjointRegularOfGiven_holds adjointDualCoreOfGiven_holds supportRegionOf_holds cellRegionClauses_holds modelClauses_holds modelAuxClauses_holds rowClauses_holds weightClauses_holds exteriorClauses_holds ballSubsetRegion_holds centreTraceFreeOf_holds c D A M MD RD X h
    exact FinalChain.isFormData_of_rest (cellRest_of_system kernelBoundOfCellSums_holds rowModeGradient_holds adjointLocalOfDual_holds rowTurnDataOf_holds sumWeightsOf_holds adjointDualStructureOf_holds centreKernelSplitOf_holds adjointKernelOf_holds c D A M MD RD X h hSB hSC hSX)
  obtain ⟨hSB, hSC, hSE, hSX, hrows⟩ := givenParts_of_system rotationRateContinuousOf_holds multiplierContinuousOf_holds profileSmoothOf_holds profileSecondOf_holds profileDivergenceOf_holds profileClassOf_holds profileBoundsOf_holds profileDriftOf_holds profilePowerOf_holds profileContinuousOf_holds centreSmoothOf_holds centreSecondOf_holds centreDivergenceOf_holds centreClassOf_holds centreBoundsOf_holds centreSecondSymmOf_holds actuatorOfGiven_holds actuatorGradientOfGiven_holds actuatorSupportOfGiven_holds smoothPinOfGiven_holds adjointSolenoidalOfGiven_holds adjointRegularOfGiven_holds adjointDualCoreOfGiven_holds supportRegionOf_holds cellRegionClauses_holds modelClauses_holds modelAuxClauses_holds rowClauses_holds weightClauses_holds exteriorClauses_holds ballSubsetRegion_holds centreTraceFreeOf_holds c D A M MD RD X h
  exact FinalChain.breakdown_of_layers c
    (cellRest_of_system kernelBoundOfCellSums_holds rowModeGradient_holds adjointLocalOfDual_holds rowTurnDataOf_holds sumWeightsOf_holds adjointDualStructureOf_holds centreKernelSplitOf_holds adjointKernelOf_holds c D A M MD RD X h hSB hSC hSX) X.split
    (splitRest_of_mesh meshMomentLinear_holds (splitGeometry_of rowsInCellOf_holds cellsApart_holds) c D A M MD RD X h
      (FinalChain.isFormData_of_rest (cellRest_of_system kernelBoundOfCellSums_holds rowModeGradient_holds adjointLocalOfDual_holds rowTurnDataOf_holds sumWeightsOf_holds adjointDualStructureOf_holds centreKernelSplitOf_holds adjointKernelOf_holds c D A M MD RD X h hSB hSC hSX)))
    X.exterior (exterior_of_system ballSubsetRegion_holds c D A M MD RD X h hSE) (chainEntry X) (cellFacts_of_system (cellOfSystem_of_rest rowPolynomialOfSystem_holds rowTracesOf_holds rowNormalTracesOf_holds (cellDataRest_of_groups cellDataBox_holds (cellDataModel_of centreSmoothOf_holds centreSecondOf_holds centreSecondSymmOf_holds modelClauses_holds modelAuxClauses_holds) cellDataRows_holds (cellDataFar_of_form hForm centreSmoothOf_holds centreSecondOf_holds centreSecondSymmOf_holds)) (cellCoordsRest_of meshSkeletonSlot_holds hForm rowLowGradientOf_holds rowSolenoidalOf_holds) rowsHere_holds) c D A M MD RD X h)
    X.tree h.tree.tree h.tree.cells_match h.tree.global_eq X.spectral (spectral_of_system rowsInBlockOf_holds c D A M MD RD X h hrows)
    h.inst.spectralBound_eq h.spectral.tail_le

end Breakdown.CellCert.FinalCellSystem


namespace Breakdown.CellCert.CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

theorem fractional_breakdown_of_cell_system_proved {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) :
    FractionalBreakdownOnSpace (501 / 500) ∧ FractionalBreakdownOnTorus (501 / 500) := by
  exact FinalCellSystem.fractional_breakdown_of_cell_system_of_parts c D A M MD RD X h

end Breakdown.CellCert.CellSystem
