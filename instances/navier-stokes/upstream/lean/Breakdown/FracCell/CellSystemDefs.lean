import Breakdown.FracCell.GivenDataDefs
import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCell.ReductionPointwiseDefs
import Breakdown.FracCell.ReductionFarDefs
import Breakdown.FracCell.MeshDefs
import Breakdown.FracCell.SpectralDefs
import Breakdown.FracCell.ExteriorDefs
import Breakdown.FracCell.FiniteDefs
import Breakdown.FracCell.AssemblyDefs
import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.CellCoordsDefs
import Breakdown.Frac.Defs
import Breakdown.FracCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

def turnOf {M : CellMesh} {N : ℕ} (RD : RowData M N) (m : ℕ) (rate : ℝ) : RowTurnData N where
  partner := RD.partner
  modeNum := RD.turnMode m
  cellOf := fun a => (RD.cell a : ℕ)
  cellSet := fun i => if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅
  outerRadius := fun i => if h : i < M.cellCount then (M.box ⟨i, h⟩).r₂ else 0
  rateRowConst := rate

namespace CellSumValues

variable (T : CellSumValues) (m : ℕ)

end CellSumValues

structure IsSumWeight (m : ℕ) (V : Space → ℝ) : Prop where
  measurable : Measurable V
  nonneg : ∀ y, 0 ≤ V y
  turn_invariant : ∀ y, V (turnBy (2 * Real.pi / m) y) = V y
  mirror_even : ∀ y, V (mirror y) = V y
  integrable : Integrable V

structure IsAdjointDualStructure (α : ℝ) {k N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (D : AdjointDual k) :
    Prop where
  adjoint_gradient : IsWeakGradientOf (d.adjoint j p) D.adjointGrad
  adjoint_measurable : AEStronglyMeasurable (d.adjoint j p) volume ∧ AEStronglyMeasurable D.adjointGrad volume
  adjoint_regular : IsAdjointRegular (d.adjoint j p) D.adjointGrad D.adjointSecond
  sharp_trace : IsWeakNegTraceOf (fun y => d.splitVisc • d.adjoint j p y + d.adjointSharp j p y) D.sharpTrace
  sharp_weighted : MemLp (fun y => ‖y‖ • D.sharpTrace y) 2 volume ∧ MemLp (d.adjointSharp j p) 2 volume ∧
    IsWeakGradientOf (d.adjointSharp j p) D.sharpGrad ∧ AEStronglyMeasurable D.sharpGrad volume ∧
    Integrable (fun y => entrySq (D.sharpGrad y))
  pin_regular : ∀ l, ContDiff ℝ 1 (D.pinPotential l) ∧ HasCompactSupport (D.pinPotential l) ∧
    AEStronglyMeasurable (D.pinSecond l) volume ∧ IsWeakSecondDerivOf (fun y => fderiv ℝ (D.pinPotential l) y) (D.pinSecond l) ∧
    (∃ C : ℝ, ∀ᵐ y ∂volume, ‖D.pinSecond l y‖ ≤ C) ∧
    IsWeakNegTraceOf (D.pinPotential l) (D.pinTrace l) ∧ AEStronglyMeasurable (D.pinTrace l) volume ∧
    (∃ C : ℝ, ∀ᵐ y ∂volume, ‖D.pinTrace l y‖ ≤ C)
  pin_field : ∀ l y, d.smoothPin l y = (1 / D.pinScale l) • fderiv ℝ (D.pinPotential l) y
  pressure_gradient : IsWeakScalarGradientOf D.pressure D.pressureGrad
  pressure_two : MemLp D.pressure 2 volume ∧ MemLp (fun y => ‖y‖ • D.pressureGrad y) 2 volume
  dual_trace : IsWeakNegTraceOf D.dualField D.dualTrace
  dual_two : MemLp D.dualField 2 volume ∧ MemLp (fun y => ‖y‖ • D.dualTrace y) 2 volume ∧
    IsWeakGradientOf D.dualField D.dualGrad ∧ AEStronglyMeasurable D.dualGrad volume ∧
    Integrable (fun y => entrySq (D.dualGrad y))
  potential_gradient : IsWeakGradientOf D.potentialField D.potentialGrad
  potential_trace : IsWeakNegTraceOf D.potentialField D.potentialTrace
  potential_two : MemLp D.potentialField 2 volume ∧ AEStronglyMeasurable D.potentialGrad volume ∧
    Integrable (fun y => entrySq (D.potentialGrad y)) ∧ MemLp (fun y => ‖y‖ • D.potentialTrace y) 2 volume
  flux_divergence : IsWeakMatrixDivergenceOf D.fluxField D.fluxDiv
  flux_two : AEStronglyMeasurable D.fluxField volume ∧ Integrable (fun y => entrySq (D.fluxField y)) ∧
    MemLp (fun y => ‖y‖ • D.fluxDiv y) 2 volume
  remainder_split : ∀ᵐ y ∂volume, D.remainderField α d j p y =
    D.inverseSquarePart y + ∑ i ∈ Finset.univ \ D.exactSet, p i • convectionAdjointField (D.shiftField i) (D.shiftGrad i)
      (d.adjoint j p) D.adjointGrad y
  shift_regular : ∀ i, ContDiff ℝ 1 (D.shiftField i) ∧ (∀ y, D.shiftGrad i y = fderiv ℝ (D.shiftField i) y) ∧
    (∀ y, divergenceAt (D.shiftField i) y = 0) ∧
    ∃ C : ℝ, ∀ y, ‖D.shiftField i y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖D.shiftGrad i y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)
  inverseSquare_part : AEStronglyMeasurable D.inverseSquarePart volume ∧
    MemLp (fun y => ‖y‖ • D.inverseSquarePart y) 2 volume
  inverseSquare_modes : ∀ k ∉ D.inverseSquareModes, ∀ ρ z : ℝ,
    angularMode (horizontalPart D.inverseSquarePart) k ρ z = 0 ∧ angularMode (verticalPart D.inverseSquarePart) k ρ z = 0
  shift_weighted : ∀ i, Integrable (fun y => ‖D.shiftField i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ∧
    Integrable (fun y => ‖y‖ ^ 2 * ‖D.shiftGrad i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2)

theorem isAdjointDual_of_parts (α : ℝ) {k N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (D : AdjointDual k) (h₁ : IsAdjointDualNumbers α d j p D) (h₂ : IsAdjointDualStructure α d j p D) :
    IsAdjointDual α d j p D where
  adjoint_gradient := h₂.adjoint_gradient
  adjoint_measurable := h₂.adjoint_measurable
  adjoint_regular := h₂.adjoint_regular
  sharp_trace := h₂.sharp_trace
  sharp_weighted := h₂.sharp_weighted
  pin_regular := h₂.pin_regular
  pin_scale := h₁.pin_scale
  pin_field := h₂.pin_field
  pressure_gradient := h₂.pressure_gradient
  pressure_two := h₂.pressure_two
  dual_trace := h₂.dual_trace
  dual_two := h₂.dual_two
  potential_gradient := h₂.potential_gradient
  potential_trace := h₂.potential_trace
  potential_two := h₂.potential_two
  potentialScale_nonneg := h₁.potentialScale_nonneg
  flux_divergence := h₂.flux_divergence
  flux_two := h₂.flux_two
  remainder_split := h₂.remainder_split
  shift_regular := h₂.shift_regular
  dual_bound := h₁.dual_bound
  potential_bound := h₁.potential_bound
  flux_bound := h₁.flux_bound
  inverseSquare_part := h₂.inverseSquare_part
  inverseSquare_modes := h₂.inverseSquare_modes
  inverseSquare_weight := h₁.inverseSquare_weight
  inverseSquareBound_nonneg := h₁.inverseSquareBound_nonneg
  shift_weighted := h₂.shift_weighted
  shift_bound := h₁.shift_bound
  shiftGrad_bound := h₁.shiftGrad_bound

def adjointWeightOf {k N : ℕ} (c : FracCellData k N) (w : ℝ) (j : Fin k) (p : Fin k → ℝ) (y : Space) : ℝ :=
  ‖c.adjoint j p y‖ ^ 2 / w



section Choices

variable {k : ℕ} (P : ChartParams) (A : AuxData k) (ν : ℝ) (j : Fin k) (p : Fin k → ℝ)

end Choices

namespace CellEntry

variable {M : CellMesh} {N k slots : ℕ} (r : CellEntry M N k slots)

end CellEntry

end CellSystem

end CellCert

end Breakdown
