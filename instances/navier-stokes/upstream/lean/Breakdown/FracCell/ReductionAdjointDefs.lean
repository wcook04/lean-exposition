import Breakdown.FracCell.Defs
import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def IsWeakScalarGradientOf (q : Space → ℝ) (Q : Space → Space) : Prop :=
  ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
    ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j)

def harmonicWeightSq (F : Space → Space) : ENNReal :=
  ∑' k : ℤ, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2) *
      (‖angularMode (horizontalPart F) k q.1 q.2‖ ^ 2 / (((|k| : ℤ) : ℝ) + 1 / 2) ^ 2
        + ‖angularMode (verticalPart F) k q.1 q.2‖ ^ 2 / (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2))

def IsAdjointRegular (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space))
    (Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop :=
  MemLp ζ 2 volume ∧ MemLp ζ 3 volume ∧ MemLp (fun y => ‖y‖ • ζ y) 2 volume ∧
    AEStronglyMeasurable Dζ volume ∧ IsWeakGradientOf ζ Dζ ∧ Integrable (fun y => entrySq (Dζ y)) ∧
    Integrable (fun y => ‖y‖ ^ 4 * entrySq (Dζ y)) ∧ AEStronglyMeasurable Hζ volume ∧ IsWeakSecondDerivOf Dζ Hζ ∧
    Integrable (fun y => fullSecondSq (Hζ y))

namespace AdjointDual

variable {k : ℕ} (D : AdjointDual k)

end AdjointDual

structure IsAdjointDual (α : ℝ) {k N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (D : AdjointDual k) :
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
  pin_scale : ∀ l, 0 < D.pinScale l
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
  potentialScale_nonneg : 0 ≤ D.potentialScale
  flux_divergence : IsWeakMatrixDivergenceOf D.fluxField D.fluxDiv
  flux_two : AEStronglyMeasurable D.fluxField volume ∧ Integrable (fun y => entrySq (D.fluxField y)) ∧
    MemLp (fun y => ‖y‖ • D.fluxDiv y) 2 volume
  remainder_split : ∀ᵐ y ∂volume, D.remainderField α d j p y =
    D.inverseSquarePart y + ∑ i ∈ Finset.univ \ D.exactSet, p i • convectionAdjointField (D.shiftField i) (D.shiftGrad i)
      (d.adjoint j p) D.adjointGrad y
  shift_regular : ∀ i, ContDiff ℝ 1 (D.shiftField i) ∧ (∀ y, D.shiftGrad i y = fderiv ℝ (D.shiftField i) y) ∧
    (∀ y, divergenceAt (D.shiftField i) y = 0) ∧
    ∃ C : ℝ, ∀ y, ‖D.shiftField i y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖D.shiftGrad i y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)
  dual_bound : l2Norm D.dualField ≤ D.dualBound
  potential_bound : Real.sqrt (∫ y, entrySq (D.potentialGrad y)) ≤ D.potentialBound
  flux_bound : Real.sqrt (∫ y, entrySq (D.fluxField y)) ≤ D.fluxBound
  inverseSquare_part : AEStronglyMeasurable D.inverseSquarePart volume ∧
    MemLp (fun y => ‖y‖ • D.inverseSquarePart y) 2 volume
  inverseSquare_modes : ∀ k ∉ D.inverseSquareModes, ∀ ρ z : ℝ,
    angularMode (horizontalPart D.inverseSquarePart) k ρ z = 0 ∧ angularMode (verticalPart D.inverseSquarePart) k ρ z = 0
  inverseSquare_weight : harmonicWeightSqOn D.inverseSquareModes D.inverseSquarePart ≤
    ENNReal.ofReal (D.inverseSquareBound ^ 2)
  inverseSquareBound_nonneg : 0 ≤ D.inverseSquareBound
  shift_weighted : ∀ i, Integrable (fun y => ‖D.shiftField i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ∧
    Integrable (fun y => ‖y‖ ^ 2 * ‖D.shiftGrad i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2)
  shift_bound : ∀ i, Real.sqrt (∫ y, ‖D.shiftField i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ≤ D.shiftBound i
  shiftGrad_bound : ∀ i, Real.sqrt (∫ y, ‖y‖ ^ 2 * ‖D.shiftGrad i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ≤ D.shiftGradBound i

def InverseSquareConstStatement (m : ℕ) (H : ℝ) : Prop :=
  0 ≤ H ∧ ∀ v G K, IsSecondOrderField m v G K →
    Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) ∧ (∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤ H ^ 2 * ∫ y, entrySq (G y)

def WeightedInverseSquareStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → ∀ F : Space → Space, AEStronglyMeasurable F volume →
      MemLp (fun y => ‖y‖ • F y) 2 volume → harmonicWeightSq F ≠ ⊤ →
      |∫ y, inner ℝ (v y) (F y)| ≤ Real.sqrt (harmonicWeightSq F).toReal * Real.sqrt (∫ y, entrySq (G y))

def AdjointRepresentationStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (D : AdjointDual k),
    IsAdjointDual α d j p D → ContDiff ℝ 1 (d.profile p) → (∀ y, divergenceAt (d.profile p) y = 0) →
    (∃ C : ℝ, ∀ y, ‖d.profile p y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖d.gradProfile p y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)) →
    IsSolenoidalL2 (d.adjoint j p) →
    ∀ v G H, IsSecondOrderField d.order v G H → MemLp (driftField α (d.rotationRate p) v G) 2 volume →
      l2Pair (d.localField α p v G H 0) (d.adjoint j p) + l2Pair (negSecondTrace H) (d.adjointSharp j p)
          - ∑ l, d.adjointPin j p l * pinValue (d.smoothPin l) G
        = l2Pair (negSecondTrace H) D.dualField + D.potentialScale * (∫ y, entryInner (G y) (D.potentialGrad y))
          - (∫ y, entryInner (G y) (D.fluxField y)) + l2Pair v (D.remainderField α d j p)

def PowerPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (m : ℕ) (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)),
    ∀ Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space), IsAdjointRegular ζ Dζ Hζ → AEStronglyMeasurable ζ volume →
    ∀ v G H P, IsSecondOrderField m v G H → IsWeakFractionalPower α v P →
      MemLp (lowPowerAt (α - 1) ζ) 2 volume ∧
        l2Pair P ζ = l2Pair (negSecondTrace H) (lowPowerAt (α - 1) ζ)

def ClassInverseSquareStatement : Prop := ∀ m : ℕ, 2 ≤ m → InverseSquareConstStatement m (2 / 3)

end Reduction

end CellCert

end Breakdown
