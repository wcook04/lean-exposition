import Breakdown.FracCell.OffAxisCoreWeakSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def ShapeSlopeStatement : Prop :=
  ∀ (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ), 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    (∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) →
    (∀ s c t z, Q s c t g.innerRadius z = 0) → (∀ s c t z, Q s c t g.outerRadius z = 0) →
    (∀ s c t r, Q s c t r (solidLower g s) = 0) → (∀ s c t r, Q s c t r (solidUpper g s) = 0) →
      ∃ K : NNReal, LipschitzWith K (shapeField g Q)

def ShapeDerivStatement : Prop :=
  ∀ (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ), 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    (∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) →
    (∀ s c t z, Q s c t g.innerRadius z = 0) → (∀ s c t z, Q s c t g.outerRadius z = 0) →
    (∀ s c t r, Q s c t r (solidLower g s) = 0) → (∀ s c t r, Q s c t r (solidUpper g s) = 0) →
      ∀ᵐ y ∂(volume : Measure Space), HasFDerivAt (shapeField g Q) (shapeGradField g (shapeGradCoef g Q) y) y

end Spectral

end CellCert

end Breakdown
