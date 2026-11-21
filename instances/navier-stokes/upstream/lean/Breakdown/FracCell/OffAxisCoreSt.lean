import Breakdown.FracCell.FieldWitnessSt
import Breakdown.FracCell.CylIntegral

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def solidLower (g : CellBlock) (s : Fin 2) : ℝ := if s = 0 then g.lowerHeight else -g.upperHeight

def solidUpper (g : CellBlock) (s : Fin 2) : ℝ := if s = 0 then g.upperHeight else -g.lowerHeight

def trigWeight (m : ℕ) (t : Fin 2) : ℝ := ∫ θ in (-Real.pi)..Real.pi, trigMode t ((m : ℝ) * θ) ^ 2

def ShapeNormStatement : Prop :=
  ∀ (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ), 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    (∀ s c t, Continuous (Function.uncurry (f s c t))) →
      MemLp (shapeField g f) 2 volume ∧
        ∫ y, ‖shapeField g f y‖ ^ 2 = ∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t *
          ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s, f s c t r z ^ 2 * r

def ShapeGradStatement : Prop :=
  ∀ (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ), 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    (∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) →
    (∀ s c t z, Q s c t g.innerRadius z = 0) → (∀ s c t z, Q s c t g.outerRadius z = 0) →
    (∀ s c t r, Q s c t r (solidLower g s) = 0) → (∀ s c t r, Q s c t r (solidUpper g s) = 0) →
      ∃ D : Space → (Space →L[ℝ] Space), AEStronglyMeasurable D volume ∧
        Integrable (fun y => entrySq (D y)) ∧ IsWeakGradientOf (shapeField g Q) D ∧ ModeGradient g D ∧
        ∫ y, entrySq (D y) ≤ ∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t *
          ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            (deriv (fun x => Q s c t x z) r ^ 2 + deriv (fun w => Q s c t r w) z ^ 2
              + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r

end Spectral

end CellCert

end Breakdown
