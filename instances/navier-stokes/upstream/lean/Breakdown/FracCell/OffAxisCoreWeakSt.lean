import Breakdown.FracCell.OffAxisCoreSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def shapeGradField (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) :
    Space →L[ℝ] Space :=
  ∑ s : Fin 2, Set.indicator (cellSolid g s)
    (fun w => ∑ c : Fin 3, ∑ d : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
      * f s c d t (radialCoord w) (w 2)) • (innerSL ℝ (frameVector d w)).smulRight (frameVector c w)) y

def angularCoef (m : ℕ) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (s : Fin 2) (c : Fin 3) (t : Fin 2)
    (r z : ℝ) : ℝ :=
  (if t = 0 then (m : ℝ) * Q s c 1 r z else -((m : ℝ) * Q s c 0 r z))
    + (if c = 0 then -Q s 1 t r z else if c = 1 then Q s 0 t r z else 0)

def shapeGradCoef (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) :
    Fin 2 → Fin 3 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ :=
  fun s c d t r z =>
    if d = 0 then deriv (fun x => Q s c t x z) r
    else if d = 1 then (max r g.innerRadius)⁻¹ * angularCoef g.mode Q s c t r z
    else deriv (fun x => Q s c t r x) z

def ShapeWeakStatement : Prop :=
  ∀ (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ), 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    (∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) →
    (∀ s c t z, Q s c t g.innerRadius z = 0) → (∀ s c t z, Q s c t g.outerRadius z = 0) →
    (∀ s c t r, Q s c t r (solidLower g s) = 0) → (∀ s c t r, Q s c t r (solidUpper g s) = 0) →
      IsWeakGradientOf (shapeField g Q) (shapeGradField g (shapeGradCoef g Q))

end Spectral

end CellCert

end Breakdown
