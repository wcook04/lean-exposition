import Breakdown.FracCell.FieldWitnessRect

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def AxisNormStatement : Prop :=
  ∀ (g : CellBlock) (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ), g.innerRadius = 0 → 0 < g.outerRadius →
    g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight → (∀ s c, Continuous (Function.uncurry (f s c))) →
    MemLp (fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y) 2 volume →
    ∫ y, ‖∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y‖ ^ 2
      = 2 * Real.pi * ∑ s : Fin 2, ∑ c : Fin 3, ∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
            f s c r z ^ 2 * r

def AxisLiftStatement : Prop :=
  ∀ (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (ψ : Space → Space),
    g.innerRadius = 0 → g.mode = 0 → 0 < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    χ 1 = 0 → (∃ K, LipschitzWith K χ) → (∀ s c j, ContDiff ℝ 1 (u s c j)) →
    (∀ s c j, u s c j (if s = 0 then g.lowerHeight else -g.upperHeight) = 0 ∧
      u s c j (if s = 0 then g.upperHeight else -g.lowerHeight) = 0) →
    (∀ s c, c ≠ 2 → u s c 0 = 0) →
    (∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y) →
    ∃ D : Space → (Space →L[ℝ] Space),
      MemLp ψ 2 volume ∧ AEStronglyMeasurable D volume ∧ Integrable (fun y => entrySq (D y)) ∧
      IsWeakGradientOf ψ D ∧ ModeGradient g D ∧
      ∀ (lam : ℝ) (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ), 0 < lam → (∀ s c, Continuous (Function.uncurry (f s c))) →
        MemLp (fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
          (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y) 2 volume →
        (∫ y, ‖∑ s : Fin 2, Set.indicator (cellSolid g s)
            (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y - ψ y‖ ^ 2)
          + (1 / lam) * ∫ y, entrySq (D y)
        ≤ 2 * Real.pi * ∑ s : Fin 2, ∑ c : Fin 3, ∫ r in (0 : ℝ)..g.outerRadius,
            ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
              ((f s c r z - χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * u s c j z) ^ 2
                + lam⁻¹ * (deriv (fun t => χ (t / g.outerRadius)
                    * ∑ j ∈ Finset.range (g.degree + 1), t ^ j * u s c j z) r ^ 2
                  + (χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * deriv (u s c j) z) ^ 2
                  + ((if c = 2 then 0 else 1 : ℕ) : ℝ) ^ 2
                    * (χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * u s c j z) ^ 2
                    / r ^ 2)) * r

end Spectral

end CellCert

end Breakdown
