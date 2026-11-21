import Breakdown.FracCell.SpectralBlocksField

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def BlockSmoothing (g : CellBlock) (lam bound : ℝ) (φ : Space → Space) : Prop :=
  ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)),
    MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧
    IsWeakGradientOf ψ Dψ ∧ ModeGradient g Dψ ∧ ModeField g (fun y => φ y - ψ y) ∧
    (∫ y, ‖φ y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y) ≤ bound * ∫ y, ‖φ y‖ ^ 2

def OffAxisCoreStatement : Prop :=
  ∀ (g : CellBlock) (lam vr vz : ℝ), 0 < lam → g.onAxis = false → 0 < g.innerRadius →
    g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    IntervalCertificate g.degree (lam * (g.outerRadius - g.innerRadius) ^ 2 / 4) vr →
    IntervalCertificate g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4) vz →
    ∀ φ : Space → Space, IsBlockField g φ → MemLp φ 2 volume →
      BlockSmoothing g lam (g.outerRadius / g.innerRadius
        * (vr + vz + ratioFn lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2))) φ

def OnAxisCoreStatement : Prop :=
  ∀ (g : CellBlock) (lam ν va vz : ℝ) (χ : ℝ → ℝ), 0 < lam → g.onAxis = true → g.innerRadius = 0 →
    g.mode = 0 → g.innerRadius < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    ν ≤ lam * (g.outerRadius - g.innerRadius) ^ 2 → AxisCertificate g.degree ν va χ →
    IntervalCertificate g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4) vz →
    ∀ φ : Space → Space, IsBlockField g φ → MemLp φ 2 volume → BlockSmoothing g lam (va + vz) φ

end Spectral

end CellCert

end Breakdown
