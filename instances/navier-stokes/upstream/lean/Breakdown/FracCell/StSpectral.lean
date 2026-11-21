import Breakdown.FracCell.SpectralDefs

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def intervalResolvent (μ : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ := p.eval x - intervalSmoothed μ p x

def IntervalIdentityStatement : Prop :=
  ∀ (μ : ℝ) (p : ℝ[X]), 0 < μ →
    ContDiff ℝ 2 (intervalResolvent μ p) ∧ intervalResolvent μ p (-1) = 0 ∧ intervalResolvent μ p 1 = 0 ∧
      (∫ x in (-1 : ℝ)..1, (p.eval x - intervalResolvent μ p x) ^ 2)
          + μ⁻¹ * (∫ x in (-1 : ℝ)..1, deriv (intervalResolvent μ p) x ^ 2)
        = ∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x

def IntervalMinimalStatement : Prop :=
  ∀ (μ : ℝ) (p : ℝ[X]), 0 < μ → ∀ w : ℝ → ℝ, (∃ K, LipschitzWith K w) → w (-1) = 0 → w 1 = 0 →
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x)
      ≤ (∫ x in (-1 : ℝ)..1, (p.eval x - w x) ^ 2) + μ⁻¹ * (∫ x in (-1 : ℝ)..1, deriv w x ^ 2)

def IntervalMonotoneStatement : Prop :=
  ∀ (ν μ : ℝ) (p : ℝ[X]), 0 < ν → ν ≤ μ →
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x)
      ≤ ∫ x in (-1 : ℝ)..1, intervalSmoothed ν p x * p.eval x

def IntervalClosedStatement : Prop :=
  ∀ (q : ℕ) (μ : ℝ) (p : ℝ[X]), 0 < μ → p.natDegree ≤ q →
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x)
      ≤ intervalClosed q μ * ∫ x in (-1 : ℝ)..1, p.eval x ^ 2

def AxisClosedStatement : Prop :=
  ∀ (q : ℕ) (M μ : ℝ), AxisGradientBound q M → 24 ≤ μ →
    ∀ i : ℕ, i ≤ 1 → ∀ p : ℝ[X], p.natDegree ≤ q → (i = 1 → X ∣ p) →
      ∃ χ : ℝ → ℝ, χ 1 = 0 ∧ (∃ K, LipschitzWith K χ) ∧
        axisFunctional i χ μ p ≤ axisClosed q M μ * ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r

def BlockBoundStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      smoothingForm lam (fun y => ∑ b, x b • c.row b y) ≤ ∑ b, sd.blockSpectral (c.blockIndex b) lam * x b ^ 2

def TailStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ a, ∀ lam : ℝ, c.cutoff ≤ lam →
      sd.blockSpectral (c.blockIndex a) lam ≤ sd.tailFormula c.cutoff (c.blockIndex a) * lam ^ (-(1 / 2 : ℝ))

end Spectral

end CellCert

end Breakdown
