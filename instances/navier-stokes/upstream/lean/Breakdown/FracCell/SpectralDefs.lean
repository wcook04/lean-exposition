import Breakdown.FracCell.Defs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace SpectralData

variable (sd : SpectralData)

end SpectralData

def angleCoord (y : Space) : ℝ := Complex.arg (⟨y 0, y 1⟩ : ℂ)

def frameVector (c : Fin 3) (y : Space) : Space :=
  match c with
  | 0 => EuclideanSpace.single 0 (Real.cos (angleCoord y)) + EuclideanSpace.single 1 (Real.sin (angleCoord y))
  | 1 => EuclideanSpace.single 0 (-Real.sin (angleCoord y)) + EuclideanSpace.single 1 (Real.cos (angleCoord y))
  | 2 => unitVector 2

def twoVarEval (P : ℝ[X][X]) (r z : ℝ) : ℝ := (P.map (evalRingHom z)).eval r

def trigMode (t : Fin 2) (x : ℝ) : ℝ := if t = 0 then Real.cos x else Real.sin x

def IsBlockField (g : CellBlock) (φ : Space → Space) : Prop :=
  ∃ A : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X],
    (∀ s c t, (A s c t).natDegree ≤ g.degree ∧ ∀ j, ((A s c t).coeff j).natDegree ≤ g.degree) ∧
    (g.onAxis = true → ∀ s t, X ∣ A s 0 t ∧ X ∣ A s 1 t) ∧
    ∀ᵐ y ∂volume, φ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * twoVarEval (A s c t) (radialCoord w) (w 2)) • frameVector c w) y

structure IsSpectralData {k N : ℕ} (c : FracCellData k N) (sd : SpectralData) : Prop where
  rows_orthonormal : ∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0
  rows_in_blocks : ∀ a, IsBlockField (sd.block (c.blockIndex a)) (c.row a)
  block_geometry : ∀ a, (sd.block (c.blockIndex a)).innerRadius < (sd.block (c.blockIndex a)).outerRadius ∧
    (sd.block (c.blockIndex a)).lowerHeight < (sd.block (c.blockIndex a)).upperHeight ∧
    0 ≤ (sd.block (c.blockIndex a)).lowerHeight ∧ 1 ≤ (sd.block (c.blockIndex a)).degree
  off_axis : ∀ a, (sd.block (c.blockIndex a)).onAxis = false → 0 < (sd.block (c.blockIndex a)).innerRadius
  on_axis : ∀ a, (sd.block (c.blockIndex a)).onAxis = true →
    (sd.block (c.blockIndex a)).innerRadius = 0 ∧ (sd.block (c.blockIndex a)).mode = 0 ∧
    24 ≤ c.cutoff * ((sd.block (c.blockIndex a)).outerRadius - (sd.block (c.blockIndex a)).innerRadius) ^ 2
  blocks_apart : ∀ a b, c.blockIndex a ≠ c.blockIndex b →
    volume (⋃ s, cellSolid (sd.block (c.blockIndex a)) s ∩ ⋃ s, cellSolid (sd.block (c.blockIndex b)) s) = 0 ∨
    ((sd.block (c.blockIndex a)).innerRadius = (sd.block (c.blockIndex b)).innerRadius ∧
      (sd.block (c.blockIndex a)).outerRadius = (sd.block (c.blockIndex b)).outerRadius ∧
      (sd.block (c.blockIndex a)).lowerHeight = (sd.block (c.blockIndex b)).lowerHeight ∧
      (sd.block (c.blockIndex a)).upperHeight = (sd.block (c.blockIndex b)).upperHeight ∧
      (sd.block (c.blockIndex a)).mode ≠ (sd.block (c.blockIndex b)).mode)
  interval_bounded : ∀ q, ∀ e ∈ sd.intervalCerts q, IntervalCertificate q e.1 e.2
  axis_bounded : ∀ q, ∀ e ∈ sd.axisCerts q, AxisCertificate q e.1 e.2 (sd.axisCutoff q e)
  axis_gradient : ∀ a, (sd.block (c.blockIndex a)).onAxis = true →
    AxisGradientBound (sd.block (c.blockIndex a)).degree (sd.axisGradient (sd.block (c.blockIndex a)).degree)
  cutoff_pos : 0 < c.cutoff

end Spectral

end CellCert

end Breakdown
