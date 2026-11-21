import Breakdown.FracCell.Defs
import Breakdown.FracCell.ExteriorDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def IsGradientPair (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) : Prop :=
  AEStronglyMeasurable v volume ∧ MemLp v 6 volume ∧ AEStronglyMeasurable G volume ∧
    Integrable (fun y => entrySq (G y)) ∧ IsWeakGradientOf v G

def IsSecondDerivPair (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop :=
  AEStronglyMeasurable G volume ∧ Integrable (fun y => entrySq (G y)) ∧ AEStronglyMeasurable H volume ∧
    Integrable (fun y => fullSecondSq (H y)) ∧ IsWeakSecondDerivOf G H

def SixthPowerConstStatement (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ v G, IsGradientPair v G → (∫ y, ‖v y‖ ^ 6) ≤ C ^ 6 * (∫ y, entrySq (G y)) ^ 3

def KernelBound (V : Space → ℝ) (Λ : ℝ) : Prop :=
  (∀ y, 0 ≤ V y) ∧ Measurable V ∧
    ∀ x, Integrable (fun y => V y / (4 * Real.pi * ‖x - y‖)) ∧ (∫ y, V y / (4 * Real.pi * ‖x - y‖)) ≤ Λ

def KernelPotentialStatement : Prop :=
  ∀ (V : Space → ℝ) (Λ : ℝ), KernelBound V Λ → ∀ v G, IsGradientPair v G →
    Integrable (fun y => V y * ‖v y‖ ^ 2) ∧ (∫ y, V y * ‖v y‖ ^ 2) ≤ Λ * ∫ y, entrySq (G y)

def turnBy (φ : ℝ) (y : Space) : Space :=
  EuclideanSpace.single 0 (Real.cos φ * y 0 - Real.sin φ * y 1) +
    EuclideanSpace.single 1 (Real.sin φ * y 0 + Real.cos φ * y 1) + EuclideanSpace.single 2 (y 2)

namespace CellSumData

variable (D : CellSumData) (m : ℕ)

end CellSumData

structure IsCellSumData (m : ℕ) (V : Space → ℝ) (D : CellSumData) : Prop where
  order_even : Even m ∧ 4 ≤ m
  measurable : Measurable V
  nonneg : ∀ y, 0 ≤ V y
  turn_invariant : ∀ y, V (turnBy (2 * Real.pi / m) y) = V y
  mirror_even : ∀ y, V (mirror y) = V y
  piece_box : ∀ b, 0 ≤ D.pieceRhoLo b ∧ (∀ h, D.pieceRhoHi b = some h → D.pieceRhoLo b ≤ h) ∧ 0 ≤ D.pieceZLo b ∧
    (∀ h, D.pieceZHi b = some h → D.pieceZLo b ≤ h)
  piece_solid : ∀ b, ∀ y ∈ D.pieceSolid b, D.pieceRhoLo b ≤ horizontalNorm y ∧
    (∀ h, D.pieceRhoHi b = some h → horizontalNorm y ≤ h) ∧ D.pieceZLo b ≤ y 2 ∧ (∀ h, D.pieceZHi b = some h → y 2 ≤ h)
  solid_measurable : ∀ b, MeasurableSet (D.pieceSolid b)
  solid_turn : ∀ b (φ : ℝ) y, y ∈ D.pieceSolid b ↔ turnBy φ y ∈ D.pieceSolid b
  sup_le : ∀ b, ∀ᵐ y ∂volume, y ∈ D.pieceSolid b → V y ≤ D.pieceSup b
  sup_nonneg : ∀ b, 0 ≤ D.pieceSup b
  mass_integrable : ∀ b, MeasureTheory.IntegrableOn V (D.pieceSolid b)
  mass_le : ∀ b, (∫ y in D.pieceSolid b, V y) ≤ D.pieceMass b
  support : ∀ y, V y ≠ 0 → ∃ b, y ∈ D.pieceSolid b ∨ mirror y ∈ D.pieceSolid b
  box_cover : ∀ ρ z : ℝ, 0 ≤ ρ → 0 ≤ z → ∃ a, D.boxRhoLo a ≤ ρ ∧ (∀ h, D.boxRhoHi a = some h → ρ ≤ h) ∧
    D.boxZLo a ≤ z ∧ (∀ h, D.boxZHi a = some h → z ≤ h)
  box_lower : ∀ a, 0 ≤ D.boxRhoLo a ∧ 0 ≤ D.boxZLo a
  near_valid : ∀ a b mirrored, D.rule a b mirrored = 2 →
    0 < D.sectorLength a b mirrored ∧ 0 < D.sectorConst m a b ∧ (D.pieceRhoHi b).isSome ∧ (D.pieceZHi b).isSome
  box_sum : ∀ a, (∑ b, ∑ mirrored : Bool, D.pairTerm m a b mirrored) ≤ D.boxBound a

structure RowTurnData (N : ℕ) where
  partner : Fin N → Fin N
  modeNum : Fin N → ℤ
  cellOf : Fin N → ℕ
  cellSet : ℕ → Set Space
  outerRadius : ℕ → ℝ
  rateRowConst : ℝ

structure IsRowTurnData {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N) : Prop where
  order_ge : 2 ≤ c.order
  row_mode : ∀ a (φ : ℝ) y, horizontalNorm y ≠ 0 → c.row a (turnBy φ y) =
    turnBy φ (Real.cos ((T.modeNum a : ℝ) * φ) • c.row a y + Real.sin ((T.modeNum a : ℝ) * φ) • c.row (T.partner a) y)
  partner_invol : ∀ a, T.partner (T.partner a) = a
  partner_mode : ∀ a, T.modeNum (T.partner a) = -T.modeNum a
  partner_cell : ∀ a, T.cellOf (T.partner a) = T.cellOf a
  partner_weight : ∀ a, c.rowWeight (T.partner a) = c.rowWeight a
  mode_large : ∀ a, T.modeNum a ≠ 0 → (c.order : ℝ) ≤ |(T.modeNum a : ℝ)|
  mode_multiple : ∀ a, (c.order : ℤ) ∣ T.modeNum a
  cell_measurable : ∀ i, MeasurableSet (T.cellSet i)
  cell_bounded : ∀ i, Bornology.IsBounded (T.cellSet i)
  cell_turn : ∀ i (φ : ℝ) y, y ∈ T.cellSet i ↔ turnBy φ y ∈ T.cellSet i
  cell_disjoint : ∀ i j, i ≠ j → volume (T.cellSet i ∩ T.cellSet j) = 0
  row_support : ∀ a, ∀ᵐ y ∂volume, c.row a y ≠ 0 → y ∈ T.cellSet (T.cellOf a)
  cell_radius : ∀ i, ∀ y ∈ T.cellSet i, horizontalNorm y ≤ T.outerRadius i
  row_orthonormal : ∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0
  row_memLp : ∀ a, MemLp (c.row a) 2 volume
  weight_nonneg : ∀ a, 0 ≤ c.rowWeight a
  const_ge : 0 ≤ T.rateRowConst ∧ ∀ a, T.modeNum a ≠ 0 → c.rowWeight a * T.outerRadius (T.cellOf a) ^ 2 ≤ T.rateRowConst ^ 2

def RowModeGradientStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N), IsRowTurnData c T →
    ∀ v G H, IsSecondOrderField c.order v G H →
      (∑ a, c.rowWeight a * ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair v (c.row a) ^ 2)
        ≤ T.rateRowConst ^ 2 * ∫ y, entrySq (G y)

def SupNormStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
      ∀ᵐ y ∂volume, ‖v y‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ z, entrySq (G z)) *
        Real.sqrt (∫ z, ‖secondTrace (H z)‖ ^ 2)

structure CentreKernelSplit (k : ℕ) where
  supBound : (Fin k → ℝ) → ℝ
  kernelBound : ℝ

structure IsCentreKernelSplit {k N : ℕ} (c : FracCellData k N) (S : CentreKernelSplit k) : Prop where
  sup_le : ∀ p ∈ box c.radius, ∀ y, ‖c.profile p y - c.centre y‖ ≤ S.supBound p
  kernel : ∀ p ∈ box c.radius,
    KernelBound (fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2) (S.kernelBound ^ 2)
  bound_nonneg : 0 ≤ S.kernelBound

end Reduction

end CellCert

end Breakdown
