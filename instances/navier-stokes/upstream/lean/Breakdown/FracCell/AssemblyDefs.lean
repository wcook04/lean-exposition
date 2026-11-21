import Breakdown.FracCell.Defs
import Breakdown.FracCell.FiniteDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

def IsAdmissible {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) : Prop :=
  IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 ∧ IsGradientField x.2.2.2.2 ∧ IsClassField c.order x.2.2.2.2

namespace CellSplit

variable {k N : ℕ} (c : FracCellData k N) (S : CellSplit k N)

def localDensity (α : ℝ) (x : FieldTuple k) (y : Space) : ℝ :=
  (c.innerWeight - c.coercivity) * fullSecondSq (x.2.2.1 y)
    + (c.splitVisc - c.innerWeight) * curlGradSq (x.2.2.1 y)
    + ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (x.2.1 y)‖ ^ 2
      + (c.curlWeight - c.coercivity * c.weight y) * entrySq (x.2.1 y))
    + jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y)
    + ∑ i, x.2.2.2.1 i * entryInner (x.2.1 y) (c.modelActuatorGrad i y)

def stateOf (x : FieldTuple k) (ζ : Fin k → ℝ) : Fin S.slots ⊕ Fin k → ℝ :=
  Sum.elim (S.moment x + S.freeMap *ᵥ ζ) ζ

def cellPart (α : ℝ) (K : Fin S.cellCount) (x : FieldTuple k) (ζ : Fin k → ℝ) : ℝ :=
  (∫ y in S.cell K, localDensity c α x y)
    + ∑ a ∈ Finset.univ.filter (fun a => S.rowCell a = K),
        c.rowWeight a * l2Pair (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) (c.row a) ^ 2
    + ∑ i, 2 * ζ i * ∫ y in S.cell K, entryInner (x.2.1 y) (c.modelPinField i y)

def exteriorPart (α : ℝ) (x : FieldTuple k) : ℝ :=
  ∫ y in (⋃ K, S.cell K)ᶜ, localDensity c α x y

structure IsCellSplit (α : ℝ) : Prop where
  cell_measurable : ∀ K, MeasurableSet (S.cell K)
  cells_apart : ∀ K L, K ≠ L → volume (S.cell K ∩ S.cell L) = 0
  cells_cover : (⋃ K, S.cell K) = c.cellRegion
  row_support : ∀ a, ∀ y ∉ S.cell (S.rowCell a), c.row a y = 0
  moment_zero : S.moment 0 = 0
  moment_additive : ∀ x x', IsAdmissible c x → IsAdmissible c x' → S.moment (x + x') = S.moment x + S.moment x'
  moment_homogeneous : ∀ (r : ℝ) x, IsAdmissible c x → S.moment (r • x) = r • S.moment x
  kappa_slot_injective : Function.Injective S.kappaSlot
  kappa_slot_value : ∀ x, IsAdmissible c x → ∀ i, S.moment x (S.kappaSlot i) = x.2.2.2.1 i
  kappa_slot_free : ∀ i j, S.freeMap (S.kappaSlot i) j = 0
  cell_bound : ∀ K, ∀ x, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
    quadValue (S.cellMatrix K) (S.stateOf x ζ) ≤ S.cellPart c α K x ζ
  exterior_bound : ∀ x, IsAdmissible c x → 0 ≤ S.exteriorPart c α x
  delay_vanish : ∀ j, ∀ x, IsAdmissible c x → ∀ ζ : Fin k → ℝ, quadValue (S.delayForm j) (S.stateOf x ζ) = 0

end CellSplit

structure IsFormData (α : ℝ) {k N : ℕ} (c : FracCellData k N) : Prop where
  base : IsFracCertBase α c.toFracCertData
  cellRegion_bounded : Bornology.IsBounded c.cellRegion
  centre_bounds : ∃ C : ℝ, ∀ y, ‖c.centre y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
    ‖c.centreGrad y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))
  model_measurable : AEStronglyMeasurable c.modelVelocity volume ∧ AEStronglyMeasurable c.modelCurl volume ∧
    AEStronglyMeasurable c.modelStrain volume ∧ AEStronglyMeasurable c.modelCurlGrad volume
  model_bounded : ∃ C : ℝ, ∀ y ∈ c.cellRegion, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C ∧
    ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C
  model_outside : ∀ y ∉ c.cellRegion, c.modelStrain y = c.centreStrain y ∧ c.modelCurlGrad y = c.centreCurlGrad y
  modelActuatorGrad_data : ∀ i, AEStronglyMeasurable (c.modelActuatorGrad i) volume ∧
    Integrable (fun y => entrySq (c.modelActuatorGrad i y)) ∧ ∀ y ∉ c.cellRegion, c.modelActuatorGrad i y = 0
  modelPin_data : ∀ i, AEStronglyMeasurable (c.modelPinField i) volume ∧
    Integrable (fun y => entrySq (c.modelPinField i y)) ∧ ∀ y ∉ c.cellRegion, c.modelPinField i y = 0

end Assembly

end CellCert

end Breakdown
