import Breakdown.FracCell.ExteriorDefs

open MeasureTheory

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

def rayRegion (R : Space → ℝ) : Set Space := {y | R y < ‖y‖}

def RayLineStatement : Prop :=
  ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → ContDiff ℝ 1 g → HasCompactSupport g →
    (∫ r in Set.Ioi a, g r ^ 2) ≤ 4 * ∫ r in Set.Ioi a, r ^ 2 * deriv g r ^ 2

def RaySmoothStatement : Prop :=
  ∀ (R : Space → ℝ) (R₀ R₁ : ℝ), Measurable R → 0 < R₀ → (∀ y, R₀ ≤ R y ∧ R y ≤ R₁) →
    (∀ (t : ℝ) (y : Space), 0 < t → R (t • y) = R y) →
    ∀ u : Space → Space, ContDiff ℝ ∞ u → HasCompactSupport u →
      (∫ y in rayRegion R, ‖u y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * ∫ y in rayRegion R, entrySq (fderiv ℝ u y)

def RayWeakStatement : Prop :=
  ∀ (R : Space → ℝ) (R₀ R₁ : ℝ), Measurable R → 0 < R₀ → (∀ y, R₀ ≤ R y ∧ R y ≤ R₁) →
    (∀ (t : ℝ) (y : Space), 0 < t → R (t • y) = R y) →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
      MemLp v 6 volume → AEStronglyMeasurable G volume → Integrable (fun y => entrySq (G y)) →
      IsWeakGradientOf v G →
      IntegrableOn (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) (rayRegion R) ∧
        (∫ y in rayRegion R, ‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * ∫ y in rayRegion R, entrySq (G y)

def ExteriorPointwiseStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (e : ExteriorData), IsExteriorData α c e → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ y ∉ c.cellRegion,
        ExteriorData.gradientCoef c e α y * entrySq (x.2.1 y)
            - (traceFreeConst / 2) * e.waveCurlGradBound y / e.splitLength y * ‖x.1 y‖ ^ 2
            - traceFreeConst * e.meanCurlGradBound y * ‖x.1 y‖ * Real.sqrt (entrySq (x.2.1 y))
          ≤ CellSplit.localDensity c α x y

def ExteriorNonnegStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (e : ExteriorData), IsExteriorData α c e → ∀ x : FieldTuple k, IsAdmissible c x →
      0 ≤ ∫ y in c.cellRegionᶜ, CellSplit.localDensity c α x y

def ExteriorPartNonnegStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (e : ExteriorData), IsExteriorData α c e → ∀ (S : CellSplit k N),
      (⋃ K, S.cell K) = c.cellRegion →
      ∀ x : FieldTuple k, IsAdmissible c x → 0 ≤ S.exteriorPart c α x

end Exterior

end CellCert

end Breakdown
