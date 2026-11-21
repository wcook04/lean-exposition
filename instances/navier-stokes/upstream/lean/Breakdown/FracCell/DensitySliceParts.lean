import Breakdown.FracCell.CellDensityModesParts

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def IsCircleSliceRegular (m : ℕ) (f : ℝ → ℝ) : Prop :=
  MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))) ∧ ∀ᵐ θ ∂volume, f (θ + 2 * π / m) = f θ

def IsCircleSliceData {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (p : ℝ × ℝ) : Prop :=
  (∀ a, IsCircleSliceRegular c.order (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) a)) ∧
  (∀ a b, IsCircleSliceRegular c.order (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b)) ∧
  (∀ a b d, IsCircleSliceRegular c.order (fun θ => frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) a b d)) ∧
  (∀ a b, AEStronglyMeasurable (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b)
      (volume.restrict (Set.Ioc 0 (2 * π))) ∧
    AEStronglyMeasurable (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b)
      (volume.restrict (Set.Ioc 0 (2 * π)))) ∧
  (∃ C : ℝ, ∀ θ a b, |frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b| ≤ C ∧
    |frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b| ≤ C) ∧
  (∀ i a b, MemLp (fun θ => frameMat θ (c.modelActuatorGrad i (cylPoint p.1 θ p.2)) a b) 2
      (volume.restrict (Set.Ioc 0 (2 * π))) ∧
    MemLp (fun θ => frameMat θ (c.modelPinField i (cylPoint p.1 θ p.2)) a b) 2
      (volume.restrict (Set.Ioc 0 (2 * π)))) ∧
  ∀ θ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p

def CircleSliceRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → IsAxisymmetricWeight c K → IsModelMirror c K → K.solid ⊆ c.cellRegion →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), IsCircleSliceData c x p

def quadraticDensity {k N : ℕ} (c : FracCellData k N) (α : ℝ) (x : FieldTuple k) (y : Space) : ℝ :=
  (c.innerWeight - c.coercivity) * CellCert.fullSecondSq (x.2.2.1 y)
    + (c.splitVisc - c.innerWeight) * CellCert.curlGradSq (x.2.2.1 y)
    + ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (x.2.1 y)‖ ^ 2
      + (c.curlWeight - c.coercivity * c.weight y) * entrySq (x.2.1 y))

def CircleSliceQuadraticStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N), 3 ≤ c.order → ∀ x : FieldTuple k, ∀ p : ℝ × ℝ,
    IsCircleSliceData c x p →
      IntervalIntegrable (fun θ => quadraticDensity c α x (cylPoint p.1 θ p.2)) volume 0 (2 * π) ∧
      HasSum (fun n : ℤ => modeLocalDensity c α x n p)
        ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), quadraticDensity c α x (cylPoint p.1 θ p.2))

def CircleSliceCouplingStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N), 3 ≤ c.order → ∀ x : FieldTuple k, ∀ p : ℝ × ℝ,
    IsCircleSliceData c x p →
      IntervalIntegrable (fun θ => jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
        (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2))) volume 0 (2 * π) ∧
      (∫ θ in (0 : ℝ)..(2 * π), jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
        (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2))) = 2 * π * modeCoupling c x p

end CellAnalysis

end CellCert

end Breakdown
