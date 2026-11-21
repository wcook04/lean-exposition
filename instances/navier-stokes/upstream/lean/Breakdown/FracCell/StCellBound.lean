import Breakdown.FracCell.CellDataDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

variable {k N : ℕ}

def IsAxisymmetricWeight (c : FracCellData k N) (K : CellBox) : Prop :=
  ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p

def IsModelMirror (c : FracCellData k N) (K : CellBox) : Prop :=
  ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
    c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
    (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
    (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
    ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
      (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u)))

def modeLocalDensity (c : FracCellData k N) (α : ℝ) (x : FieldTuple k) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  (c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
    + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p
    + CellScalars.densityForm c α p (fun a b => gradMode c.order n x.2.1 a b p)

def modeCoupling (c : FracCellData k N) (x : FieldTuple k) (p : ℝ × ℝ) : ℝ :=
  (∑' n : ℤ, ∑' n' : ℤ,
    waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p)
      (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
      (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)).re

def modeFieldPair (c : FracCellData k N) (G E : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  (∑' n : ℤ, entryPairing (fun a b => gradMode c.order n G a b p) (fun a b => modeMat c.order n E p.1 p.2 a b)).re

def CellDensityModesStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → IsAxisymmetricWeight c K → IsModelMirror c K → K.solid ⊆ c.cellRegion →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∫ y in K.solid, CellSplit.localDensity c α x y) =
          4 * Real.pi * ∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
            + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p) ∧
        ∀ i, (∫ y in K.solid, entryInner (x.2.1 y) (c.modelPinField i y)) =
          4 * Real.pi * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p

def CellFormBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (Sp : CellSplit k N)
      (R : CellRows N Sp.slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ (K₂ : Fin Sp.cellCount), Sp.cell K₂ =ᵐ[volume] K.solid → (∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ ≤ Sp.cellPart c α K₂ x ζ

end CellAnalysis

end CellCert

end Breakdown
