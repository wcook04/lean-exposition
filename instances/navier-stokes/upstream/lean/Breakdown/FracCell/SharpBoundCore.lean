import Breakdown.FracCell.SharpCoreSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

def unresolvedRowPair {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else
    (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
      (entryPairing (fun i q => gradMode c.order n x.2.1 i q p) (rowCouplingStrain c K R a n p)
        + vecPair (modeVec c.order n x.1 p.1 p.2) (rowCouplingVelocity c K R a n p))).re

def unresolvedRowCharge {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (Cl : CellClasses)
    (x : FieldTuple k) : ℝ :=
  ∫ p in K.rect, p.1 * ∑' n : ℤ, (if n ∈ S.resolved ∪ S.band then 0 else
    ∑ i, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 * curlSq (fun a b => gradMode c.order n x.2.1 a b p)
      + Cl.curlDev i p ^ 2 * vecSq (modeVec c.order n x.1 p.1 p.2)))

end CellScalars

def SharpRowIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      2 / (4 * Real.pi) * ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)
        = CellScalars.sharpRowForm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
          + 2 * ∑ a ∈ R.rowSet, μ a * ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n

def UnresolvedRowClassStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      -(2 * ∑ a ∈ R.rowSet, μ a * ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n)
        ≤ ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2 + CellScalars.unresolvedRowCharge c K S Cl x

def SharpYChargeStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      CellScalars.localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
          + CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
              (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
          + CellScalars.unresolvedRowCharge c K S Cl x
        ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
              + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
          + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p)

def SharpRowPartStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
      CellScalars.sharpRowForm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
          - ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2
        ≤ CellScalars.unresolvedRowCharge c K S Cl x + 2 / (4 * Real.pi) *
            ∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)

theorem sharpRowPart_of (hI : SharpRowIdentityStatement) (hC : UnresolvedRowClassStatement) :
    SharpRowPartStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx μ hμ
  have e := hI α h1 h2 c hc K S B Cl R hd hw x hx μ hμ
  have b := hC α h1 h2 c hc K S B Cl R hd hw x hx μ hμ
  linarith

theorem sharpBound_of_parts (hR : SharpRowPartStatement) (hY : SharpYChargeStatement) :
    SharpBoundStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx ζ
  exact ⟨CellScalars.unresolvedRowCharge c K S Cl x, hY α h1 h2 c hc K S B Cl R hd hw x hx ζ,
    fun μ hμ => hR α h1 h2 c hc K S B Cl R hd hw x hx μ hμ⟩

theorem sharpBound_of (hI : SharpRowIdentityStatement) (hC : UnresolvedRowClassStatement)
    (hY : SharpYChargeStatement) : SharpBoundStatement :=
  sharpBound_of_parts (sharpRowPart_of hI hC) hY

end CellAnalysis

end CellCert

end Breakdown
