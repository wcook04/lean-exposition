import Breakdown.FracCell.Defs
import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

def ChosenAgreeStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → FracCellData.chosenGrad m v =ᵐ[volume] G ∧ FracCellData.chosenSecond m v =ᵐ[volume] H

def ClassAverageRowsStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ F : Space → Space, AEStronglyMeasurable F volume → IsLocalSquareIntegrable (fun y => ‖F y‖ ^ 2) →
    ∀ Q : Space → Space, IsGradientField Q →
      ∃ Q' : Space → Space, IsGradientField Q' ∧ IsClassField c.order Q' ∧
        c.toFracCertData.rows (fun y => F y + Q' y) = c.toFracCertData.rows (fun y => F y + Q y)

def SecondIdentityStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
      (∫ y, fullSecondSq (H y)) = (∫ y, ‖secondTrace (H y)‖ ^ 2) ∧
      (∫ y, curlGradSq (H y)) = (∫ y, ‖secondTrace (H y)‖ ^ 2) ∧
      (∫ y, ‖curlOf (G y)‖ ^ 2) = (∫ y, entrySq (G y))

def CrossIdentityStatement : Prop :=
  ∀ (u w : Space) (Du Dw : Space →L[ℝ] Space),
    Dw u + Du w = crossVec (curlOf Dw) u + crossVec (curlOf Du) w
      + ContinuousLinearMap.adjoint Du w + ContinuousLinearMap.adjoint Dw u

def ModelRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ p ∈ box (c.toCertData α).radius, ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H →
      ∀ κ : Fin k → ℝ, AEStronglyMeasurable ((c.toCertData α).modelField p v κ) volume ∧
        IsLocalSquareIntegrable (fun y => ‖(c.toCertData α).modelField p v κ y‖ ^ 2)

def ModelLowerStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ p ∈ box (c.toCertData α).radius, ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H →
      ∀ κ : Fin k → ℝ, ∀ Q, IsGradientField Q →
        (c.toCertData α).coercivity * (c.toCertData α).size G H κ ^ 2 ≤ (c.toCertData α).modelForm p v κ
          + (c.toCertData α).rows (fun y => (c.toCertData α).modelField p v κ y + Q y) ^ 2
          + (c.toCertData α).pinWeight * ∑ i, (c.toCertData α).modelPin p v i ^ 2

def ModelFormStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ p ∈ box (c.toCertData α).radius, ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H → ∀ P,
      IsWeakFractionalPower α v P → MemLp (driftField α ((c.toCertData α).rotationRate p) v G) 2 volume →
      ∀ κ : Fin k → ℝ, (c.toCertData α).modelForm p v κ - (c.toCertData α).potLoss * (c.toCertData α).size G H κ ^ 2
        ≤ l2Pair ((c.toCertData α).localField α p v G H κ) (negSecondTrace H)

def ModelFieldStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ p ∈ box (c.toCertData α).radius, ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H → ∀ P,
      IsWeakFractionalPower α v P → MemLp (driftField α ((c.toCertData α).rotationRate p) v G) 2 volume →
      ∀ κ : Fin k → ℝ, ∃ Q, IsGradientField Q ∧
        (c.toCertData α).rows (fun y => (c.toCertData α).localField α p v G H κ y
          - (c.toCertData α).modelField p v κ y + Q y) ≤ (c.toCertData α).rowLoss * (c.toCertData α).size G H κ

def ModelPinStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ p ∈ box (c.toCertData α).radius, ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H → ∀ P,
      IsWeakFractionalPower α v P → MemLp (driftField α ((c.toCertData α).rotationRate p) v G) 2 volume →
      ∀ κ : Fin k → ℝ, vecNorm (fun i => (c.toCertData α).modelPin p v i - (c.toCertData α).pins G i)
        ≤ (c.toCertData α).pinLoss * (c.toCertData α).size G H κ

def SplitRowsStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ v G H, IsSecondOrderField (c.toCertData α).order v G H → ∀ P, IsWeakFractionalPower α v P →
      (c.toCertData α).rows ((c.toCertData α).splitField P H) ≤ (c.toCertData α).splitBound * (c.toCertData α).splitEnergy P G H

def SmoothingLowerStatement : Prop :=
  ∀ (lam : ℝ), 0 < lam → ∀ φ : Space → Space, MemLp φ 2 volume →
    (∫ ξ, ratioFn lam (freqPow 2 ξ) * ‖(fieldSymbol φ : Space → Freq.CSpace) ξ‖ ^ 2) ≤ smoothingForm lam φ

end CellCert

end Breakdown
