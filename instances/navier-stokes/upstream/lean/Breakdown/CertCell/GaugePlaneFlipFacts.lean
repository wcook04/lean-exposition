import Breakdown.CertCell.GaugeKeyStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace PlaneFlipFacts

open CellCert.CellFormula CellCert.CellAnalysis

def IsAxisAdmissibleTest (lo : ℝ) (t : ℝ → ℝ) : Prop :=
  0 < lo ∨ (lo = 0 ∧ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, t r = r * t₀ r)

def planeGrad (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeGrad ξ G 0 (planePoint p) (a, b)

def planeSlope (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, c, b)

def planeVelocity (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeVel ξ v 0 (planePoint p) a

def IsSquareIntegrableNear (Q : Space → Space) : Prop :=
  AEStronglyMeasurable Q volume ∧ ∀ R : ℝ, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖Q y‖ ^ 2) < ⊤

def StripDataFlipAxisHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (lo hi h h' : ℝ) (wt t : ℝ → ℝ),
      0 ≤ lo → lo < hi → 0 < h → 0 < h' → Continuous wt → Continuous t →
      heightStripMoment 0 h lo hi wt (planeVelocity (flipLabel ξ) v a) (planeGrad (flipLabel ξ) G a 2) t
        = (frameSign a : ℂ) * heightStripMoment 0 h' lo hi wt (planeVelocity ξ v a) (planeGrad ξ G a 2) t ∧
      (IsAxisAdmissibleTest lo (fun r => wt r * t r) →
        heightStripMoment 0 h lo hi wt (planeGrad (flipLabel ξ) G a 2) (planeSlope (flipLabel ξ) H a 2 2) t
          = -((frameSign a : ℂ) * heightStripMoment 0 h' lo hi wt (planeGrad ξ G a 2) (planeSlope ξ H a 2 2) t))

def CornerDataFlipAxisHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (cr orr h h' : ℝ), 0 < cr → 0 ≤ orr → cr ≠ orr → 0 < h → 0 < h' →
      cornerMoment cr orr 0 h (planeVelocity (flipLabel ξ) v a) (planeGrad (flipLabel ξ) G a 0)
          (planeGrad (flipLabel ξ) G a 2) (planeSlope (flipLabel ξ) H a 0 2)
        = (frameSign a : ℂ) * cornerMoment cr orr 0 h' (planeVelocity ξ v a) (planeGrad ξ G a 0)
          (planeGrad ξ G a 2) (planeSlope ξ H a 0 2)

def PressureStripFlipHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q →
    (∀ᵐ y, Q (flipPoint y) = flipPoint (Q y)) → ∀ n : ℤ,
    ∀ (lo hi h h' : ℝ) (wt t : ℝ → ℝ), IsAxisAdmissibleTest lo (fun r => wt r * t r) → lo < hi → 0 < h → 0 < h' →
      Continuous wt → Continuous t →
      heightStripMoment 0 h lo hi wt (fun p => presMode m (-n) q p.1 p.2) (fun p => modeVec m (-n) Q p.1 p.2 2) t
        = heightStripMoment 0 h' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t

def PotentialShiftHolds : Prop :=
  ∀ (Q : Space → Space) (q : Space → ℝ) (C : ℝ), IsPotentialOf Q q → IsPotentialOf Q (fun y => q y - C)

def PotentialOfGradientHolds : Prop :=
  ∀ Q : Space → Space, SteadyCert.IsGradientField Q → IsPotentialOf Q (potentialOf Q)

def HarmonicPressureSquareHolds : Prop :=
  ∀ Pg : ℝ → Space → Space, CellCalculus.IsPeriodicPressure Pg → ∀ ν : ℤ,
    IsSquareIntegrableNear (CellCalculus.harmonicCos ν Pg) ∧ IsSquareIntegrableNear (CellCalculus.harmonicSin ν Pg)

def HarmonicPressureFlipHolds : Prop :=
  ∀ Pg : ℝ → Space → Space, CellCalculus.IsPeriodicPressure Pg →
    (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) → ∀ ν : ℤ,
      (∀ᵐ y, CellCalculus.harmonicCos ν Pg (flipPoint y) = flipPoint (CellCalculus.harmonicCos ν Pg y)) ∧
      (∀ᵐ y, CellCalculus.harmonicSin ν Pg (flipPoint y) = flipPoint (CellCalculus.harmonicSin ν Pg y))

def PeriodicSecondOrderHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → CellCalculus.IsPeriodicSecondOrder v G H

end PlaneFlipFacts

end CertCell

end Breakdown
