import Breakdown.FracCell.ReductionAdjointDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def modeEnergy (v : Space → Space) : ENNReal :=
  ∑' k : ℤ, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 *
      ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart v) k q.1 q.2‖ ^ 2
        + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart v) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))

def modePairing (v F : Space → Space) : ENNReal :=
  ∑' k : ℤ, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 *
      (‖angularMode (horizontalPart v) k q.1 q.2‖ * ‖angularMode (horizontalPart F) k q.1 q.2‖
        + ‖angularMode (verticalPart v) k q.1 q.2‖ * ‖angularMode (verticalPart F) k q.1 q.2‖))

def ModeInverseSquareStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → modeEnergy v ≤ ENNReal.ofReal (∫ y, entrySq (G y))

def ModePairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → ∀ F : Space → Space, AEStronglyMeasurable F volume →
      MemLp (fun y => ‖y‖ • F y) 2 volume →
      ENNReal.ofReal |∫ y, inner ℝ (v y) (F y)| ≤ modePairing v F

def ModeMeasurableStatement : Prop :=
  ∀ u : Space → ℂ, AEStronglyMeasurable u volume → ∀ k : ℤ,
    AEStronglyMeasurable (fun q : ℝ × ℝ => angularMode u k q.1 q.2)
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))

def ringRadius (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def ringFrame (c : Fin 3) (y : Space) : Space :=
  match c with
  | 0 => EuclideanSpace.single 0 (y 0 / ringRadius y) + EuclideanSpace.single 1 (y 1 / ringRadius y)
  | 1 => EuclideanSpace.single 0 (-(y 1 / ringRadius y)) + EuclideanSpace.single 1 (y 0 / ringRadius y)
  | 2 => EuclideanSpace.single 2 1

def frameModeSq (G : Space → (Space →L[ℝ] Space)) (k : ℤ) (ρ z : ℝ) : ℝ :=
  ∑ c : Fin 3, (‖angularMode (horizontalPart fun y => G y (ringFrame c y)) k ρ z‖ ^ 2
    + ‖angularMode (verticalPart fun y => G y (ringFrame c y)) k ρ z‖ ^ 2)

def GradientModeSumStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
      ∑' k : ℤ, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2) ≤ ENNReal.ofReal (∫ y, entrySq (G y))

def FrameInverseSquareStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → ∀ k : ℤ,
      ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart v) k q.1 q.2‖ ^ 2
            + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart v) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) ≤
      ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2)

end Reduction

end CellCert

end Breakdown
