import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

theorem keyPhase_add_time (P : ShapeParams) (κ : FieldKey) (σ τ : ℝ) (y : Space) :
    keyPhase P κ (σ + τ) y =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * τ : ℝ) : ℂ) * Complex.I) * keyPhase P κ σ y := by
  unfold keyPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem keyTimeShift_holds : KeyTimeShift := by
  intro P κ A σ τ y
  funext i
  simp only [keyVector]
  rw [keyPhase_add_time, mul_assoc]

end GivenShape

end CertCell

end Breakdown
