import Breakdown.CertCell.AssemblyExteriorValueSets

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.ExteriorValueSets

theorem rotate_planePoint (p : ℝ × ℝ) (θ : ℝ) : axialRot θ (planePoint p) = cylPoint p.1 θ p.2 := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, cylPoint, unitVector] <;> ring

theorem eval_cylPoint (hF : ScalarShape.ChartBoundFacts) (P : CellCert.GivenFields.ChartParams)
    (B : ScalarShape.ChartBound) (p : ℝ × ℝ) (θ : ℝ) :
    B.eval P (cylPoint p.1 θ p.2) = B.eval P (planePoint p) := by
  rw [← rotate_planePoint]
  exact (hF P B).2.1 θ (planePoint p)

end Internal.ExteriorValueSets

open Internal.ExteriorValueSets in
theorem exteriorValuesChargeHolds : ExteriorValuesChargeHolds := by
  intro hF k C nE nM D Tb h
  refine ⟨?_, ?_, ?_, h.length_common, h.length_pos, ?_⟩
  · intro ι p hp σ θ u
    rw [(h.charges_eq ι p hp).1, ← eval_cylPoint hF Tb.chart Tb.strain p θ]
    exact h.strain_enclosed p hp σ θ u
  · intro ι p hp
    rw [(h.charges_eq ι p hp).2.1]
    exact h.mean_enclosed p hp
  · intro ι p hp σ θ u
    rw [(h.charges_eq ι p hp).2.2, ← eval_cylPoint hF Tb.chart Tb.waveGrad p θ]
    exact h.wave_enclosed p hp σ θ u
  · intro ι p hp
    rw [(h.charges_eq ι p hp).2.1, (h.charges_eq ι p hp).2.2]
    exact h.valueSets_nonneg p hp

end Assembly

end CertCell

end Breakdown
