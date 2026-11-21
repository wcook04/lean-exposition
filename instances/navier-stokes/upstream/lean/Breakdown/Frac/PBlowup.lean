import Breakdown.Frac.StProfile
import Breakdown.Frac.RExports
import Breakdown.Frac.PAxial
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal

private theorem rotatingSlice_zero (a : ℝ) (U : Space → Space) : rotatingSlice a U 0 = U := by
  funext y
  simp only [rotatingSlice, pushForward, mul_zero, neg_zero, axialRotationSpec.2.1]
  rfl

private theorem dilExponent_pos (α : ℝ) (hα : 1 < α) : 0 < dilExponent α := by
  unfold dilExponent
  have h : 3 / (4 * α) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

end FracInternal

theorem fracMildBlowup_of (h1 : ScaledTransferHolds) (h2 : FracProfileOrbit) (h3 : UnitViscosity)
    (h4 : ProfileExistsIff) (_h5 : RotatingSliceDecay) : FracMildBlowup := by
  intro α hα hα' hex
  obtain ⟨U, P, a, ν, hp⟩ := (h4 α).1 hex
  have hp1 := h3 α hα hα' a ν U P hp
  refine ⟨a, _, _, hp1, ?_⟩
  obtain ⟨⟨F, hG, hK, hD⟩, hC⟩ := Freq.fracFramework_holds α hα
  refine ⟨F, hG, hK, hD, ?_⟩
  intro ε hε
  have horb := h2 α hα hα' a _ _ hp1 F hG hK hD 1 one_pos
  obtain ⟨u, hu0, hclose, hmild, C, κ', hκ', hrate⟩ :=
    h1 Freq.X (dilExponent α) (FracInternal.dilExponent_pos α hα) F _ (hC F hG hK hD _) _ 1 horb
      Freq.testSpan Freq.testDense_holds.2 ε hε
  obtain ⟨φ, hφ, hφe⟩ := Freq.testSpan_holds _ hu0
  refine ⟨φ, u, hφ, hφe.symm, ?_, hmild, C, κ', hκ', hrate⟩
  rw [FracInternal.rotatingSlice_zero] at hclose
  exact hclose

end Breakdown
