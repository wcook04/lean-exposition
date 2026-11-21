import Breakdown.FracCell.StMesh
import Breakdown.FracCell.RelStream

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

def RadialAxisCrossStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (R o z₁ z₂ : ℝ), 0 < R → o < 0 → z₁ < z₂ →
      radialStripMoment R o z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0) (fun _ => 1)
        = radialStripMoment R 0 z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0) (fun _ => 1)

theorem fluxRadial_of (hC : CylinderFluxStatement) (hA : RadialAxisCrossStatement)
    (hI : StreamIndependenceStatement) : FluxRadialStatement := by
  intro k N c x hx L hL S hS o o' hrad hlev hlo ho ho' c0 hc0
  have hso := hx.1
  have hlh := hS.lo_lt_hi
  have hc : c0 * S.testCoef 0 0 = 1 := by
    have h := hc0 S.lo ⟨le_rfl, hlh.le⟩
    rw [Internal.RelStream.test_zero] at h
    linarith
  have e1 : streamValue L x S.level S.lo o = streamValue L x S.level S.lo S.hi :=
    hI c x hx L hL S.level S.lo o S.hi hlev ho (ne_of_gt hlh)
  have e2 : streamValue L x S.level S.hi o' = streamValue L x S.level S.hi S.lo :=
    hI c x hx L hL S.level S.hi o' S.lo hlev ho' (ne_of_lt hlh)
  rw [e1, e2]
  simp only [FaceSegment.moment, hrad, if_true, Internal.RelStream.test_zero]
  rw [Internal.RelStream.radialStrip_const]
  have ev : ∀ a, L.velMode 0 x a = fun p => modeVec c.order 0 x.1 p.1 p.2 a := by
    intro a; funext p; rw [← hL]; rfl
  have eg : ∀ a b, L.gradModeOf 0 x a b = gradMode c.order 0 x.2.1 a b := by
    intro a b; rw [← hL]; rfl
  simp only [streamValue, ev, eg]
  have hrm : radialStripMoment S.level S.other S.lo S.hi (fun p => modeVec c.order 0 x.1 p.1 p.2 0)
      (gradMode c.order 0 x.2.1 0 0) (fun _ => 1) =
      radialStripMoment S.level (max S.other 0) S.lo S.hi (fun p => modeVec c.order 0 x.1 p.1 p.2 0)
      (gradMode c.order 0 x.2.1 0 0) (fun _ => 1) := by
    rcases le_or_gt 0 S.other with h0 | h0
    · rw [max_eq_left h0]
    · rw [max_eq_right h0.le]
      exact hA c.order x.1 x.2.1 x.2.2.1 hso S.level S.other S.lo S.hi hlev h0 hlh
  have hne : max S.other 0 ≠ S.level := by
    rcases le_or_gt 0 S.other with h0 | h0
    · rw [max_eq_left h0]; exact hS.other_ne
    · rw [max_eq_right h0.le]; exact ne_of_lt hlev
  have key := hC c.order x.1 x.2.1 x.2.2.1 hso S.level (max S.other 0) S.lo S.hi hlev (le_max_right _ _) hne hlh
  rw [hrm]
  have hc' : (c0 : ℂ) * (S.testCoef 0 0 : ℂ) = 1 := by exact_mod_cast hc
  push_cast
  linear_combination key + ((S.level : ℂ) * radialStripMoment S.level (max S.other 0) S.lo S.hi
    (fun p => modeVec c.order 0 x.1 p.1 p.2 0) (gradMode c.order 0 x.2.1 0 0) (fun _ => 1)) * hc'

end CellCoordinates

end CellCert

end Breakdown
