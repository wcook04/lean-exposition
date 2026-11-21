import Breakdown.FracCell.SharpRowIdentity
import Breakdown.FracCell.SharpTargetSquare

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpTargetSquare.Internal

theorem rowCouplingSquare_holds : RowCouplingSquareStatement := by
  intro α _ _ k N c hform K S B Cl slots R hcell _ a ha n
  have hK := hcell.box
  obtain ⟨C0, hC0⟩ := hform.model_bounded
  obtain ⟨mV, mC, _, _⟩ := hform.model_measurable
  have hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)) := Bd_rHat hK
  have bV : ∀ β j, Bd K (fun p => modeVec c.order β c.modelVelocity p.1 p.2 j) :=
    fun β j => modeVec_bd hK mV _ _ j (fun y hy => (hC0 y (hcell.solid_in_region hy)).1)
  have bC : ∀ β j, Bd K (fun p => modeVec c.order β c.modelCurl p.1 p.2 j) :=
    fun β j => modeVec_bd hK mC _ _ j (fun y hy => (hC0 y (hcell.solid_in_region hy)).2.1)
  have wRow : ∀ n j, IsWeightedSquareOn K (fun p => CellScalars.rowMode c a n p j) :=
    fun n j => modeVec_W hK (hform.base.row_two a) _ _ j
  refine ⟨fun i q => rowS_W hK c R a n hR bV wRow i q, fun i => rowV_W hK c R a n hR bC wRow i, fun i q => ?_⟩
  unfold CellScalars.rowCouplingFolded
  by_cases hn : n ∈ S.resolved
  · simp only [if_pos hn]
    exact rowS_W hK c R a n hR bV wRow i q
  · simp only [if_neg hn]
    exact fold_W hK _ (rowS_W hK c R a n hR bV wRow) (rowV_W hK c R a n hR bC wRow) i q

end Breakdown.CellCert.CellAnalysis
