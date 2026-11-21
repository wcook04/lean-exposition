import Breakdown.FracCell.EnergyCross
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.FormulaYLinear

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

theorem crossIntegrable_of_setting (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ) (hs : EnergySetting α c K B S I v G H u) :
    CrossIntegrable c K G := by
  have hK := hs.box
  have hf := hs.field
  have hc := hs.form
  intro n a b
  refine ⟨LowEntry.Internal.gradMode_int K hK c.order n hf.measurable_gradient hf.gradient_two a b,
    fun i => ⟨?_, ?_⟩⟩
  · exact FormulaYLinearInternal.mode_int K hK.r_order.1 c.order n (c.modelActuatorGrad i) a b
      (FormulaYLinearInternal.act_int (hc.modelActuatorGrad_data i).1 (hc.modelActuatorGrad_data i).2.1
        (hc.modelActuatorGrad_data i).2.2 hc.cellRegion_bounded c.order n a b) (fun _ _ _ _ _ => rfl)
  · exact FormulaYLinearInternal.mode_int K hK.r_order.1 c.order n (c.modelPinField i) a b
      (FormulaYLinearInternal.act_int (hc.modelPin_data i).1 (hc.modelPin_data i).2.1
        (hc.modelPin_data i).2.2 hc.cellRegion_bounded c.order n a b) (fun _ _ _ _ _ => rfl)

theorem crossForm_closed : CrossFormStatement :=
  fun α _ _ _ _ _ c K B S Cl _ _ _ I v G H u hs =>
    crossForm_holds α c K B S Cl I v G H u hs (crossIntegrable_of_setting α c K B S I v G H u hs)

end Breakdown.CellCert.CellEnergy
