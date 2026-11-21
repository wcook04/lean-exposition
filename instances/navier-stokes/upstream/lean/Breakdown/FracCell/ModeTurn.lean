import Breakdown.FracCell.SharpRowIdentity
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.CircleWeak

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

private theorem rect_radius_pos_ae (K : CellBox) (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  have hline : volume ({(0 : ℝ)} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hoff : ∀ᵐ p : ℝ × ℝ ∂volume, p ∉ ({(0 : ℝ)} ×ˢ (Set.univ : Set ℝ)) :=
    measure_eq_zero_iff_ae_notMem.1 hline
  filter_upwards [ae_restrict_of_ae hoff,
    ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet K.rect)] with p hp hm
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hm.1.1
  have hne : p.1 ≠ 0 := fun h => hp ⟨h, Set.mem_univ _⟩
  exact lt_of_le_of_ne h0 (Ne.symm hne)

theorem modeTurn_holds : ModeTurnStatement := by
  intro m v G H hs K hK n
  filter_upwards [ae_restrict_of_ae
      (CellFormula.angularMode CellEnergy.circleWeak m v G H hs n),
    rect_radius_pos_ae K hK] with p hp hpos
  obtain ⟨h0, h1, h2⟩ := hp hpos
  funext a
  fin_cases a <;> simp [turnVec, h0, h1, h2]

end Breakdown.CellCert.CellAnalysis
