import Breakdown.FracCell.StMesh
import Breakdown.FracCell.PlaneDeleted

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

private theorem stream_radius_zero (L : CellLayout) {k : ℕ} (x : FieldTuple k) (o : ℝ) :
    streamValue L x 0 0 o = 0 := by
  unfold streamValue heightStripMoment
  have h : (volume : Measure (ℝ × ℝ)) (Set.Icc (0 : ℝ) 0 ×ˢ Set.Icc (min 0 o) (max 0 o)) = 0 := by
    rw [Set.Icc_self, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  rw [setIntegral_measure_zero _ h, mul_zero]

theorem streamPlane_of (hS : StreamIndependenceStatement) : StreamPlaneStatement := by
  intro k N c x hx L hord r o hr ho
  rcases hr.eq_or_lt with rfl | hr
  · exact stream_radius_zero L x o
  have key := hS c x hx L hord r 0 o (-o) hr ho (neg_ne_zero.mpr ho)
  have hae := Internal.PlaneDeleted.modes_ae c x L hord
    (fun n => Internal.PlaneDeleted.modes_mirror hx.1 n) 0
  unfold streamValue
  refine Internal.PlaneDeleted.height_zero o 0 r ho le_rfl _ _ _ _ ?_ key
  filter_upwards [hae] with p hp hpos
  obtain ⟨h1, h2, -⟩ := hp hpos
  rw [h1, h2]
  simp [Internal.PlaneDeleted.sR]

end CellCoordinates

end CellCert

end Breakdown
