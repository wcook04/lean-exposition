import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.GivenModelRowTurn
import Breakdown.FracCell.GivenModelRows

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

namespace RowTurnBridgeInternal

theorem turnMode_eq_zero_iff {M : CellMesh} {N : ℕ} (RD : RowData M N) {m : ℕ} (hm : 0 < m) (a : Fin N) :
    RD.turnMode m a = 0 ↔ RD.harmonic a = 0 := by
  unfold RowData.turnMode
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h1
    · revert h1
      cases RD.positive a <;> norm_num
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hm'
      · exact_mod_cast h2
  · intro h
    simp [h]

theorem abs_turnMode {M : CellMesh} {N : ℕ} (RD : RowData M N) (m : ℕ) (a : Fin N) :
    |(RD.turnMode m a : ℝ)| = (m : ℝ) * (RD.harmonic a : ℝ) := by
  unfold RowData.turnMode
  split_ifs <;> push_cast <;> simp [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]

theorem cellSet_pos (M : CellMesh) (K : Fin M.cellCount) :
    (if h : (K : ℕ) < M.cellCount then (M.box ⟨K, h⟩).solid else ∅) = (M.box K).solid := by
  rw [dif_pos K.isLt]

theorem outer_pos (M : CellMesh) (K : Fin M.cellCount) :
    (if h : (K : ℕ) < M.cellCount then (M.box ⟨K, h⟩).r₂ else 0) = (M.box K).r₂ := by
  rw [dif_pos K.isLt]

theorem solid_bounded (K : CellBox) : Bornology.IsBounded K.solid := by
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := |K.r₂| + |K.z₂|)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨-, h2, -, h4⟩ := hy
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hrr : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hz : |cylHeight y| ^ 2 = y 2 ^ 2 := by rw [sq_abs]; rfl
  have hz0 : 0 ≤ |cylHeight y| := abs_nonneg _
  have ha : cylRadius y ≤ |K.r₂| := h2.trans (le_abs_self _)
  have hb : |cylHeight y| ≤ |K.z₂| := h4.trans (le_abs_self _)
  have hsum : ∑ i : Fin 3, ‖y i‖ ^ 2 ≤ (|K.r₂| + |K.z₂|) ^ 2 := by
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg K.r₂, abs_nonneg K.z₂]
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i : Fin 3, ‖y i‖ ^ 2) ≤ Real.sqrt ((|K.r₂| + |K.z₂|) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = |K.r₂| + |K.z₂| := Real.sqrt_sq (by positivity)

end RowTurnBridgeInternal

open RowTurnBridgeInternal in
theorem rowTurnData_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (rate : ℝ) (hS : IsGivenData c D A M MD RD)
    (hN : IsRowTurnNumbers c M RD rate) : IsRowTurnData c (turnOf RD c.order rate) := by
  have hm : 0 < c.order := by have := hN.order_ge; omega
  have hR := hS.rows
  have hI := hS.rows_instance
  have hrw : ∀ a, c.rowWeight a = RD.cellWeight (RD.cell a) := fun a => by rw [hI.rowWeight_eq]; rfl
  obtain ⟨hL2, hortho, -⟩ := row_clauses c M RD hS.mesh hR hI hm
  obtain ⟨-, hmix, -⟩ := mix_clauses RD c.order c.rowMax hR
  refine
    { order_ge := hN.order_ge
      row_mode := rowTurn_of c M RD hS.mesh hR hI
      partner_invol := hR.partner_invol
      partner_mode := ?_
      partner_cell := ?_
      partner_weight := ?_
      mode_large := ?_
      mode_multiple := ?_
      cell_measurable := ?_
      cell_bounded := ?_
      cell_turn := ?_
      cell_disjoint := ?_
      row_support := ?_
      cell_radius := ?_
      row_orthonormal := hortho
      row_memLp := hL2
      weight_nonneg := ?_
      const_ge := ?_ }
  · intro a
    show RD.turnMode c.order (RD.partner a) = -RD.turnMode c.order a
    by_cases h0 : RD.harmonic a = 0
    · simp [RowData.turnMode, hR.partner_harmonic, h0]
    · unfold RowData.turnMode
      rw [hR.partner_sign a h0, hR.partner_harmonic]
      cases RD.positive a <;> simp
  · intro a
    show ((RD.cell (RD.partner a) : ℕ)) = RD.cell a
    rw [hR.partner_cell]
  · intro a
    show c.rowWeight (RD.partner a) = c.rowWeight a
    rw [hrw, hrw, hR.partner_cell]
  · intro a ha
    have ha' : RD.turnMode c.order a ≠ 0 := ha
    have hh : RD.harmonic a ≠ 0 := fun h => ha' ((turnMode_eq_zero_iff RD hm a).2 h)
    show (c.order : ℝ) ≤ |(RD.turnMode c.order a : ℝ)|
    rw [abs_turnMode]
    have h1 : (1 : ℝ) ≤ (RD.harmonic a : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hh
    have h2 : (0 : ℝ) ≤ (c.order : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro a
    show (c.order : ℤ) ∣ RD.turnMode c.order a
    unfold RowData.turnMode
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  · intro i
    show MeasurableSet (if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅)
    split_ifs
    · exact RowsInternal.solid_measurableSet _
    · exact MeasurableSet.empty
  · intro i
    show Bornology.IsBounded (if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅)
    split_ifs
    · exact solid_bounded _
    · exact Bornology.isBounded_empty
  · intro i φ y
    show y ∈ (if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅) ↔
      turnBy φ y ∈ (if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅)
    split_ifs
    · exact (RowTurnInternal.solid_turn _ φ y).symm
    · simp
  · intro i j hij
    show volume ((if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅) ∩
      (if h : j < M.cellCount then (M.box ⟨j, h⟩).solid else ∅)) = 0
    by_cases hi : i < M.cellCount
    · by_cases hj : j < M.cellCount
      · rw [dif_pos hi, dif_pos hj]
        refine RowsInternal.solid_inter_null hS.mesh ?_
        intro h
        exact hij (congrArg Fin.val h)
      · rw [dif_neg hj, Set.inter_empty, measure_empty]
    · rw [dif_neg hi, Set.empty_inter, measure_empty]
  · intro a
    refine Filter.Eventually.of_forall fun y hy => ?_
    show y ∈ (if h : ((RD.cell a : ℕ)) < M.cellCount then (M.box ⟨RD.cell a, h⟩).solid else ∅)
    rw [cellSet_pos]
    by_contra hn
    apply hy
    rw [hI.row_eq]
    unfold RowData.rowField
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases h : RD.mix a b = 0
    · simp [h]
    · rw [show RD.testField c.order b y = 0 from Set.indicator_of_notMem (by rwa [← (hmix a b h).1]) _, smul_zero]
  · intro i y hy
    change y ∈ (if h : i < M.cellCount then (M.box ⟨i, h⟩).solid else ∅) at hy
    show horizontalNorm y ≤ (if h : i < M.cellCount then (M.box ⟨i, h⟩).r₂ else 0)
    split_ifs at hy ⊢ with h
    · exact hy.2.1
    · exact absurd hy (Set.notMem_empty y)
  · intro a
    rw [hrw]
    exact (hR.cellWeight_pos _).le
  · refine ⟨hN.rate_nonneg, fun a ha => ?_⟩
    have ha' : RD.turnMode c.order a ≠ 0 := ha
    have hh : RD.harmonic a ≠ 0 := fun h => ha' ((turnMode_eq_zero_iff RD hm a).2 h)
    show c.rowWeight a * (if h : ((RD.cell a : ℕ)) < M.cellCount then (M.box ⟨RD.cell a, h⟩).r₂ else 0) ^ 2 ≤ rate ^ 2
    rw [outer_pos, hrw]
    exact hN.const_ge a hh

end CellSystem

end CellCert

end Breakdown
