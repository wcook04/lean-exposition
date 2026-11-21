import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace PiecePerturbationInternal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem extendPiece_eq {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    extendPiece f t = f ⟨t, ht⟩ := by
  unfold extendPiece
  rw [dif_pos hT, Set.IccExtend_of_mem hT f ht]

theorem extendPiece_add {T : ℝ} (f g : Piece X T) :
    extendPiece (f + g) = extendPiece f + extendPiece g := by
  funext t
  unfold extendPiece
  by_cases hT : 0 ≤ T
  · simp only [dif_pos hT, Pi.add_apply, Set.IccExtend_apply, ContinuousMap.add_apply]
  · simp only [dif_neg hT, Pi.add_apply, add_zero]

theorem continuous_extendPiece {T : ℝ} (f : Piece X T) : Continuous (extendPiece f) := by
  by_cases hT : 0 ≤ T
  · have h : extendPiece f = Set.IccExtend hT f := by
      funext t
      unfold extendPiece
      rw [dif_pos hT]
    rw [h]
    exact f.continuous.Icc_extend'
  · have h : extendPiece f = fun _ => (0 : X) := by
      funext t
      unfold extendPiece
      rw [dif_neg hT]
    rw [h]
    exact continuous_const

theorem norm_extendPiece_le {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : ‖extendPiece f t‖ ≤ ‖f‖ := by
  rw [extendPiece_eq hT f ht]
  exact f.norm_coe_le_norm _

end PiecePerturbationInternal

open PiecePerturbationInternal in
theorem piecePerturbation_of (h1 : VarConstIntegralStatement) (h2 : PieceOperatorStatement) :
    PiecePerturbationStatement := by
  intro X _ _ _ H T ub v x hT _ hub hv
  obtain ⟨hB, -, hF, -⟩ := h2 X H T hT
  have hT0 : 0 ≤ T := hT.le
  have hvt : ∀ t : Icc (0 : ℝ) T, v t = H.G t x +
      (2 : ℝ) • (∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece ub s) (extendPiece v s)) +
      ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece v s) (extendPiece v s) := by
    intro t
    conv_lhs => rw [hv]
    rw [ContinuousMap.add_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, hF, hB, hB]
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hv0 : extendPiece v 0 = x := by
    rw [extendPiece_eq hT0 v h0mem, hvt]
    simp [H.G_zero]
  refine ⟨hv0, ?_⟩
  rw [extendPiece_add]
  have cU : ContinuousOn (extendPiece ub) (Icc 0 T) := (continuous_extendPiece ub).continuousOn
  have cV : ContinuousOn (extendPiece v) (Icc 0 T) := (continuous_extendPiece v).continuousOn
  have bU : ∀ s ∈ Icc (0 : ℝ) T, ‖extendPiece ub s‖ ≤ ‖ub‖ :=
    fun s hs => norm_extendPiece_le hT0 ub hs
  have bV : ∀ s ∈ Icc (0 : ℝ) T, ‖extendPiece v s‖ ≤ ‖v‖ :=
    fun s hs => norm_extendPiece_le hT0 v hs
  have iUU := (h1 X H _ _ 0 T _ _ hT0 cU cU bU bU).1
  have iUV := (h1 X H _ _ 0 T _ _ hT0 cU cV bU bV).1
  have iVV := (h1 X H _ _ 0 T _ _ hT0 cV cV bV bV).1
  refine ⟨cU.add cV, fun t ht => ?_⟩
  have hsplit : (fun s => H.K (t - s) ((extendPiece ub + extendPiece v) s)
      ((extendPiece ub + extendPiece v) s)) = fun s =>
      H.K (t - s) (extendPiece ub s) (extendPiece ub s) +
        H.K (t - s) (extendPiece ub s) (extendPiece v s) +
        H.K (t - s) (extendPiece ub s) (extendPiece v s) +
        H.K (t - s) (extendPiece v s) (extendPiece v s) := by
    funext s
    simp only [Pi.add_apply, map_add, add_apply]
    rw [H.K_symm (t - s) (extendPiece v s) (extendPiece ub s)]
    abel
  have hint : IntervalIntegrable (fun s => H.K (t - s) ((extendPiece ub + extendPiece v) s)
      ((extendPiece ub + extendPiece v) s)) volume 0 t := by
    rw [hsplit]
    exact (((iUU t ht).add (iUV t ht)).add (iUV t ht)).add (iVV t ht)
  refine ⟨hint, ?_⟩
  rw [hsplit, intervalIntegral.integral_add (((iUU t ht).add (iUV t ht)).add (iUV t ht)) (iVV t ht),
    intervalIntegral.integral_add ((iUU t ht).add (iUV t ht)) (iUV t ht),
    intervalIntegral.integral_add (iUU t ht) (iUV t ht)]
  have hU := ((hub.2 t ht).2)
  have hV := hvt ⟨t, ht⟩
  rw [← extendPiece_eq hT0 v ht] at hV
  simp only [Pi.add_apply, sub_zero, map_add, hv0] at hU ⊢
  rw [hU, hV]
  simp only [two_smul]
  abel

end Breakdown
