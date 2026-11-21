import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace SmallData.Internal

theorem bil_sub {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (v w : Y) :
    B v v - B w w = B (v - w) v + B w (v - w) := by
  simp only [map_sub, sub_apply]
  abel

theorem bil_norm_sub {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (v w : Y) {r : ℝ} (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖B v v - B w w‖ ≤ 2 * ‖B‖ * r * ‖v - w‖ := by
  rw [bil_sub]
  have h1 := B.le_opNorm₂ (v - w) v
  have h2 := B.le_opNorm₂ w (v - w)
  have hB := norm_nonneg B
  have hd := norm_nonneg (v - w)
  calc ‖B (v - w) v + B w (v - w)‖ ≤ ‖B (v - w) v‖ + ‖B w (v - w)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖v - w‖ * ‖v‖ + ‖B‖ * ‖w‖ * ‖v - w‖ := add_le_add h1 h2
    _ ≤ ‖B‖ * ‖v - w‖ * r + ‖B‖ * r * ‖v - w‖ := by gcongr
    _ = 2 * ‖B‖ * r * ‖v - w‖ := by ring

theorem fixed_point {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (y : Y) (hy : 8 * ‖B‖ * ‖y‖ ≤ 1) :
    ∃ v : Y, ‖v‖ ≤ 2 * ‖y‖ ∧ v = y + B v v := by
  have hB := norm_nonneg B
  have hy0 := norm_nonneg y
  have maps : ∀ v : Y, ‖v‖ ≤ 2 * ‖y‖ → ‖y + B v v‖ ≤ 2 * ‖y‖ := by
    intro v hv
    have h1 : ‖B v v‖ ≤ ‖B‖ * (2 * ‖y‖) * (2 * ‖y‖) :=
      (B.le_opNorm₂ v v).trans (by gcongr)
    have h2 := mul_le_mul_of_nonneg_right hy hy0
    calc ‖y + B v v‖ ≤ ‖y‖ + ‖B v v‖ := norm_add_le _ _
      _ ≤ 2 * ‖y‖ := by nlinarith
  let S := Metric.closedBall (0 : Y) (2 * ‖y‖)
  have memS : ∀ v : Y, v ∈ S ↔ ‖v‖ ≤ 2 * ‖y‖ := fun v => mem_closedBall_zero_iff
  let f : S → S := fun v => ⟨y + B v v, (memS _).2 (maps v ((memS _).1 v.2))⟩
  have hf : ContractingWith 2⁻¹ f := by
    refine ⟨two_inv_lt_one, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha := (memS _).1 a.2
    have hb := (memS _).1 b.2
    have key := bil_norm_sub B a b ha hb
    have hab : dist a b = ‖(a : Y) - b‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    have hfab : dist (f a) (f b) = ‖B a a - B b b‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      simp only [f, add_sub_add_left_eq_sub]
    rw [hfab, hab]
    have hd := norm_nonneg ((a : Y) - b)
    have h3 := mul_le_mul_of_nonneg_right hy hd
    push_cast
    nlinarith
  have : Nonempty S := ⟨⟨0, (memS _).2 (by simp)⟩⟩
  have : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  let vfix : S := ContractingWith.fixedPoint (α := S) f hf
  have hfix : f vfix = vfix := hf.fixedPoint_isFixedPt
  exact ⟨vfix, (memS _).1 vfix.2, (congrArg Subtype.val hfix).symm⟩

end SmallData.Internal

theorem smallData_of (h1 : VarConstIntegralStatement) (h2 : PieceOperatorStatement) :
    SmallDataStatement := by
  intro X _ _ _ H
  obtain ⟨hB, -, hΓ, hΓn⟩ := h2 X H 1 one_pos
  set B := H.pieceBil 1 with hBdef
  set Γ := H.pieceFree 1 with hΓdef
  have hBn := norm_nonneg B
  refine ⟨1 / (8 * (‖B‖ + 1)), by positivity, ?_⟩
  intro x hx
  have hx' : ‖x‖ * (8 * (‖B‖ + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hx
  have hx0 := norm_nonneg x
  have hy : ‖Γ x‖ ≤ ‖x‖ := (Γ.le_opNorm x).trans (by nlinarith)
  have h8 : 8 * ‖B‖ * ‖Γ x‖ ≤ 1 := by nlinarith [norm_nonneg (Γ x)]
  obtain ⟨v, hv, hfix⟩ := SmallData.Internal.fixed_point B (Γ x) h8
  have hpt : ∀ t : Icc (0 : ℝ) 1, v t = H.G t x +
      ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece v s) (extendPiece v s) := by
    intro t
    have := DFunLike.congr_fun hfix t
    rw [ContinuousMap.add_apply, hΓ, hB] at this
    exact this
  have hu : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), extendPiece v t = v ⟨t, ht⟩ := by
    intro t ht
    rw [extendPiece, dif_pos zero_le_one, Set.IccExtend_of_mem]
  have hcont : ContinuousOn (extendPiece v) (Icc (0 : ℝ) 1) := by
    have he : extendPiece v = Set.IccExtend (zero_le_one' ℝ) v := by
      funext t
      exact dif_pos _
    have : Continuous (extendPiece v) := by
      rw [he]
      exact continuous_IccExtend_iff.2 v.continuous
    exact this.continuousOn
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖extendPiece v s‖ ≤ ‖v‖ := by
    intro s hs
    rw [hu s hs]
    exact v.norm_coe_le_norm _
  have hint := (h1 X H (extendPiece v) (extendPiece v) 0 1 ‖v‖ ‖v‖ zero_le_one hcont hcont
    hbd hbd).1
  have hu0 : extendPiece v 0 = x := by
    rw [hu 0 ⟨le_rfl, zero_le_one⟩, hpt]
    simp [H.G_zero]
  refine ⟨extendPiece v, hu0, ⟨hcont, fun t ht => ⟨hint t ht, ?_⟩⟩, ?_⟩
  · rw [hu t ht, hpt ⟨t, ht⟩, hu0, sub_zero]
  · intro t ht
    calc ‖extendPiece v t‖ ≤ ‖v‖ := hbd t ht
      _ ≤ 2 * ‖Γ x‖ := hv
      _ ≤ 2 * ‖x‖ := by linarith

end Breakdown
