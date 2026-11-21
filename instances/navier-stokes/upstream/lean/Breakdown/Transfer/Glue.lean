import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace GlueInternal

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem index_spec {μ t : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    μ ^ (MildFramework.stepIndex μ t + 1) < 1 - t ∧ 1 - t ≤ μ ^ MildFramework.stepIndex μ t := by
  have hl : Real.log μ < 0 := Real.log_neg hμ0 hμ1
  have hpos : 0 < 1 - t := by linarith
  have hl1 : Real.log (1 - t) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  have hq : 0 ≤ Real.log (1 - t) / Real.log μ := div_nonneg_of_nonpos hl1 hl.le
  have h1 : ((MildFramework.stepIndex μ t : ℕ) : ℝ) ≤ Real.log (1 - t) / Real.log μ :=
    Nat.floor_le hq
  have h2 : Real.log (1 - t) / Real.log μ < (MildFramework.stepIndex μ t : ℕ) + 1 :=
    Nat.lt_floor_add_one _
  rw [le_div_iff_of_neg hl] at h1
  rw [div_lt_iff_of_neg hl] at h2
  constructor
  · rw [← Real.log_lt_log_iff (pow_pos hμ0 _) hpos, Real.log_pow]
    push_cast
    exact h2
  · rw [← Real.log_le_log_iff hpos (pow_pos hμ0 _), Real.log_pow]
    exact h1

theorem index_eq {μ t : ℝ} {n : ℕ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (h1 : μ ^ (n + 1) < 1 - t) (h2 : 1 - t ≤ μ ^ n) : MildFramework.stepIndex μ t = n := by
  have hl : Real.log μ < 0 := Real.log_neg hμ0 hμ1
  have hpos : 0 < 1 - t := lt_trans (pow_pos hμ0 _) h1
  have hle : 1 - t ≤ 1 := h2.trans (pow_le_one₀ hμ0.le hμ1.le)
  have hl1 : Real.log (1 - t) ≤ 0 := Real.log_nonpos hpos.le hle
  have hq : 0 ≤ Real.log (1 - t) / Real.log μ := div_nonneg_of_nonpos hl1 hl.le
  unfold MildFramework.stepIndex
  rw [Nat.floor_eq_iff hq, le_div_iff_of_neg hl, div_lt_iff_of_neg hl]
  rw [← Real.log_lt_log_iff (pow_pos hμ0 _) hpos, Real.log_pow] at h1
  rw [← Real.log_le_log_iff hpos (pow_pos hμ0 _), Real.log_pow] at h2
  push_cast at h1
  exact ⟨h2, h1⟩

def scaledPiece (F : MildFramework X) (μ : ℝ) (u : ℕ → Piece X (1 - μ)) (n : ℕ) (t : ℝ) : X :=
  F.D (μ ^ n)⁻¹ (extendPiece (u n) ((μ ^ n)⁻¹ * (t - (1 - μ ^ n))))

theorem extendPiece_continuous {T : ℝ} (f : Piece X T) : Continuous (extendPiece f) := by
  by_cases h : 0 ≤ T
  · have e : extendPiece f = IccExtend h f := funext fun t => by simp only [extendPiece, dif_pos h]
    rw [e]
    exact f.continuous.Icc_extend'
  · have e : extendPiece f = fun _ => (0 : X) := funext fun t => by simp only [extendPiece, dif_neg h]
    rw [e]
    exact continuous_const

theorem scaledPiece_continuous (F : MildFramework X) (μ : ℝ) (u : ℕ → Piece X (1 - μ)) (n : ℕ) :
    Continuous (scaledPiece F μ u n) :=
  (F.D (μ ^ n)⁻¹).continuous.comp
    ((extendPiece_continuous (u n)).comp (continuous_const.mul (continuous_id.sub continuous_const)))

theorem glue_eq (F : MildFramework X) {μ : ℝ} (u : ℕ → Piece X (1 - μ)) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hmatch : ∀ n, extendPiece (u (n + 1)) 0 = F.D μ (extendPiece (u n) (1 - μ)))
    (n : ℕ) :
    EqOn (F.gluePieces μ u) (scaledPiece F μ u n) (Icc (1 - μ ^ n) (1 - μ ^ (n + 1))) := by
  intro t ht
  have hpn : 0 < μ ^ n := pow_pos hμ0 n
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    have hidx : MildFramework.stepIndex μ (1 - μ ^ (n + 1)) = n + 1 := by
      refine index_eq hμ0 hμ1 ?_ ?_
      · rw [sub_sub_cancel, pow_succ μ (n + 1)]
        exact mul_lt_of_lt_one_right (pow_pos hμ0 _) hμ1
      · rw [sub_sub_cancel]
    simp only [MildFramework.gluePieces]
    rw [hidx, sub_self, zero_div, hmatch n, ← ContinuousLinearMap.comp_apply,
      ← F.D_mul _ _ (inv_pos.2 (pow_pos hμ0 _)) hμ0]
    have e1 : (μ ^ (n + 1))⁻¹ * μ = (μ ^ n)⁻¹ := by
      rw [pow_succ]
      field_simp
    have e2 : (μ ^ n)⁻¹ * (1 - μ ^ (n + 1) - (1 - μ ^ n)) = 1 - μ := by
      rw [pow_succ]
      field_simp
      ring
    simp only [scaledPiece]
    rw [e1, e2]
  · have hidx : MildFramework.stepIndex μ t = n := index_eq hμ0 hμ1 (by linarith) (by linarith [ht.1])
    simp only [MildFramework.gluePieces, scaledPiece, hidx, div_eq_inv_mul]

theorem varConst_congr (H : HeatBilinear X) {u v : ℝ → X} {a t : ℝ} (hat : a ≤ t)
    (h : EqOn u v (Icc a t)) (hu : H.VarConst u a t) : H.VarConst v a t := by
  have hint : EqOn (fun s => H.K (t - s) (u s) (u s)) (fun s => H.K (t - s) (v s) (v s))
      (Icc a t) := fun s hs => by
    show H.K (t - s) (u s) (u s) = H.K (t - s) (v s) (v s)
    rw [h hs]
  refine ⟨?_, ?_⟩
  · have hi := hu.1
    rw [intervalIntegrable_iff, uIoc_of_le hat] at hi ⊢
    exact hi.congr_fun (hint.mono Ioc_subset_Icc_self) measurableSet_Ioc
  · rw [← h ⟨hat, le_rfl⟩, ← h ⟨le_rfl, hat⟩, hu.2]
    congr 1
    exact intervalIntegral.integral_congr (by rw [uIcc_of_le hat]; exact hint)

theorem piece_varConst (F : MildFramework X) (h1 : ScaleStatement) (h4 : ShiftStatement) {μ : ℝ}
    (u : ℕ → Piece X (1 - μ)) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hm : ∀ n, F.IsMildOnIcc (extendPiece (u n)) 0 (1 - μ)) (n : ℕ) (t : ℝ)
    (ht : t ∈ Icc (1 - μ ^ n) (1 - μ ^ (n + 1))) :
    F.toHeatBilinear.VarConst (scaledPiece F μ u n) (1 - μ ^ n) t := by
  have hpn : 0 < μ ^ n := pow_pos hμ0 n
  have hsc := h1 X F (extendPiece (u n)) (μ ^ n)⁻¹ (μ ^ n * (1 - μ)) (inv_pos.2 hpn)
    (mul_nonneg hpn.le (by linarith))
    (by rw [← mul_assoc, inv_mul_cancel₀ hpn.ne', one_mul]; exact hm n)
  rw [h4 X F.toHeatBilinear (scaledPiece F μ u n) (1 - μ ^ n) t (1 - μ ^ n), sub_self]
  have hfun : (fun s => scaledPiece F μ u n (s + (1 - μ ^ n))) =
      fun s => F.D (μ ^ n)⁻¹ (extendPiece (u n) ((μ ^ n)⁻¹ * s)) := by
    funext s
    simp only [scaledPiece, add_sub_cancel_right]
  rw [hfun]
  have h2 := ht.2
  rw [pow_succ] at h2
  have e : μ ^ n * (1 - μ) = μ ^ n - μ ^ n * μ := by ring
  exact hsc.2 (t - (1 - μ ^ n)) ⟨by linarith [ht.1], by linarith⟩

theorem glue_upto (F : MildFramework X) (h1 : ScaleStatement) (h2 : ConcatStatement)
    (h4 : ShiftStatement) {μ : ℝ} (u : ℕ → Piece X (1 - μ)) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hm : ∀ n, F.IsMildOnIcc (extendPiece (u n)) 0 (1 - μ))
    (hmatch : ∀ n, extendPiece (u (n + 1)) 0 = F.D μ (extendPiece (u n) (1 - μ))) (n : ℕ) :
    ContinuousOn (F.gluePieces μ u) (Icc 0 (1 - μ ^ n)) ∧
      ∀ t ∈ Icc 0 (1 - μ ^ n), F.toHeatBilinear.VarConst (F.gluePieces μ u) 0 t := by
  induction n with
  | zero =>
    simp only [pow_zero, sub_self, Icc_self]
    refine ⟨continuousOn_singleton _ _, ?_⟩
    rintro t rfl
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [sub_self, intervalIntegral.integral_same, F.toHeatBilinear.G_zero, add_zero]
    rfl
  | succ n ih =>
    obtain ⟨hc, hd⟩ := ih
    have hpn : 0 < μ ^ n := pow_pos hμ0 n
    have hmono : 1 - μ ^ n ≤ 1 - μ ^ (n + 1) := by
      rw [pow_succ]
      have := mul_lt_of_lt_one_right hpn hμ1
      linarith
    have h0 : (0 : ℝ) ≤ 1 - μ ^ n := by linarith [pow_le_one₀ (n := n) hμ0.le hμ1.le]
    have hEq := glue_eq F u hμ0 hμ1 hmatch n
    have hcn : ContinuousOn (F.gluePieces μ u) (Icc (1 - μ ^ n) (1 - μ ^ (n + 1))) :=
      (scaledPiece_continuous F μ u n).continuousOn.congr hEq
    have hc' : ContinuousOn (F.gluePieces μ u) (Icc 0 (1 - μ ^ (n + 1))) := by
      rw [← Icc_union_Icc_eq_Icc h0 hmono]
      exact hc.union_of_isClosed hcn isClosed_Icc isClosed_Icc
    refine ⟨hc', fun t ht => ?_⟩
    by_cases htn : t ≤ 1 - μ ^ n
    · exact hd t ⟨ht.1, htn⟩
    · replace htn := not_le.mp htn
      have htI : t ∈ Icc (1 - μ ^ n) (1 - μ ^ (n + 1)) := ⟨htn.le, ht.2⟩
      have hp := piece_varConst F h1 h4 u hμ0 hμ1 hm n t htI
      have hg := varConst_congr F.toHeatBilinear htn.le
        (fun s hs => (hEq ⟨hs.1, hs.2.trans ht.2⟩).symm) hp
      exact h2 X F.toHeatBilinear _ 0 (1 - μ ^ n) t h0 htn.le
        (hc'.mono (Icc_subset_Icc le_rfl ht.2)) (hd _ ⟨h0, le_rfl⟩) hg

end GlueInternal

theorem glue_of (h1 : ScaleStatement) (h2 : ConcatStatement) (h4 : ShiftStatement) :
    GlueStatement := by
  intro X _ _ _ F μ u hμ0 hμ1 hm hmatch
  have cover : ∀ t ∈ Ico (0 : ℝ) 1, t < 1 - μ ^ (MildFramework.stepIndex μ t + 1) := by
    intro t ht
    linarith [(GlueInternal.index_spec hμ0 hμ1 ht.1 ht.2).1]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro t ht
    have hlt := cover t ht
    have hc := (GlueInternal.glue_upto F h1 h2 h4 u hμ0 hμ1 hm hmatch
      (MildFramework.stepIndex μ t + 1)).1
    refine (hc t ⟨ht.1, hlt.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio _, isOpen_Iio, hlt, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩
  · intro t ht
    exact (GlueInternal.glue_upto F h1 h2 h4 u hμ0 hμ1 hm hmatch
      (MildFramework.stepIndex μ t + 1)).2 t ⟨ht.1, (cover t ht).le⟩
  · intro t ht
    obtain ⟨hs1, hs2⟩ := GlueInternal.index_spec hμ0 hμ1 ht.1 ht.2
    have hpn : 0 < μ ^ MildFramework.stepIndex μ t := pow_pos hμ0 _
    refine ⟨MildFramework.stepIndex μ t,
      (t - (1 - μ ^ MildFramework.stepIndex μ t)) / μ ^ MildFramework.stepIndex μ t,
      ⟨div_nonneg (by linarith) hpn.le, ?_⟩, ?_, ?_⟩
    · rw [div_lt_iff₀ hpn]
      rw [pow_succ] at hs1
      have e : (1 - μ) * μ ^ MildFramework.stepIndex μ t =
          μ ^ MildFramework.stepIndex μ t - μ ^ MildFramework.stepIndex μ t * μ := by ring
      linarith
    · field_simp
      ring
    · simp only [MildFramework.gluePieces]
      rw [← ContinuousLinearMap.comp_apply, ← F.D_mul _ _ (by linarith [ht.2]) (inv_pos.2 hpn)]
      congr 3
      field_simp
      ring
