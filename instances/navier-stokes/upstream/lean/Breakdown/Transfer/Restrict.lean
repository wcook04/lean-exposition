import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private lemma varConst_free_step (H : HeatBilinear X) (u : ℝ → X) {a m t : ℝ} (ham : a ≤ m) (hmt : m ≤ t)
    (hm : H.VarConst u a m) :
    IntervalIntegrable (fun s => H.K (t - s) (u s) (u s)) volume a m ∧
      H.G (t - m) (u m) = H.G (t - a) (u a) + ∫ s in a..m, H.K (t - s) (u s) (u s) := by
  obtain ⟨hi, he⟩ := hm
  have heq : EqOn (fun s => H.G (t - m) (H.K (m - s) (u s) (u s)))
      (fun s => H.K (t - s) (u s) (u s)) (Ioo a m) := by
    intro s hs
    simp only
    rw [H.K_shift _ _ (sub_nonneg.2 hmt) (sub_pos.2 hs.2), sub_add_sub_cancel]
  have hG : IntervalIntegrable (fun s => H.G (t - m) (H.K (m - s) (u s) (u s))) volume a m :=
    ⟨(H.G (t - m)).integrable_comp hi.1, (H.G (t - m)).integrable_comp hi.2⟩
  refine ⟨hG.congr_uIoo (by rw [uIoo_of_le ham]; exact heq), ?_⟩
  rw [he, map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hi,
    intervalIntegral.integral_congr_Ioo_of_le ham heq, ← ContinuousLinearMap.comp_apply,
    ← H.G_add _ _ (sub_nonneg.2 hmt) (sub_nonneg.2 ham), sub_add_sub_cancel]

theorem restrict : RestrictStatement := by
  intro X _ _ _ H u a m t ham hmt _ hm hat
  have hB : IntervalIntegrable (fun s => H.K (t - s) (u s) (u s)) volume m t :=
    hat.1.mono_set (by
      rw [uIcc_of_le hmt, uIcc_of_le (ham.trans hmt)]
      exact Icc_subset_Icc_left ham)
  obtain ⟨hA, hfs⟩ := varConst_free_step H u ham hmt hm
  refine ⟨hB, ?_⟩
  rw [hat.2, hfs, add_assoc, intervalIntegral.integral_add_adjacent_intervals hA hB]

theorem restrict_of (_h1 : VarConstIntegralStatement) : RestrictStatement := restrict

theorem concat : ConcatStatement := by
  intro X _ _ _ H u a m t ham hmt _ hm hmt'
  obtain ⟨hA, hfs⟩ := varConst_free_step H u ham hmt hm
  refine ⟨hA.trans hmt'.1, ?_⟩
  rw [hmt'.2, hfs, add_assoc, intervalIntegral.integral_add_adjacent_intervals hA hmt'.1]

theorem concat_of (_h1 : VarConstIntegralStatement) : ConcatStatement := concat

theorem shift : ShiftStatement := by
  intro X _ _ _ H u a t c
  have hf : (fun s => H.K (t - c - s) (u (s + c)) (u (s + c))) =
      fun s => (fun r => H.K (t - r) (u r) (u r)) (s + c) := by
    funext s
    rw [sub_sub, add_comm c s]
  unfold HeatBilinear.VarConst
  rw [hf, intervalIntegral.integral_comp_add_right (fun r => H.K (t - r) (u r) (u r)) c]
  simp only [sub_add_cancel, sub_sub_sub_cancel_right]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
  · simpa using h.comp_add_right c
  · simpa using h.comp_add_right (-c)

end Breakdown
