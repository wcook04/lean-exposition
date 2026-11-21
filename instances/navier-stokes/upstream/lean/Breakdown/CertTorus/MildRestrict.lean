import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

open Freq

theorem mildRestrict_holds : MildRestrict := by
  intro u a a' b hu haa' ha'b
  obtain ⟨hc, hm⟩ := hu
  refine ⟨hc.mono (Icc_subset_Icc_left haa'), fun t ht => ?_⟩
  have hat : t ∈ Icc a b := ⟨haa'.trans ht.1, ht.2⟩
  obtain ⟨hit, het⟩ := hm t hat
  obtain ⟨hia', hea'⟩ := hm a' ⟨haa', ha'b⟩
  have hA : IntervalIntegrable (fun s => bilinX (t - s) (u s) (u s)) volume a a' :=
    hit.mono_set (by
      rw [uIcc_of_le haa', uIcc_of_le hat.1]
      exact Icc_subset_Icc_right ht.1)
  have hB : IntervalIntegrable (fun s => bilinX (t - s) (u s) (u s)) volume a' t :=
    hit.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hat.1]
      exact Icc_subset_Icc_left haa')
  refine ⟨hB, ?_⟩
  have hcongr : ∫ s in a..a', heatX (t - a') (bilinX (a' - s) (u s) (u s)) =
      ∫ s in a..a', bilinX (t - s) (u s) (u s) := by
    refine intervalIntegral.integral_congr_Ioo_of_le haa' fun s hs => ?_
    beta_reduce
    have h := bilinShift_holds (t - a') (a' - s) (sub_nonneg.2 ht.1) (sub_pos.2 hs.2) (u s) (u s)
    rw [sub_add_sub_cancel] at h
    exact h
  have hheat : heatX (t - a') (heatX (a' - a) (u a)) = heatX (t - a) (u a) := by
    have h := heat_holds.2.1 (t - a') (a' - a) (sub_nonneg.2 ht.1) (sub_nonneg.2 haa')
    rw [sub_add_sub_cancel] at h
    rw [h]
    rfl
  have hcomm : heatX (t - a') (∫ s in a..a', bilinX (a' - s) (u s) (u s)) =
      ∫ s in a..a', heatX (t - a') (bilinX (a' - s) (u s) (u s)) :=
    ((heatX (t - a')).intervalIntegral_comp_comm hia').symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have h3 : heatX (t - a') (u a') =
      heatX (t - a') (heatX (a' - a) (u a)) + ∫ s in a..a', bilinX (t - s) (u s) (u s) :=
    (congrArg (heatX (t - a')) hea').trans
      ((map_add (heatX (t - a')) _ _).trans (congrArg _ (hcomm.trans hcongr)))
  exact het.trans ((congrArg₂ (· + ·) hheat.symm hsplit.symm).trans ((add_assoc _ _ _).symm.trans
    (congrArg (fun z => z + ∫ s in a'..t, bilinX (t - s) (u s) (u s)) h3.symm)))

end Breakdown.FarField
