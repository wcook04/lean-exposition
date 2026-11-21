import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.MildOfWeak

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq Freq.Internal.MildOfWeak

theorem mildFromGood_holds : MildFromGood := by
  intro hBI y l r M t₀ E hM hy hsub hnull ht₀ hc hgood a b hta0 hab hbr
  have h5 := heat_holds
  have h9 := bilinShift_holds
  have hIcc : Icc a b ⊆ Ico t₀ r := fun s hs => ⟨hta0.trans hs.1, hs.2.trans_lt hbr⟩
  have hcab : ContinuousOn (varConst y t₀) (Icc a b) := hc.mono hIcc
  refine ⟨hcab, fun t ht => ⟨bilin_intervalIntegrable bilin_holds.2 bilinCont_holds hcab ht, ?_⟩⟩
  have htr : t < r := ht.2.trans_lt hbr
  have hIt : IntervalIntegrable (fun τ => bilinX (t - τ) (y τ) (y τ)) volume t₀ t := by
    have := hBI y l r M hM hy t₀ t 0 ht₀.1 (hta0.trans ht.1) htr le_rfl
    simpa only [add_zero] using this
  have hmem : a ∈ uIcc t₀ t := mem_uIcc_of_le hta0 ht.1
  have hIa : IntervalIntegrable (fun τ => bilinX (t - τ) (y τ) (y τ)) volume t₀ a :=
    hIt.mono_set (uIcc_subset_uIcc left_mem_uIcc hmem)
  have hIat : IntervalIntegrable (fun τ => bilinX (t - τ) (y τ) (y τ)) volume a t :=
    hIt.mono_set (uIcc_subset_uIcc hmem right_mem_uIcc)
  have Ga : IntervalIntegrable (fun τ => bilinX (a - τ) (y τ) (y τ)) volume t₀ a := by
    have := hBI y l r M hM hy t₀ a 0 ht₀.1 hta0 (hab.trans hbr) le_rfl
    simpa only [add_zero] using this
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hIa hIat
  have e1 : heatX (t - a) (heatX (a - t₀) (y t₀)) = heatX (t - t₀) (y t₀) := by
    rw [← ContinuousLinearMap.comp_apply, ← h5.2.1 _ _ (sub_nonneg.2 ht.1) (sub_nonneg.2 hta0),
      show t - a + (a - t₀) = t - t₀ by ring]
  have e2 : heatX (t - a) (∫ τ in t₀..a, bilinX (a - τ) (y τ) (y τ)) =
      ∫ τ in t₀..a, bilinX (t - τ) (y τ) (y τ) := by
    refine (ContinuousLinearMap.intervalIntegral_comp_comm (heatX (t - a)) Ga).symm.trans ?_
    apply intervalIntegral.integral_congr_ae
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton a)] with s hs hs'
    rw [uIoc_of_le hta0] at hs'
    have hlt : s < a := lt_of_le_of_ne hs'.2 hs
    have hb := h9 (t - a) (a - s) (sub_nonneg.2 ht.1) (sub_pos.2 hlt) (y s) (y s)
    have hq : t - a + (a - s) = t - s := by ring
    refine hb.trans ?_
    exact congrArg (fun q => bilinX q (y s) (y s)) hq
  have hae : ∀ᵐ τ ∂volume, τ ∈ Ioo l r → τ ∈ E := by
    refine ae_iff.2 (measure_mono_null ?_ hnull)
    intro τ hτ
    exact Classical.not_imp.1 hτ
  have e3 : ∫ τ in a..t, bilinX (t - τ) (y τ) (y τ) =
      ∫ τ in a..t, bilinX (t - τ) (varConst y t₀ τ) (varConst y t₀ τ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with s hs hs'
    rw [uIoc_of_le ht.1] at hs'
    have hsE : s ∈ E := hs ⟨ht₀.1.trans_le (hta0.trans_lt hs'.1).le, hs'.2.trans_lt htr⟩
    exact congrArg (fun q => bilinX (t - s) q q) (hgood s hsE (hta0.trans hs'.1.le)).symm
  have hheat : heatX (t - a) (varConst y t₀ a) =
      heatX (t - t₀) (y t₀) + ∫ τ in t₀..a, bilinX (t - τ) (y τ) (y τ) :=
    (map_add (heatX (t - a)) (heatX (a - t₀) (y t₀))
      (∫ τ in t₀..a, bilinX (a - τ) (y τ) (y τ))).trans (congrArg₂ (· + ·) e1 e2)
  calc varConst y t₀ t = heatX (t - t₀) (y t₀) + ((∫ τ in t₀..a, bilinX (t - τ) (y τ) (y τ)) +
        ∫ τ in a..t, bilinX (t - τ) (y τ) (y τ)) :=
        congrArg (fun q => heatX (t - t₀) (y t₀) + q) hsplit.symm
    _ = (heatX (t - t₀) (y t₀) + ∫ τ in t₀..a, bilinX (t - τ) (y τ) (y τ)) +
        ∫ τ in a..t, bilinX (t - τ) (y τ) (y τ) := (add_assoc _ _ _).symm
    _ = heatX (t - a) (varConst y t₀ a) +
        ∫ s in a..t, bilinX (t - s) (varConst y t₀ s) (varConst y t₀ s) :=
        congrArg₂ (· + ·) hheat.symm e3

end Breakdown.WeakProfile
