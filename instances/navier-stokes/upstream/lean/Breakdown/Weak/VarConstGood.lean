import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.MildOfWeak

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq Freq.Internal.MildOfWeak

theorem varConstGood_holds : VarConstGood := by
  intro hBI hDI y l r M E hM hy hE t₀ ht₀ t ht htt
  have h5 := heat_holds
  have h9 := bilinShift_holds
  have hl : l < t₀ := (hE.sub ht₀).1
  have hr : t < r := (hE.sub ht).2
  have hint : IntervalIntegrable (fun τ => bilinX (t - τ) (y τ) (y τ)) volume t₀ t := by
    have := hBI y l r M hM hy t₀ t 0 hl htt hr le_rfl
    simpa only [add_zero] using this
  obtain ⟨Z, hZ⟩ : ∃ Z : X, Z = y t - heatX (t - t₀) (y t₀) -
      ∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ) := ⟨_, rfl⟩
  have key : ∀ ε, 0 < ε → inner ℝ Z (heatX ε Z) = 0 := by
    intro ε hε
    have hd := hDI hBI y l r M E hM hy hE t₀ ht₀ t ht htt ε hε Z
    have e1 : inner ℝ (heatX (t - t₀) (y t₀)) (heatX ε Z) =
        inner ℝ (y t₀) (heatX (t - t₀ + ε) Z) := by
      refine (h5.2.2.2.2.1 _ _ _).trans ?_
      rw [h5.2.1 (t - t₀) ε (sub_nonneg.2 htt) hε.le, ContinuousLinearMap.comp_apply]
    have e2 : inner ℝ (∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)) (heatX ε Z) =
        ∫ τ in t₀..t, inner ℝ (bilinX (t - τ + ε) (y τ) (y τ)) Z := by
      refine (inner_intervalIntegral hint (heatX ε Z)).trans ?_
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton t)] with s hs hs'
      rw [uIoc_of_le htt] at hs'
      have hlt : s < t := lt_of_le_of_ne hs'.2 hs
      refine (h5.2.2.2.2.1 ε _ Z).symm.trans ?_
      have hb := h9 ε (t - s) hε.le (sub_pos.2 hlt) (y s) (y s)
      rw [add_comm ε (t - s)] at hb
      exact congrArg (fun q => inner ℝ q Z) hb
    have s0 : inner ℝ Z (heatX ε Z) = inner ℝ (y t - heatX (t - t₀) (y t₀) -
        ∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)) (heatX ε Z) :=
      congrArg (fun q => inner ℝ q (heatX ε Z)) hZ
    have s1 := inner_sub_left (𝕜 := ℝ) (y t - heatX (t - t₀) (y t₀))
      (∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)) (heatX ε Z)
    have s2 := inner_sub_left (𝕜 := ℝ) (y t) (heatX (t - t₀) (y t₀)) (heatX ε Z)
    linarith [s0, s1, s2, e1, e2, hd]
  have hZ0 : Z = 0 := by
    have hc : ContinuousWithinAt (fun ε => heatX ε Z) (Ici 0) 0 :=
      h5.2.2.2.1 Z 0 (mem_Ici.2 (le_refl (0 : ℝ)))
    have hlim : Filter.Tendsto (fun ε => inner ℝ Z (heatX ε Z)) (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ Z (heatX 0 Z))) :=
      Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (hc.mono Ioi_subset_Ici_self).tendsto
    rw [h5.1, ContinuousLinearMap.id_apply] at hlim
    have h0 : Filter.Tendsto (fun ε => inner ℝ Z (heatX ε Z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)
    exact inner_self_eq_zero.1 (tendsto_nhds_unique hlim h0)
  rw [hZ, sub_sub, sub_eq_zero] at hZ0
  exact hZ0.symm

end Breakdown.WeakProfile
