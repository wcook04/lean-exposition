import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology InnerProductSpace
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma integral_norm_inner_le_mul (ψ φ : L2C) :
    ∫ ξ, ‖inner ℂ (ψ ξ) (φ ξ)‖ ≤ ‖ψ‖ * ‖φ‖ := by
  have hψ : AEStronglyMeasurable (ψ : Space → CSpace) volume := Lp.aestronglyMeasurable ψ
  have hφ : AEStronglyMeasurable (φ : Space → CSpace) volume := Lp.aestronglyMeasurable φ
  have hH : eLpNorm (fun ξ => inner ℂ (ψ ξ) (φ ξ)) 1 volume ≤
      1 * eLpNorm ψ 2 volume * eLpNorm φ 2 volume :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hψ hφ (fun a b => inner ℂ a b) 1
      (Eventually.of_forall fun ξ => by
        simpa [one_mul] using nnnorm_inner_le_nnnorm (𝕜 := ℂ) (ψ ξ) (φ ξ))
  rw [one_mul] at hH
  have hm : AEStronglyMeasurable (fun ξ => inner ℂ (ψ ξ) (φ ξ)) volume := hψ.inner hφ
  rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def,
    Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top ψ) (Lp.eLpNorm_ne_top φ)) hH

theorem coe_intervalIntegral_ae {t : ℝ} (ht : 0 ≤ t) {G : ℝ → X} {g : ℝ → Space → CSpace}
    (hG : ∀ s ∈ Ioo 0 t, ((G s : X) : Space → CSpace) =ᵐ[volume] g s)
    (hGi : IntervalIntegrable G volume 0 t)
    (hg : AEStronglyMeasurable (Function.uncurry g) ((volume.restrict (Ioc 0 t)).prod volume))
    (hgi : ∀ ξ, IntervalIntegrable (fun s => g s ξ) volume 0 t)
    (hk : MemLp (fun ξ => ∫ s in (0 : ℝ)..t, g s ξ) 2 volume) :
    ((∫ s in (0 : ℝ)..t, G s : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ∫ s in (0 : ℝ)..t, g s ξ := by
  set k : L2C := hk.toLp _ with hkdef
  have hkae : (k : Space → CSpace) =ᵐ[volume] fun ξ => ∫ s in (0 : ℝ)..t, g s ξ := hk.coeFn_toLp
  refine Filter.EventuallyEq.trans ?_ hkae
  have hcoe : ((∫ s in (0 : ℝ)..t, G s : X) : L2C) = ∫ s in (0 : ℝ)..t, (G s : L2C) :=
    ((Sig.subtypeL).intervalIntegral_comp_comm hGi).symm
  suffices h : ((∫ s in (0 : ℝ)..t, G s : X) : L2C) = k by rw [h]
  rw [hcoe, intervalIntegral.integral_of_le ht]
  have hHi : Integrable (fun s => (G s : L2C)) (volume.restrict (Ioc 0 t)) :=
    (Sig.subtypeL).integrable_comp hGi.1
  have hres : volume.restrict (Ioc (0 : ℝ) t) = volume.restrict (Ioo 0 t) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hae : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)), s ∈ Ioo 0 t := by
    rw [hres]; exact ae_restrict_mem measurableSet_Ioo
  refine ext_inner_left ℂ (fun ψ => ?_)
  rw [← integral_inner hHi ψ, L2.inner_def ψ k]
  have hL : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)),
      inner ℂ ψ (G s : L2C) = ∫ ξ, inner ℂ (ψ ξ) (g s ξ) := by
    filter_upwards [hae] with s hs
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hG s hs] with ξ hξ
    rw [hξ]
  rw [integral_congr_ae hL]
  have hR : ∫ ξ, inner ℂ (ψ ξ) (k ξ) = ∫ ξ, ∫ s in Ioc 0 t, inner ℂ (ψ ξ) (g s ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [hkae] with ξ hξ
    rw [hξ, intervalIntegral.integral_of_le ht, integral_inner (hgi ξ).1]
  rw [hR]
  have hF : AEStronglyMeasurable (Function.uncurry fun s ξ => inner ℂ (ψ ξ) (g s ξ))
      ((volume.restrict (Ioc 0 t)).prod volume) :=
    (Lp.aestronglyMeasurable ψ).comp_snd.inner hg
  refine integral_integral_swap ((integrable_prod_iff hF).2 ⟨?_, ?_⟩)
  · filter_upwards [hae] with s hs
    refine (L2.integrable_inner ψ (G s : L2C)).congr ?_
    filter_upwards [hG s hs] with ξ hξ
    simp only [Function.uncurry_apply_pair]
    rw [hξ]
  · refine Integrable.mono' (hHi.norm.const_mul ‖ψ‖) hF.norm.integral_prod_right' ?_
    filter_upwards [hae] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ ξ, ‖Function.uncurry (fun s ξ => inner ℂ (ψ ξ) (g s ξ)) (s, ξ)‖
        = ∫ ξ, ‖inner ℂ (ψ ξ) ((G s : L2C) ξ)‖ := by
          refine integral_congr_ae ?_
          filter_upwards [hG s hs] with ξ hξ
          simp only [Function.uncurry_apply_pair]
          rw [hξ]
      _ ≤ ‖ψ‖ * ‖(G s : L2C)‖ := integral_norm_inner_le_mul ψ (G s : L2C)

end Breakdown.SmoothFlow
