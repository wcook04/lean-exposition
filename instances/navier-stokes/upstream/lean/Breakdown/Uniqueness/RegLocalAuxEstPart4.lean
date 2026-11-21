import Breakdown.Uniqueness.RegLocalAuxSymm
import Breakdown.Uniqueness.RegCurveAuxPointwise

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hsNormSq_mono_index {k m : ℕ} (hkm : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  unfold hsWeight
  exact pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖ξ‖]) hkm

private theorem isHsCurve_shift {m : ℕ} (hm : 1 ≤ m) {G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve m G a b) : IsHsCurve 1 (fun s => G (s + a)) 0 (b - a) := by
  obtain ⟨h1, h2⟩ := hG
  have hmap : MapsTo (fun s : ℝ => s + a) (Icc 0 (b - a)) (Icc a b) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
  · obtain ⟨hm1, hs1⟩ := h1 (t + a) (hmap ht)
    exact ⟨hm1, lt_of_le_of_lt (hsNormSq_mono_index hm _) hs1⟩
  · have hc : Tendsto (fun s : ℝ => s + a) (𝓝[Icc 0 (b - a)] t₀) (𝓝[Icc a b] (t₀ + a)) :=
      ((continuous_add_const a).continuousWithinAt).tendsto_nhdsWithin hmap
    have hlim := (h2 (t₀ + a) (hmap ht₀)).comp hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun s => ?_
    exact hsNormSq_mono_index hm _

private theorem continuous_divFreeC_apply (ξ : Space) : Continuous (fun z : CSpace => divFreeC ξ z) := by
  unfold divFreeC
  fun_prop

theorem continuousOn_nonlinSymbol_curve {m : ℕ} (hm : 1 ≤ m) {G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve m G a b) (ξ : Space) :
    ContinuousOn (fun s => nonlinSymbol (G s) ξ) (Icc a b) := by
  have hA := continuousOn_advectionSymbol_apply (isHsCurve_shift hm hG) ξ
  have hmap : MapsTo (fun s : ℝ => s - a) (Icc a b) (Icc 0 (b - a)) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hB : ContinuousOn (fun s => advectionSymbol (G s) ξ) (Icc a b) := by
    have := hA.comp (continuous_id.sub continuous_const).continuousOn hmap
    refine this.congr fun s _ => ?_
    simp
  exact ((continuous_divFreeC_apply ξ).comp_continuousOn hB).neg

end Breakdown.SmoothFlow
