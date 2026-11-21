import Breakdown.Uniqueness.RegLocalAuxCurvePart1
import Breakdown.Uniqueness.RegLocalAuxCurvePart2

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem isHsCurve_add {m : ℕ} {F F' : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve m F a b) (hF' : IsHsCurve m F' a b) :
    IsHsCurve m (fun t => F t + F' t) a b := by
  obtain ⟨h1, h2⟩ := hF
  obtain ⟨h1', h2'⟩ := hF'
  refine ⟨fun t ht => ⟨(h1 t ht).1.add (h1' t ht).1, ?_⟩, fun t₀ ht₀ => ?_⟩
  · refine lt_of_le_of_lt (hsNormSq_add_le_two_mul m (h1 t ht).1) ?_
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2 ⟨(h1 t ht).2, (h1' t ht).2⟩)
  · have hlim : Tendsto (fun t => 2 * (hsNormSq m (F t - F t₀) + hsNormSq m (F' t - F' t₀)))
        (𝓝[Icc a b] t₀) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) ((h2 t₀ ht₀).add (h2' t₀ ht₀)) (Or.inr (by norm_num))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have he : F t + F' t - (F t₀ + F' t₀) = (F t - F t₀) + (F' t - F' t₀) := by abel
    rw [he]
    exact hsNormSq_add_le_two_mul m ((h1 t ht).1.sub (h1 t₀ ht₀).1)

private theorem heatPart_isHsCurve (m : ℕ) (a b : ℝ) {F₀ : Space → CSpace}
    (hF₀ : AEStronglyMeasurable F₀ volume) (hF₀m : hsNormSq m F₀ < ⊤) :
    IsHsCurve m (heatPart a F₀) a b := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, fun t₀ ht₀ => tendsto_hsNormSq_heatPart hF₀ hF₀m t₀ ht₀⟩
  · have hc : Continuous (fun ξ : Space => ((heatSymbol (t - a) ξ : ℝ) : ℂ)) := by
      unfold heatSymbol
      fun_prop
    exact hc.aestronglyMeasurable.smul hF₀
  · have h := fracNormSq_heatPart_le (m : ℝ) ht.1 F₀
    rw [fracNormSq_natCast, fracNormSq_natCast] at h
    exact lt_of_le_of_lt h hF₀m

theorem varConstMap_isHsCurve (m : ℕ) (hm : 3 ≤ m) (a δ : ℝ) (F₀ : Space → CSpace)
    (G : ℝ → Space → CSpace) (_hδ : 0 < δ) (hF₀ : AEStronglyMeasurable F₀ volume)
    (hF₀m : hsNormSq m F₀ < ⊤) (hG : IsHsCurve m G a (a + δ)) :
    IsHsCurve m (varConstMap a F₀ G) a (a + δ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K, hK⟩ := hsNormSq_nonlinSymbol_curve_le (by omega) hG
  have hN := nonlinSymbol_aestronglyMeasurable_curve (by omega) hG
  have hD := varConstIntegral_isHsCurve k (fun s => nonlinSymbol (G s)) K hN hK
  have hH := heatPart_isHsCurve (k + 1) a (a + δ) hF₀ hF₀m
  have he : varConstMap a F₀ G = fun t => heatPart a F₀ t + varConstIntegral a (fun s => nonlinSymbol (G s)) t := by
    funext t ξ
    rfl
  rw [he]
  exact isHsCurve_add hH hD

end Breakdown.SmoothFlow
