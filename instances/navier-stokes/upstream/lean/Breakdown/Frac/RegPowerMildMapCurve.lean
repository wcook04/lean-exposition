import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegLocalAuxCurvePart2

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem powerMapCurve_add {m : ℕ} {F F' : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve m F a b) (hF' : IsHsCurve m F' a b) :
    IsHsCurve m (fun t => F t + F' t) a b := by
  obtain ⟨h1, h2⟩ := hF
  obtain ⟨h1', h2'⟩ := hF'
  refine ⟨fun t ht => ⟨(h1 t ht).1.add (h1' t ht).1, ?_⟩, fun t₀ ht₀ => ?_⟩
  · refine lt_of_le_of_lt (hsNormSq_add_le_two_mul m (h1 t ht).1) ?_
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2 ⟨(h1 t ht).2, (h1' t ht).2⟩)
  · have hlim : Tendsto (fun t => 2 * (hsNormSq m (F t - F t₀) + hsNormSq m (F' t - F' t₀)))
        (𝓝[Icc a b] t₀) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) ((h2 t₀ ht₀).add (h2' t₀ ht₀))
        (Or.inr (by norm_num))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have he : F t + F' t - (F t₀ + F' t₀) = (F t - F t₀) + (F' t - F' t₀) := by abel
    rw [he]
    exact hsNormSq_add_le_two_mul m ((h1 t ht).1.sub (h1 t₀ ht₀).1)

private theorem powerMapCurve_heat {α : ℝ} (h2 : PowerHeatPartStatement α) (m : ℕ) (a b : ℝ)
    {F₀ : Space → CSpace} (hF₀ : AEStronglyMeasurable F₀ volume) (hF₀m : hsNormSq m F₀ < ⊤) :
    IsHsCurve m (powerHeatPart α a F₀) a b := by
  obtain ⟨hmeas, hle, hcont⟩ := h2
  refine ⟨fun t ht => ⟨hmeas F₀ hF₀ a t, ?_⟩, fun t₀ ht₀ => hcont m F₀ hF₀ hF₀m a b t₀ ht₀⟩
  have h := hle (m : ℝ) a t ht.1 F₀
  rw [fracNormSq_natCast, fracNormSq_natCast] at h
  exact lt_of_le_of_lt h hF₀m

theorem powerMildMapCurve_of (α : ℝ) (_hα : 1 < α) (h1 : PowerMildIntegralCurveStatement α)
    (h2 : PowerHeatPartStatement α) : PowerMildMapCurveStatement α := by
  intro m hm a δ F₀ G _hδ hF₀ hF₀m hG
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K, hK⟩ := hsNormSq_nonlinSymbol_curve_le (by omega) hG
  have hN := nonlinSymbol_aestronglyMeasurable_curve (by omega) hG
  have hD := h1 k a (a + δ) (fun s => nonlinSymbol (G s)) K hN hK
  have hH := powerMapCurve_heat h2 (k + 1) a (a + δ) hF₀ hF₀m
  have he : powerMildMap α a F₀ G =
      fun t => powerHeatPart α a F₀ t + powerMildIntegral α a (fun s => nonlinSymbol (G s)) t := by
    funext t ξ
    rfl
  rw [he]
  exact powerMapCurve_add hH hD

end Breakdown.SmoothFlow
