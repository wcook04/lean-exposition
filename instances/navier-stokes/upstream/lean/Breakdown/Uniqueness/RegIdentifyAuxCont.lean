import Breakdown.Uniqueness.RegEmbed

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal.RegIdentifyCont

theorem eLpNorm_gradWeight_le (d : Space → CSpace) :
    eLpNorm (fun ξ => (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • d ξ) 2 volume ≤
      (ENNReal.ofReal (4 * π ^ 2) * hsNormSq 1 d) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [hsNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  have hw : 0 ≤ hsWeight 1 η := by unfold hsWeight; positivity
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_two, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h6 : hsWeight 1 η = 1 + ‖η‖ ^ 2 := by simp [hsWeight]
  rw [h6]
  have key : (2 * π * ‖η‖ * ‖d η‖) ^ 2 + 4 * π ^ 2 * ‖d η‖ ^ 2 =
      4 * π ^ 2 * ((1 + ‖η‖ ^ 2) * ‖d η‖ ^ 2) := by ring
  have hp : 0 ≤ 4 * π ^ 2 * ‖d η‖ ^ 2 := by positivity
  linarith

theorem tendsto_rpow_half {l : Filter ℝ} {Y : ℝ → ℝ≥0∞} (hY : Tendsto Y l (𝓝 0)) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) : Tendsto (fun s => (c * Y s) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have h1 : Tendsto (fun s => c * Y s) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hY (Or.inr hc)
  have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h1
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h2

end Internal.RegIdentifyCont

open Internal.RegIdentifyCont

theorem continuousOn_embedX_physField (hR : FieldOpRealized) {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    ContinuousOn (fun t => embedX (physField (F t))) (Icc 0 T) := by
  intro t₀ ht₀
  have hmem : ∀ᶠ t in 𝓝[Icc 0 T] t₀, t ∈ Icc 0 T := self_mem_nhdsWithin
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  have hlim := tendsto_rpow_half ((hF 1).2 t₀ ht₀) (ENNReal.ofReal (4 * π ^ 2)) ENNReal.ofReal_ne_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hmem] with t ht
  have e1 := coe_embedX_physField hR ((hF 0).1 t ht).1 (hs t ht) (fun m => ((hF m).1 t ht).2)
  have e0 := coe_embedX_physField hR ((hF 0).1 t₀ ht₀).1 (hs t₀ ht₀)
    (fun m => ((hF m).1 t₀ ht₀).2)
  change edist ((embedX (physField (F t)) : X) : L2C) ((embedX (physField (F t₀)) : X) : L2C) ≤ _
  rw [Lp.edist_def, eLpNorm_congr_ae (e1.sub e0)]
  refine le_of_eq_of_le ?_ (eLpNorm_gradWeight_le (F t - F t₀))
  congr 1
  funext ξ
  simp [smul_sub]

end Breakdown.SmoothFlow
