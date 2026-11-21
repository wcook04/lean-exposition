import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hsNormSq_mono_index {m : ℕ} (hm : 2 ≤ m) (f : Space → CSpace) :
    hsNormSq 2 f ≤ hsNormSq m f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  unfold hsWeight
  exact pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖ξ‖]) hm

theorem freqL1Norm_lt_top_of_hsNormSq {m : ℕ} (hm : 2 ≤ m) {f : Space → CSpace}
    (hf : hsNormSq m f < ⊤) : freqL1Norm f < ⊤ := by
  obtain ⟨C, hC⟩ := freqL1Norm_le_hsNormSq
  refine (hC f).trans_lt ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ((hsNormSq_mono_index hm f).trans_lt hf).ne

private theorem hsNormSq_eq_eLpNorm_sq (m : ℕ) (f : Space → CSpace) :
    hsNormSq m f =
      eLpNorm f 2 (volume.withDensity fun ξ => ENNReal.ofReal (hsWeight m ξ)) ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_withDensity_eq_lintegral_mul_non_measurable]
  · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    rfl
  · exact ENNReal.measurable_ofReal.comp (by unfold hsWeight; fun_prop)
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem tendsto_eLpNorm_of_tendsto_sub {ι : Type*} {l : Filter ι} {μ : Measure Space}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {G : ι → Space → CSpace} {g : Space → CSpace}
    (hG : ∀ᶠ i in l, AEStronglyMeasurable (G i) μ) (hg : AEStronglyMeasurable g μ)
    (hfin : eLpNorm g p μ ≠ ⊤) (h : Tendsto (fun i => eLpNorm (G i - g) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (G i) p μ) l (𝓝 (eLpNorm g p μ)) := by
  rw [ENNReal.tendsto_nhds hfin]
  intro ε hε
  filter_upwards [hG, h.eventually (Iio_mem_nhds hε)] with i hi hi2
  have h1 : eLpNorm (G i) p μ ≤ eLpNorm (G i - g) p μ + eLpNorm g p μ := by
    calc eLpNorm (G i) p μ = eLpNorm (G i - g + g) p μ := by rw [sub_add_cancel]
      _ ≤ _ := eLpNorm_add_le (hi.sub hg) hg hp
  have h2 : eLpNorm g p μ ≤ eLpNorm (G i - g) p μ + eLpNorm (G i) p μ := by
    calc eLpNorm g p μ = eLpNorm (G i - (G i - g)) p μ := by rw [sub_sub_cancel]
      _ ≤ eLpNorm (G i) p μ + eLpNorm (G i - g) p μ := eLpNorm_sub_le hi (hi.sub hg) hp
      _ = _ := add_comm _ _
  have hi3 : eLpNorm (G i - g) p μ ≤ ε := le_of_lt hi2
  constructor
  · rw [tsub_le_iff_left]
    calc eLpNorm g p μ ≤ eLpNorm (G i - g) p μ + eLpNorm (G i) p μ := h2
      _ ≤ ε + eLpNorm (G i) p μ := by gcongr
  · calc eLpNorm (G i) p μ ≤ eLpNorm (G i - g) p μ + eLpNorm g p μ := h1
      _ ≤ ε + eLpNorm g p μ := by gcongr
      _ = eLpNorm g p μ + ε := add_comm _ _

theorem continuousOn_hsNormSq_toReal {m : ℕ} {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) :
    ContinuousOn (fun t => (hsNormSq m (F t)).toReal) (Icc 0 T) := by
  intro t₀ ht₀
  set μ : Measure Space := volume.withDensity fun ξ => ENNReal.ofReal (hsWeight m ξ) with hμ
  have hac : μ ≪ volume := withDensity_absolutelyContinuous _ _
  have hmeas : ∀ᶠ t in 𝓝[Icc 0 T] t₀, AEStronglyMeasurable (F t) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hF.1 t ht).1.mono_ac hac
  have hfin0 : hsNormSq m (F t₀) ≠ ⊤ := (hF.1 t₀ ht₀).2.ne
  have hfin : eLpNorm (F t₀) 2 μ ≠ ⊤ := by
    intro htop
    apply hfin0
    rw [hsNormSq_eq_eLpNorm_sq, ← hμ, htop]
    simp
  have hsub : Tendsto (fun t => eLpNorm (F t - F t₀) 2 μ) (𝓝[Icc 0 T] t₀) (𝓝 0) := by
    have h0 := hF.2 t₀ ht₀
    have hc : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    refine (hc.comp h0).congr fun t => ?_
    simp only [Function.comp_apply]
    rw [hsNormSq_eq_eLpNorm_sq, ← hμ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hlim := tendsto_eLpNorm_of_tendsto_sub (by norm_num) hmeas ((hF.1 t₀ ht₀).1.mono_ac hac)
    hfin hsub
  have hsq : Tendsto (fun t => hsNormSq m (F t)) (𝓝[Icc 0 T] t₀) (𝓝 (hsNormSq m (F t₀))) := by
    have := ENNReal.Tendsto.pow (n := 2) hlim
    simpa only [hsNormSq_eq_eLpNorm_sq, ← hμ] using this
  exact (ENNReal.tendsto_toReal hfin0).comp hsq

theorem continuousOn_freqL1Norm_toReal {m : ℕ} (hm : 2 ≤ m) {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) :
    ContinuousOn (fun t => (freqL1Norm (F t)).toReal) (Icc 0 T) := by
  intro t₀ ht₀
  have hW : ∀ f : Space → CSpace, freqL1Norm f = eLpNorm f 1 volume := fun f =>
    eLpNorm_one_eq_lintegral_enorm.symm
  have hfin0 : freqL1Norm (F t₀) ≠ ⊤ :=
    (freqL1Norm_lt_top_of_hsNormSq hm (hF.1 t₀ ht₀).2).ne
  have hmeas : ∀ᶠ t in 𝓝[Icc 0 T] t₀, AEStronglyMeasurable (F t) volume := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hF.1 t ht).1
  obtain ⟨C, hC⟩ := freqL1Norm_le_hsNormSq
  have hbound : Tendsto (fun t => ENNReal.ofReal C * hsNormSq m (F t - F t₀) ^ (1 / 2 : ℝ))
      (𝓝[Icc 0 T] t₀) (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) (hc.comp (hF.2 t₀ ht₀))
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact this
  have hsub : Tendsto (fun t => eLpNorm (F t - F t₀) 1 volume) (𝓝[Icc 0 T] t₀) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => zero_le) fun t => ?_
    rw [← hW]
    refine (hC _).trans ?_
    gcongr
    exact hsNormSq_mono_index hm _
  have hlim := tendsto_eLpNorm_of_tendsto_sub le_rfl hmeas (hF.1 t₀ ht₀).1
    (by rw [← hW]; exact hfin0) hsub
  have hlim' : Tendsto (fun t => freqL1Norm (F t)) (𝓝[Icc 0 T] t₀) (𝓝 (freqL1Norm (F t₀))) := by
    simpa only [hW] using hlim
  exact (ENNReal.tendsto_toReal hfin0).comp hlim'

end Breakdown.SmoothFlow
