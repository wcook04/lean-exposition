import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

private theorem inner_field_eq_zero {Φ : Space → Space} {x : Space} (hx : x ∉ tsupport Φ)
    (a : Space) : inner ℝ a (Φ x) = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]

theorem continuousOn_integral_inner_field {T : ℝ} {v : ℝ → Space → Space}
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ)) {Φ : Space → Space}
    (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) :
    ContinuousOn (fun τ => ∫ x, inner ℝ (v τ x) (Φ x)) (Icc 0 T) := by
  have hf : ContinuousOn (fun p : ℝ × Space => inner ℝ (v p.1 p.2) (Φ p.2)) (Icc 0 T ×ˢ univ) :=
    hv.continuousOn.inner (hΦ.comp continuous_snd).continuousOn
  have h := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) (f := fun τ x => inner ℝ (v τ x) (Φ x))
    (g := fun _ : Space => (1 : ℝ)) hc hf
    (fun p x _ hx => inner_field_eq_zero hx _) (integrableOn_const hc.measure_lt_top.ne)
  simpa using h

theorem hasDerivAt_integral_inner_field {T : ℝ} {v : ℝ → Space → Space}
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ)) {Φ : Space → Space}
    (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun τ => ∫ x, inner ℝ (v τ x) (Φ x))
      (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) t := by
  have hm : 0 < min t (T - t) := lt_min ht.1 (by linarith [ht.2])
  have h1 := min_le_left t (T - t)
  have h2 := min_le_right t (T - t)
  set h := min t (T - t) / 2 with hh
  have hsub : Icc (t - h) (t + h) ⊆ Ioo 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsub' : Icc (t - h) (t + h) ⊆ Icc 0 T := hsub.trans Ioo_subset_Icc_self
  have hnhds : Icc (t - h) (t + h) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hD : ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0)) (Ioo 0 T ×ˢ univ) :=
    CutoffEnergy.continuousOn_fderiv_slice_time hv
  have hK : IsCompact (tsupport Φ) := hc
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ((hD.norm.mul (hΦ.comp continuous_snd).continuousOn.norm).mono
      (prod_mono hsub (subset_univ _)))
  have hcont : ∀ τ ∈ Icc 0 T, Continuous (fun x => inner ℝ (v τ x) (Φ x)) := fun τ hτ =>
    (CutoffEnergy.contDiff_slice hv hτ).continuous.inner hΦ
  have hDx : Continuous (fun x => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t, x) (1, 0)) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hmem : Ioo 0 T ×ˢ univ ∈ 𝓝 (t, x) := prod_mem_nhds (Ioo_mem_nhds ht.1 ht.2) univ_mem
    exact ((hD.continuousAt hmem).comp (Continuous.continuousAt (by fun_prop)) :)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ x => inner ℝ (v τ x) (Φ x))
    (F' := fun τ x => inner ℝ (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (τ, x) (1, 0)) (Φ x))
    (bound := indicator (tsupport Φ) (fun _ => M)) hnhds
    (eventually_of_mem hnhds fun τ hτ => (hcont τ (hsub' hτ)).aestronglyMeasurable)
    ((hcont t (Ioo_subset_Icc_self ht)).integrable_of_hasCompactSupport
      (hc.mono fun x hx => fun h0 => hx (by simp [h0])))
    ((hDx.inner hΦ).aestronglyMeasurable)
    (ae_of_all _ fun x τ hτ => ?_)
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet)
    (ae_of_all _ fun x τ hτ => ?_)
  · have e : (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) =
        ∫ x, inner ℝ (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t, x) (1, 0)) (Φ x) := by
      congr 1; funext x; rw [(CutoffEnergy.hasDerivAt_slice_time hv ht x).deriv]
    rw [e]; exact key.2
  · by_cases hx : x ∈ tsupport Φ
    · rw [indicator_of_mem hx]
      have := hM (τ, x) ⟨hτ, hx⟩
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by simpa using this)
    · rw [indicator_of_notMem hx, inner_field_eq_zero hx, norm_zero]
  · have hd := CutoffEnergy.hasDerivAt_slice_time hv (hsub hτ) x
    have := hd.inner ℝ (hasDerivAt_const τ (Φ x))
    simpa using this

end Breakdown.Internal
