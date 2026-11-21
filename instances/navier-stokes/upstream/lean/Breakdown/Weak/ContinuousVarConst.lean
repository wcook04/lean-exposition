import Breakdown.Weak.StatementsTime

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.ContinuousVarConst

theorem bilinX_of_nonpos {σ : ℝ} (h : σ ≤ 0) : bilinX σ = 0 := by
  unfold bilinX
  exact dif_neg (fun h' => by linarith [h'.1])

theorem norm_bilin_le {C M σ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    (hσ : 0 ≤ σ) {u : X} (hu : ‖u‖ ≤ M) :
    ‖bilinX σ u u‖ ≤ C * M * M * σ ^ (-(3 / 4 : ℝ)) := by
  rcases hσ.lt_or_eq with hσ | hσ
  · have h2 : 0 ≤ C * σ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC0 (rpow_nonneg hσ.le _)
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    calc ‖bilinX σ u u‖ ≤ C * σ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖u‖ := hC σ hσ u u
      _ ≤ C * σ ^ (-(3 / 4 : ℝ)) * M * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu h2) hu hu0 (mul_nonneg h2 (hu0.trans hu))
      _ = C * M * M * σ ^ (-(3 / 4 : ℝ)) := by ring
  · have h0 : bilinX σ = 0 := bilinX_of_nonpos hσ.ge
    have h1 : ‖bilinX σ u u‖ = 0 := by simp [h0]
    have h2 : (0 : ℝ) ^ (-(3 / 4 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    calc ‖bilinX σ u u‖ = 0 := h1
      _ ≤ C * M * M * σ ^ (-(3 / 4 : ℝ)) := by rw [← hσ, h2, mul_zero]

theorem kernel_integral (t m : ℝ) :
    ∫ τ in m..t, (t - τ) ^ (-(3 / 4 : ℝ)) = 4 * (t - m) ^ (1 / 4 : ℝ) := by
  have h : ∫ τ in m..t, (t - τ) ^ (-(3 / 4 : ℝ)) = ∫ x in t - t..t - m, x ^ (-(3 / 4 : ℝ)) :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) t
  rw [h, integral_rpow (Or.inl (by norm_num)), sub_self]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

theorem kernel_intervalIntegrable (t m : ℝ) :
    IntervalIntegrable (fun τ => (t - τ) ^ (-(3 / 4 : ℝ))) volume m t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - m) (b := t - t)
    (by norm_num : (-1 : ℝ) < -(3 / 4))).comp_sub_left t
  have e1 : t - (t - m) = m := by ring
  have e2 : t - (t - t) = t := by ring
  rw [e1, e2] at h
  exact h

theorem integ (hBI : BilinIntegrable) {y : ℝ → X} {l r M : ℝ} (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M)
    (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r))) {t₀ c t : ℝ} (hl : l < t₀)
    (h0 : t₀ ≤ c) (hct : c ≤ t) (htr : t < r) :
    IntervalIntegrable (fun τ => bilinX (t - τ) (y τ) (y τ)) volume t₀ c := by
  have h := hBI y l r M hM hy t₀ c (t - c) hl h0 (lt_of_le_of_lt hct htr) (sub_nonneg.2 hct)
  have e : ∀ τ : ℝ, c - τ + (t - c) = t - τ := fun τ => by ring
  simp only [e] at h
  exact h

theorem remainder (hBI : BilinIntegrable) {y : ℝ → X} {l r M C : ℝ}
    (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M) (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r)))
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {t₀ t δ : ℝ} (hl : l < t₀) (htt : t₀ ≤ t) (htr : t < r) (hδ : 0 < δ) :
    ‖(∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)) -
      ∫ τ in t₀..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)‖ ≤
        C * M * M * (4 * δ ^ (1 / 4 : ℝ)) := by
  have hm1 : t₀ ≤ max t₀ (t - δ) := le_max_left _ _
  have hm2 : max t₀ (t - δ) ≤ t := max_le htt (by linarith)
  have hm3 : t - max t₀ (t - δ) ≤ δ := by
    have := le_max_right t₀ (t - δ)
    linarith
  have hCMM : 0 ≤ C * M * M := mul_nonneg (mul_nonneg hC0 hM0) hM0
  rw [intervalIntegral.integral_interval_sub_left (integ hBI hM hy hl htt le_rfl htr)
    (integ hBI hM hy hl hm1 hm2 htr)]
  calc ‖∫ τ in max t₀ (t - δ)..t, bilinX (t - τ) (y τ) (y τ)‖
      ≤ ∫ τ in max t₀ (t - δ)..t, C * M * M * (t - τ) ^ (-(3 / 4 : ℝ)) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hm2 (ae_of_all _ fun τ hτ => ?_)
          ((kernel_intervalIntegrable t _).const_mul _)
        exact norm_bilin_le hC0 hC (by linarith [hτ.2])
          (hM τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    _ = C * M * M * (4 * (t - max t₀ (t - δ)) ^ (1 / 4 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul, kernel_integral]
    _ ≤ C * M * M * (4 * δ ^ (1 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hCMM
        exact rpow_le_rpow (by linarith) hm3 (by norm_num)

theorem pt_bound {y : ℝ → X} {l r M C : ℝ} (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M) (hM0 : 0 ≤ M)
    (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {t τ δ : ℝ} (hδ : 0 < δ) (h : δ / 2 ≤ t - τ) (hτ : τ ∈ Ioo l r) :
    ‖bilinX (t - τ) (y τ) (y τ)‖ ≤ C * M * M * (δ / 2) ^ (-(3 / 4 : ℝ)) :=
  (norm_bilin_le hC0 hC (by linarith) (hM τ hτ)).trans
    (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos (by linarith) h (by norm_num))
      (mul_nonneg (mul_nonneg hC0 hM0) hM0))

theorem le_of_le_max {τ a c : ℝ} (h1 : a < τ) (h2 : τ ≤ max a c) : τ ≤ c := by
  rcases le_max_iff.1 h2 with h | h
  · exact absurd h (not_le.2 h1)
  · exact h

set_option maxHeartbeats 1000000 in
theorem trunc_continuousOn (hBI : BilinIntegrable) {y : ℝ → X} {l r M C : ℝ}
    (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M) (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r)))
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {t₀ b δ : ℝ} (hl : l < t₀) (hbr : b < r) (hδ : 0 < δ) :
    ContinuousOn (fun t => ∫ τ in t₀..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)) (Icc t₀ b) := by
  intro s hs
  have hev : ∀ᶠ t in 𝓝[Icc t₀ b] s, t ∈ Icc t₀ b ∧ t ∈ Ioo (s - δ / 2) (s + δ / 2) :=
    Filter.Eventually.and self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)))
  have hms1 : t₀ ≤ max t₀ (s - δ) := le_max_left _ _
  have hsplit : ∀ᶠ t in 𝓝[Icc t₀ b] s,
      (∫ τ in t₀..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)) =
        (∫ τ in t₀..max t₀ (s - δ), bilinX (t - τ) (y τ) (y τ)) +
          ∫ τ in max t₀ (s - δ)..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ) := by
    filter_upwards [hev] with t ht
    have hc : max (max t₀ (s - δ)) (max t₀ (t - δ)) ≤ t :=
      max_le (max_le ht.1.1 (by linarith [ht.2.1])) (max_le ht.1.1 (by linarith))
    have hI := integ hBI hM hy hl (hms1.trans (le_max_left _ _)) hc (lt_of_le_of_lt ht.1.2 hbr)
    have h1 := hI.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hms1 (le_max_left _ _)))
    have h2 := hI.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hms1 (le_max_left _ _))
      (mem_uIcc_of_le (le_max_left _ _) (le_max_right _ _)))
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hA : ContinuousWithinAt (fun t => ∫ τ in t₀..max t₀ (s - δ), bilinX (t - τ) (y τ) (y τ))
      (Icc t₀ b) s := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _ => C * M * M * (δ / 2) ^ (-(3 / 4 : ℝ))) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with t ht
      have hst : max t₀ (s - δ) ≤ t := max_le ht.1.1 (by linarith [ht.2.1])
      exact Integrable.aestronglyMeasurable
        (intervalIntegrable_iff.1 (integ hBI hM hy hl hms1 hst (lt_of_le_of_lt ht.1.2 hbr)))
    · filter_upwards [hev] with t ht
      refine ae_of_all _ fun τ hτ => ?_
      rw [uIoc_of_le hms1] at hτ
      have h3 := le_of_le_max hτ.1 hτ.2
      exact pt_bound hM hM0 hC0 hC hδ (by linarith [ht.2.1])
        ⟨by linarith [hτ.1], by linarith [hs.2]⟩
    · refine ae_of_all _ fun τ hτ => ?_
      rw [uIoc_of_le hms1] at hτ
      have h3 := le_of_le_max hτ.1 hτ.2
      have hc : ContinuousAt (fun σ => bilinX σ (y τ) (y τ)) (s - τ) :=
        (bilinCont_holds (y τ) (y τ)).continuousAt (Ioi_mem_nhds (by linarith))
      exact (hc.comp (f := fun t : ℝ => t - τ) (by fun_prop)).continuousWithinAt
  have hB : Tendsto (fun t => ∫ τ in max t₀ (s - δ)..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ))
      (𝓝[Icc t₀ b] s) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => C * M * M * (δ / 2) ^ (-(3 / 4 : ℝ)) *
      |max t₀ (t - δ) - max t₀ (s - δ)|) ?_ ?_
    · filter_upwards [hev] with t ht
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
      have hmt := le_max_left t₀ (t - δ)
      rcases Set.mem_uIoc.1 hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h3 := le_of_le_max (lt_of_le_of_lt hms1 h1) h2
        exact pt_bound hM hM0 hC0 hC hδ (by linarith)
          ⟨by linarith, by linarith [hs.2, ht.1.2]⟩
      · have h3 := le_of_le_max (lt_of_le_of_lt hmt h1) h2
        exact pt_bound hM hM0 hC0 hC hδ (by linarith [ht.2.1])
          ⟨by linarith, by linarith [hs.2]⟩
    · have hc : Continuous fun t : ℝ => C * M * M * (δ / 2) ^ (-(3 / 4 : ℝ)) *
          |max t₀ (t - δ) - max t₀ (s - δ)| := by fun_prop
      have h0 := hc.tendsto s
      simp only [sub_self, abs_zero, mul_zero] at h0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hBc : ContinuousWithinAt
      (fun t => ∫ τ in max t₀ (s - δ)..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)) (Icc t₀ b) s := by
    show Tendsto _ (𝓝[Icc t₀ b] s)
      (𝓝 (∫ τ in max t₀ (s - δ)..max t₀ (s - δ), bilinX (s - τ) (y τ) (y τ)))
    rw [intervalIntegral.integral_same]
    exact hB
  have hAB : ContinuousWithinAt (fun t => (∫ τ in t₀..max t₀ (s - δ), bilinX (t - τ) (y τ) (y τ)) +
      ∫ τ in max t₀ (s - δ)..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)) (Icc t₀ b) s :=
    hA.add hBc
  refine hAB.congr_of_eventuallyEq hsplit ?_
  rw [intervalIntegral.integral_same, add_zero]

theorem integral_continuousOn (hBI : BilinIntegrable) {y : ℝ → X} {l r M C : ℝ}
    (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M) (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r)))
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {t₀ b : ℝ} (hl : l < t₀) (hbr : b < r) :
    ContinuousOn (fun t => ∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)) (Icc t₀ b) := by
  refine TendstoUniformlyOn.continuousOn
    (F := fun δ t => ∫ τ in t₀..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ))
    (p := 𝓝[>] (0 : ℝ)) ?_ ?_
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hc : ContinuousAt (fun δ : ℝ => C * M * M * (4 * δ ^ (1 / 4 : ℝ))) 0 :=
      continuousAt_const.mul (continuousAt_const.mul
        (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))))
    have h0 : Tendsto (fun δ : ℝ => C * M * M * (4 * δ ^ (1 / 4 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
      have h := hc.tendsto
      simp only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    filter_upwards [(tendsto_order.1 h0).2 ε hε, self_mem_nhdsWithin] with δ h1 (h2 : 0 < δ) t ht
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (remainder hBI hM hy hM0 hC0 hC hl ht.1 (lt_of_le_of_lt ht.2 hbr) h2) h1
  · have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ContinuousOn
        (fun t => ∫ τ in t₀..max t₀ (t - δ), bilinX (t - τ) (y τ) (y τ)) (Icc t₀ b) := by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      exact trunc_continuousOn hBI hM hy hM0 hC0 hC hl hbr hδ
    exact hev.frequently

end Internal.ContinuousVarConst

open Internal.ContinuousVarConst in
theorem continuousVarConst_holds : ContinuousVarConst := by
  intro hBI y l r M hM hy t₀ ht₀ s hs
  obtain ⟨C, hC0, hC⟩ := bilin_holds.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ht₀)
  obtain ⟨b, hsb, hbr⟩ := exists_between hs.2
  have hH : ContinuousOn (fun t => heatX (t - t₀) (y t₀)) (Ici t₀) :=
    (heat_holds.2.2.2.1 (y t₀)).comp (by fun_prop)
      (fun t (ht : t₀ ≤ t) => (sub_nonneg.2 ht : (0 : ℝ) ≤ t - t₀))
  have hD : ContinuousOn (varConst y t₀) (Icc t₀ b) :=
    (hH.mono Icc_subset_Ici_self).add (integral_continuousOn hBI hM hy hM0 hC0 hC ht₀.1 hbr)
  exact (hD s ⟨hs.1, hsb.le⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hsb, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩)

end Breakdown.WeakProfile
