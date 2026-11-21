import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Metric

noncomputable section

namespace Breakdown.Internal.CutoffEnergy

theorem contDiff_cutoffPow {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (cutoffPow r) := by
  show ContDiff ℝ ∞ (fun x => radialCutoff r x ^ 4)
  exact (contDiff_radialCutoff hr).pow 4

theorem cutoffPow_eq_zero {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : x ∉ closedBall (0 : Space) (2 * r)) : cutoffPow r x = 0 := by
  have h : 2 * r ≤ ‖x‖ := by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  simp [cutoffPow, radialCutoff_eq_zero hr h]

theorem hasCompactSupport_of_cutoffPow {E : Type*} [NormedAddCommGroup E] {r : ℝ} (hr : 0 < r)
    {g : Space → E} (hg : ∀ x, cutoffPow r x = 0 → g x = 0) : HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * r)) fun x hx => hg x (cutoffPow_eq_zero hr hx)

theorem hasCompactSupport_cutoffPow {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoffPow r) :=
  hasCompactSupport_of_cutoffPow hr fun _ h => h

theorem abs_cutoffPow_le_one (r : ℝ) (x : Space) : |cutoffPow r x| ≤ 1 := by
  have h0 := radialCutoff_nonneg r x
  have h1 := radialCutoff_le_one r x
  rw [cutoffPow, abs_of_nonneg (pow_nonneg h0 4)]
  exact pow_le_one₀ h0 h1

theorem integrable_cutoffPow_mul {r : ℝ} (hr : 0 < r) {g : Space → ℝ} (hg : Continuous g) :
    Integrable (fun x => cutoffPow r x * g x) :=
  ((contDiff_cutoffPow hr).continuous.mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_of_cutoffPow hr fun x h => by simp [h])

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {τ : ℝ}
    (hτ : τ ∈ Icc 0 T) : ContDiff ℝ ∞ (f τ) := by
  have h : ContDiffOn ℝ ∞ ((fun z : ℝ × Space => f z.1 z.2) ∘ fun x : Space => (τ, x)) univ :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨hτ, mem_univ x⟩)
  exact contDiffOn_univ.1 h

theorem hasDerivAt_slice_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun s => f s x) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (τ, x) (1, 0)) τ := by
  have hmem : Icc 0 T ×ˢ univ ∈ 𝓝 (τ, x) := prod_mem_nhds (Icc_mem_nhds hτ.1 hτ.2) Filter.univ_mem
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => f z.1 z.2) (τ, x) :=
    (hf.contDiffAt hmem).differentiableAt (by simp)
  have h2 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  exact hd.hasFDerivAt.comp_hasDerivAt τ h2

theorem continuousOn_fderiv_slice_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z (1, 0))
      (Ioo 0 T ×ˢ univ) := by
  have h := (hf.mono (prod_mono Ioo_subset_Icc_self subset_rfl)).continuousOn_fderiv_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) (by simp)
  exact h.clm_apply continuousOn_const

theorem continuousOn_cutoffEnergy_sub {T : ℝ} {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hu : IsSolutionOn T u p) (hv : IsSolutionOn T v q) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun τ => cutoffEnergy r (v τ - u τ)) (Icc 0 T) := by
  have hW : ContinuousOn (fun z : ℝ × Space => v z.1 z.2 - u z.1 z.2) (Icc 0 T ×ˢ univ) :=
    hv.smooth_velocity.continuousOn.sub hu.smooth_velocity.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) (2 * r))).exists_bound_of_continuousOn
    (hW.mono (prod_mono subset_rfl (subset_univ _)))
  have hint : ContinuousOn (fun τ => ∫ x, cutoffPow r x * ‖v τ x - u τ x‖ ^ 2) (Icc 0 T) := by
    apply continuousOn_of_dominated (bound := indicator (closedBall (0 : Space) (2 * r)) (fun _ => C ^ 2))
    · intro τ hτ
      exact ((contDiff_cutoffPow hr).continuous.mul
        (((contDiff_slice hv.smooth_velocity hτ).continuous.sub
          (contDiff_slice hu.smooth_velocity hτ).continuous).norm.pow 2)).aestronglyMeasurable
    · intro τ hτ
      refine ae_of_all _ fun x => ?_
      by_cases hx : x ∈ closedBall (0 : Space) (2 * r)
      · rw [indicator_of_mem hx]
        have h1 : ‖v τ x - u τ x‖ ≤ C := hC (τ, x) ⟨hτ, hx⟩
        have h2 := abs_cutoffPow_le_one r x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v τ x - u τ x‖ ^ 2)]
        have h3 : ‖v τ x - u τ x‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        calc |cutoffPow r x| * ‖v τ x - u τ x‖ ^ 2 ≤ 1 * C ^ 2 :=
              mul_le_mul h2 h3 (by positivity) zero_le_one
          _ = C ^ 2 := one_mul _
      · rw [indicator_of_notMem hx, cutoffPow_eq_zero hr hx]
        simp
    · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
    · refine ae_of_all _ fun x => ?_
      have h : ContinuousOn (fun τ => v τ x - u τ x) (Icc 0 T) :=
        hW.comp (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => ⟨hτ, mem_univ x⟩)
      exact continuousOn_const.mul (h.norm.pow 2)
  have hfun : (fun τ => cutoffEnergy r (v τ - u τ)) =
      fun τ => (1 / 2) * ∫ x, cutoffPow r x * ‖v τ x - u τ x‖ ^ 2 := rfl
  rw [hfun]
  exact continuousOn_const.mul hint

theorem hasDerivAt_cutoffEnergy_inner {T : ℝ} {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hu : IsSolutionOn T u p) (hv : IsSolutionOn T v q) {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun τ => cutoffEnergy r (v τ - u τ))
      (∫ x, cutoffPow r x * inner ℝ (v t x - u t x)
        (deriv (fun τ => v τ x) t - deriv (fun τ => u τ x) t)) t := by
  have hm : 0 < min t (T - t) := lt_min ht.1 (by linarith [ht.2])
  have h1 := min_le_left t (T - t)
  have h2 := min_le_right t (T - t)
  have hsub : Icc (t - min t (T - t) / 2) (t + min t (T - t) / 2) ⊆ Ioo 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsub' : Icc (t - min t (T - t) / 2) (t + min t (T - t) / 2) ⊆ Icc 0 T :=
    hsub.trans Ioo_subset_Icc_self
  have hnhds : Icc (t - min t (T - t) / 2) (t + min t (T - t) / 2) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hW : ContinuousOn (fun z : ℝ × Space => v z.1 z.2 - u z.1 z.2) (Ioo 0 T ×ˢ univ) :=
    (hv.smooth_velocity.continuousOn.sub hu.smooth_velocity.continuousOn).mono
      (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hD : ContinuousOn (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) -
        fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) z (1, 0)) (Ioo 0 T ×ˢ univ) :=
    (continuousOn_fderiv_slice_time hv.smooth_velocity).sub
      (continuousOn_fderiv_slice_time hu.smooth_velocity)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) (2 * r))).exists_bound_of_continuousOn
    ((hW.norm.mul hD.norm).mono (prod_mono hsub (subset_univ _)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ x => cutoffPow r x * ‖v τ x - u τ x‖ ^ 2)
    (F' := fun τ x => cutoffPow r x * (2 * inner ℝ (v τ x - u τ x)
      (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (τ, x) (1, 0) -
        fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (τ, x) (1, 0))))
    (bound := indicator (closedBall (0 : Space) (2 * r)) (fun _ => 2 * C)) hnhds
    (Filter.eventually_of_mem hnhds fun τ hτ =>
      ((contDiff_cutoffPow hr).continuous.mul
        (((contDiff_slice hv.smooth_velocity (hsub' hτ)).continuous.sub
          (contDiff_slice hu.smooth_velocity (hsub' hτ)).continuous).norm.pow 2)).aestronglyMeasurable)
    (integrable_cutoffPow_mul hr
        (((contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)).continuous.sub
          (contDiff_slice hu.smooth_velocity (Ioo_subset_Icc_self ht)).continuous).norm.pow 2))
    (by
      have hc : Continuous (fun x : Space =>
          fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t, x) (1, 0) -
            fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (t, x) (1, 0)) :=
        hD.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
      exact ((contDiff_cutoffPow hr).continuous.mul (continuous_const.mul
        ((((contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)).continuous.sub
          (contDiff_slice hu.smooth_velocity (Ioo_subset_Icc_self ht)).continuous)).inner hc))).aestronglyMeasurable)
    (by
      refine ae_of_all _ fun x τ hτ => ?_
      by_cases hx : x ∈ closedBall (0 : Space) (2 * r)
      · rw [indicator_of_mem hx]
        have h3' : ‖‖v τ x - u τ x‖ * ‖fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (τ, x) (1, 0) -
            fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (τ, x) (1, 0)‖‖ ≤ C := hC (τ, x) ⟨hτ, hx⟩
        have h3 := (Real.le_norm_self _).trans h3'
        have h4 := abs_cutoffPow_le_one r x
        have h5 := abs_real_inner_le_norm (v τ x - u τ x)
          (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (τ, x) (1, 0) -
            fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (τ, x) (1, 0))
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
        calc |cutoffPow r x| * (2 * |inner ℝ (v τ x - u τ x)
              (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (τ, x) (1, 0) -
                fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (τ, x) (1, 0))|)
            ≤ 1 * (2 * C) := mul_le_mul h4 (by linarith) (by positivity) zero_le_one
          _ = 2 * C := one_mul _
      · rw [indicator_of_notMem hx, cutoffPow_eq_zero hr hx]
        simp)
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne))
    (ae_of_all _ fun x τ hτ =>
      (((hasDerivAt_slice_time hv.smooth_velocity (hsub hτ) x).sub
        (hasDerivAt_slice_time hu.smooth_velocity (hsub hτ) x)).norm_sq).const_mul (cutoffPow r x))
  have hfun : (fun τ => cutoffEnergy r (v τ - u τ)) =
      fun τ => (1 / 2) * ∫ x, cutoffPow r x * ‖v τ x - u τ x‖ ^ 2 := rfl
  have hval : (1 / 2) * ∫ x, cutoffPow r x * (2 * inner ℝ (v t x - u t x)
      (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t, x) (1, 0) -
        fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (t, x) (1, 0))) =
      ∫ x, cutoffPow r x * inner ℝ (v t x - u t x)
        (deriv (fun τ => v τ x) t - deriv (fun τ => u τ x) t) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [(hasDerivAt_slice_time hv.smooth_velocity ht x).deriv,
      (hasDerivAt_slice_time hu.smooth_velocity ht x).deriv]
    ring
  rw [hfun, ← hval]
  exact key.2.const_mul (1 / 2)

end Breakdown.Internal.CutoffEnergy
