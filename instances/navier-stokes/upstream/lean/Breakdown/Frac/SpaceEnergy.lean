import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.LocalEnergyAuxIbp
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Metric

noncomputable section

namespace Breakdown.FracInternal.SpaceEnergy

open Breakdown.Internal.CutoffEnergy

private theorem continuousOn_energy_of_smooth {T : ℝ} {u v : ℝ → Space → Space}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ)) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun τ => cutoffEnergy r (v τ - u τ)) (Icc 0 T) := by
  have hW : ContinuousOn (fun z : ℝ × Space => v z.1 z.2 - u z.1 z.2) (Icc 0 T ×ˢ univ) :=
    hv.continuousOn.sub hu.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) (2 * r))).exists_bound_of_continuousOn
    (hW.mono (prod_mono subset_rfl (subset_univ _)))
  have hint : ContinuousOn (fun τ => ∫ x, cutoffPow r x * ‖v τ x - u τ x‖ ^ 2) (Icc 0 T) := by
    apply continuousOn_of_dominated (bound := indicator (closedBall (0 : Space) (2 * r)) (fun _ => C ^ 2))
    · intro τ hτ
      exact ((contDiff_cutoffPow hr).continuous.mul
        (((contDiff_slice hv hτ).continuous.sub
          (contDiff_slice hu hτ).continuous).norm.pow 2)).aestronglyMeasurable
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

private theorem hasDerivAt_energy_of_smooth {T : ℝ} {u v : ℝ → Space → Space}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ)) {r : ℝ} (hr : 0 < r) {t : ℝ}
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
    (hv.continuousOn.sub hu.continuousOn).mono
      (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hD : ContinuousOn (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) -
        fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) z (1, 0)) (Ioo 0 T ×ˢ univ) :=
    (continuousOn_fderiv_slice_time hv).sub
      (continuousOn_fderiv_slice_time hu)
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
        (((contDiff_slice hv (hsub' hτ)).continuous.sub
          (contDiff_slice hu (hsub' hτ)).continuous).norm.pow 2)).aestronglyMeasurable)
    (integrable_cutoffPow_mul hr
        (((contDiff_slice hv (Ioo_subset_Icc_self ht)).continuous.sub
          (contDiff_slice hu (Ioo_subset_Icc_self ht)).continuous).norm.pow 2))
    (by
      have hc : Continuous (fun x : Space =>
          fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (t, x) (1, 0) -
            fderiv ℝ (fun z : ℝ × Space => u z.1 z.2) (t, x) (1, 0)) :=
        hD.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
      exact ((contDiff_cutoffPow hr).continuous.mul (continuous_const.mul
        ((((contDiff_slice hv (Ioo_subset_Icc_self ht)).continuous.sub
          (contDiff_slice hu (Ioo_subset_Icc_self ht)).continuous)).inner hc))).aestronglyMeasurable)
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
      (((hasDerivAt_slice_time hv (hsub hτ) x).sub
        (hasDerivAt_slice_time hu (hsub hτ) x)).norm_sq).const_mul (cutoffPow r x))
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
    rw [(hasDerivAt_slice_time hv ht x).deriv,
      (hasDerivAt_slice_time hu ht x).deriv]
    ring
  rw [hfun, ← hval]
  exact key.2.const_mul (1 / 2)

end Breakdown.FracInternal.SpaceEnergy

namespace Breakdown

open Internal.CutoffEnergy FracInternal.SpaceEnergy

theorem forcedLocalEnergy : ForcedLocalEnergyStatement := by
  intro T u v p q F G hu hv r hr
  refine ⟨continuousOn_energy_of_smooth hu.smooth_velocity hv.smooth_velocity hr, fun t ht => ?_⟩
  have key := hasDerivAt_energy_of_smooth hu.smooth_velocity hv.smooth_velocity hr ht
  convert key using 1
  have hVs : ContDiff ℝ ∞ (v t) := contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)
  have hUs : ContDiff ℝ ∞ (u t) := contDiff_slice hu.smooth_velocity (Ioo_subset_Icc_self ht)
  have hQs : ContDiff ℝ ∞ (q t) := contDiff_slice hv.smooth_pressure (Ioo_subset_Icc_self ht)
  have hPs : ContDiff ℝ ∞ (p t) := contDiff_slice hu.smooth_pressure (Ioo_subset_Icc_self ht)
  have hGs : ContDiff ℝ ∞ (G t) := hv.force_smooth t ht
  have hFs : ContDiff ℝ ∞ (F t) := hu.force_smooth t ht
  have hWs : ContDiff ℝ ∞ (v t - u t) := hVs.sub hUs
  have hφ := contDiff_cutoffPow hr
  have hφc := hasCompactSupport_cutoffPow hr
  have hpt : ∀ x, cutoffPow r x * inner ℝ (v t x - u t x)
      (deriv (fun τ => v τ x) t - deriv (fun τ => u τ x) t) =
      -(cutoffPow r x * inner ℝ (v t x - u t x) (G t x - F t x))
      - cutoffPow r x * inner ℝ (v t x - u t x) (gradientAt (q t) x - gradientAt (p t) x)
      - cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (v t - u t) x (v t x))
      - cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (u t) x (v t x - u t x)) := by
    intro x
    have e1 := hv.momentum t ht x
    have e2 := hu.momentum t ht x
    have hf : fderiv ℝ (v t - u t) x = fderiv ℝ (v t) x - fderiv ℝ (u t) x :=
      fderiv_sub (hVs.differentiable (by simp) x) (hUs.differentiable (by simp) x)
    simp only [advectionAt] at e1 e2
    rw [hf, eq_sub_of_add_eq (eq_sub_of_add_eq e1), eq_sub_of_add_eq (eq_sub_of_add_eq e2),
      sub_apply, map_sub]
    simp only [inner_sub_right, inner_neg_right]
    ring
  have hcW : Continuous (fun x => v t x - u t x) := hVs.continuous.sub hUs.continuous
  have hcG : ∀ f : Space → ℝ, ContDiff ℝ ∞ f → Continuous (gradientAt f) := by
    intro f hf
    unfold gradientAt
    exact continuous_finsetSum _ fun i _ =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hcDW : Continuous (fun x => fderiv ℝ (v t - u t) x (v t x)) :=
    (hWs.continuous_fderiv (by simp)).clm_apply hVs.continuous
  have hcDU : Continuous (fun x => fderiv ℝ (u t) x (v t x - u t x)) :=
    (hUs.continuous_fderiv (by simp)).clm_apply hcW
  have iA : Integrable (fun x => cutoffPow r x * inner ℝ (v t x - u t x) (G t x - F t x)) :=
    integrable_cutoffPow_mul hr (hcW.inner (hGs.continuous.sub hFs.continuous))
  have iB : Integrable (fun x => cutoffPow r x * inner ℝ (v t x - u t x)
      (gradientAt (q t) x - gradientAt (p t) x)) :=
    integrable_cutoffPow_mul hr (hcW.inner ((hcG _ hQs).sub (hcG _ hPs)))
  have iC := integrable_cutoffPow_mul hr (hcW.inner hcDW)
  have iD := integrable_cutoffPow_mul hr (hcW.inner hcDU)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub, integral_sub, integral_sub, integral_neg]
  all_goals first | exact iA.neg | exact iB | exact iC | exact iD | exact iA.neg.sub iB | exact (iA.neg.sub iB).sub iC | skip
  have hC := integral_mul_inner_fderiv_transport hφ hφc hVs
    (hv.incompressible t (Ioo_subset_Icc_self ht)) hWs
  simp only [Pi.sub_apply] at hC
  have hB : (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x)
      (cutoffPow r x • (v t x - u t x))) =
      ∫ x, cutoffPow r x * inner ℝ (v t x - u t x) (gradientAt (q t) x - gradientAt (p t) x) := by
    congr 1
    funext x
    rw [inner_smul_right, real_inner_comm]
  rw [hC, hB]
  ring

end Breakdown
