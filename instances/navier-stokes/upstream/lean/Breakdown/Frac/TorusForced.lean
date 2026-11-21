import Breakdown.Frac.StTorusForce
import Breakdown.Torus.Forced
import Breakdown.Frac.TorusForcedModes

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusForced.Internal

open TimeCoef.Internal

theorem heat_tendsto {α : ℝ} (hH : FracTorusHeatAlgebra α) {ι : Type*} {l : Filter ι} {σ : ι → ℝ}
    {w : ι → V} {σ₀ : ℝ} {w₀ : V} (hσ : Tendsto σ l (𝓝 σ₀)) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a => fracTorusHeat α (σ a) (w a)) l (𝓝 (fracTorusHeat α σ₀ w₀)) := by
  have h1 : Tendsto (fun a => fracTorusHeat α (σ a) w₀) l (𝓝 (fracTorusHeat α σ₀ w₀)) :=
    ((hH.2.2.2.2.2 w₀).tendsto σ₀).comp hσ
  have h2 : Tendsto (fun a => fracTorusHeat α (σ a) (w a) - fracTorusHeat α (σ a) w₀) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 hw)
    rw [← map_sub]
    calc ‖fracTorusHeat α (σ a) (w a - w₀)‖ ≤ ‖fracTorusHeat α (σ a)‖ * ‖w a - w₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w a - w₀‖ := by gcongr; exact hH.2.2.2.1 _
      _ = ‖w a - w₀‖ := one_mul _
  simpa using h2.add h1

theorem heat_norm_apply_le {α : ℝ} (hH : FracTorusHeatAlgebra α) (t : ℝ) (w : V) :
    ‖fracTorusHeat α t w‖ ≤ ‖w‖ :=
  calc ‖fracTorusHeat α t w‖ ≤ ‖fracTorusHeat α t‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖w‖ := by gcongr; exact hH.2.2.2.1 _
    _ = ‖w‖ := one_mul _

theorem kernel_eq_heat {α : ℝ} (hK : FracTorusKernelAlgebra α) {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ)
    (x y : V) : fracTorusKernel α τ x y = fracTorusHeat α (τ - σ) (fracTorusKernel α σ x y) := by
  rw [hK.2.2.2 (τ - σ) σ (sub_nonneg.2 h) hσ, sub_add_cancel]

theorem kernel_tendsto {α : ℝ} (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
    {ι : Type*} {l : Filter ι} {τ : ι → ℝ} {x y : ι → V} {τ₀ : ℝ} {x₀ y₀ : V}
    (h0 : 0 < τ₀) (hτ : Tendsto τ l (𝓝 τ₀)) (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun a => fracTorusKernel α (τ a) (x a) (y a)) l (𝓝 (fracTorusKernel α τ₀ x₀ y₀)) := by
  have hσ : 0 < τ₀ / 2 := half_pos h0
  have hx' : Tendsto (fun a => fracTorusKernel α (τ₀ / 2) (x a)) l
      (𝓝 (fracTorusKernel α (τ₀ / 2) x₀)) :=
    ((fracTorusKernel α (τ₀ / 2)).continuous.tendsto x₀).comp hx
  have hB : Tendsto (fun a => fracTorusKernel α (τ₀ / 2) (x a) (y a)) l
      (𝓝 (fracTorusKernel α (τ₀ / 2) x₀ y₀)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := V)).continuous.tendsto
      (fracTorusKernel α (τ₀ / 2) x₀, y₀)).comp (hx'.prodMk_nhds hy)
  have hHt := heat_tendsto hH (hτ.sub_const (τ₀ / 2)) hB
  have hev : ∀ᶠ a in l, τ₀ / 2 ≤ τ a := hτ.eventually (le_mem_nhds (half_lt_self h0))
  rw [kernel_eq_heat hK hσ (half_le_self h0.le) x₀ y₀]
  exact hHt.congr' (hev.mono fun a ha => (kernel_eq_heat hK hσ ha (x a) (y a)).symm)

theorem kernel_opNorm_anti {α : ℝ} (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
    {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) : ‖fracTorusKernel α τ‖ ≤ ‖fracTorusKernel α σ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _) fun x y => ?_
  rw [kernel_eq_heat hK hσ h x y]
  exact (heat_norm_apply_le hH _ _).trans (ContinuousLinearMap.le_opNorm₂ _ _ _)

theorem kernel_norm_le {α : ℝ} (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
    (hS : FracTorusKernelSharpBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ x y : V,
      ‖fracTorusKernel α τ x y‖ ≤ (C * τ ^ (-(3 / (4 * α))) + C) * ‖x‖ * ‖y‖ := by
  obtain ⟨C, hC, hb⟩ := hS
  refine ⟨C, hC, fun τ hτ x y => ?_⟩
  have h3 : 0 ≤ C * τ ^ (-(3 / (4 * α))) := mul_nonneg hC.le (rpow_nonneg hτ.le _)
  have hop : ‖fracTorusKernel α τ‖ ≤ C * τ ^ (-(3 / (4 * α))) + C := by
    rcases le_or_gt τ 1 with h | h
    · linarith [hb τ hτ h]
    · have h1 := hb 1 one_pos le_rfl
      rw [one_rpow, mul_one] at h1
      have h2 := kernel_opNorm_anti hH hK one_pos h.le
      linarith
  calc ‖fracTorusKernel α τ x y‖ ≤ ‖fracTorusKernel α τ‖ * ‖x‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (C * τ ^ (-(3 / (4 * α))) + C) * ‖x‖ * ‖y‖ := by gcongr

theorem integrable_kernel {α : ℝ} (hα : 1 < α) (hH : FracTorusHeatAlgebra α)
    (hK : FracTorusKernelAlgebra α) (hS : FracTorusKernelSharpBound α) {U : ℝ → V} {a t : ℝ}
    (ht : a ≤ t) (hU : ContinuousOn U (Icc a t)) :
    IntervalIntegrable (fun s => fracTorusKernel α (t - s) (U s) (U s)) volume a t := by
  obtain ⟨C, hC, hb⟩ := kernel_norm_le hH hK hS
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  have hr : -1 < -(3 / (4 * α)) := by
    have : 3 / (4 * α) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    linarith
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(3 / (4 * α))) + C) * M * M) (Ioo a t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / (4 * α)))) volume a t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
        (r := -(3 / (4 * α))) hr).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume a t := intervalIntegrable_const
    have h2 := (((h1.const_mul C).add h0).mul_const M).mul_const M
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).1 h2
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable_of_isSeparable (fun s hs => ?_) measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace _)
    have hUs : ContinuousWithinAt U (Ioo a t) s :=
      (hU s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    exact kernel_tendsto hH hK (sub_pos.2 hs.2)
      (((continuous_const.sub continuous_id).tendsto s).mono_left nhdsWithin_le_nhds) hUs hUs
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hu := hM s (Ioo_subset_Icc_self hs)
    have hA : 0 ≤ C * (t - s) ^ (-(3 / (4 * α))) + C :=
      add_nonneg (mul_nonneg hC.le (rpow_nonneg (sub_pos.2 hs.2).le _)) hC.le
    calc ‖fracTorusKernel α (t - s) (U s) (U s)‖
        ≤ (C * (t - s) ^ (-(3 / (4 * α))) + C) * ‖U s‖ * ‖U s‖ := hb _ (sub_pos.2 hs.2) _ _
      _ ≤ (C * (t - s) ^ (-(3 / (4 * α))) + C) * M * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu hA) hu (norm_nonneg _)
            (mul_nonneg hA ((norm_nonneg _).trans hu))

theorem periodic_sub {G H : Space → Space} (hG : IsPeriodic G) (hH : IsPeriodic H) :
    IsPeriodic (fun x => G x - H x) := by
  intro i x
  show G (x + unitVector i) - H (x + unitVector i) = G x - H x
  rw [hG i x, hH i x]

theorem force_sub {α : ℝ} (hF : FracTorusForceAlgebra α) (τ : ℝ) {G H : Space → Space}
    (hG : Continuous G) (hH : Continuous H) :
    fracTorusForce α τ G - fracTorusForce α τ H = fracTorusForce α τ (fun x => G x - H x) := by
  apply coeff_injective
  intro k
  rw [← Internal.Mild.coeffL_apply, map_sub, Internal.Mild.coeffL_apply, Internal.Mild.coeffL_apply,
    hF.1, hF.1, hF.1]
  unfold fracTorusForceCoef
  split_ifs
  · have e := (Internal.Mild.divFreeL k).map_sub (freqTrCoef G k) (freqTrCoef H k)
    simp only [Internal.Mild.divFreeL_apply] at e
    rw [Internal.Mild.freqTrCoef_sub hG hH k, e, smul_sub]
  · exact sub_zero 0

theorem norm_force_le {α : ℝ} (hH : FracTorusHeatAlgebra α) (hF : FracTorusForceAlgebra α)
    (hFS : FracForceSmoothing α) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Space → Space, Continuous G → IsPeriodic G →
      ‖fracTorusForce α τ G‖ ≤ (C * τ ^ (-(1 / (2 * α))) + C) * Real.sqrt (∫ x in cell, ‖G x‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := hFS
  refine ⟨C, hC0, fun τ hτ G hG hp => ?_⟩
  have hS := Real.sqrt_nonneg (∫ x in cell, ‖G x‖ ^ 2)
  have hT : 0 ≤ C * τ ^ (-(1 / (2 * α))) := mul_nonneg hC0.le (rpow_nonneg hτ.le _)
  rcases le_or_gt τ 1 with h1 | h1
  · have := hC τ hτ h1 G hG hp
    nlinarith
  · rw [hF.2.1 1 τ one_pos h1.le]
    have h2 := hC 1 one_pos le_rfl G hG hp
    rw [one_rpow, mul_one] at h2
    have h3 := heat_norm_apply_le hH (τ - 1) (fracTorusForce α 1 G)
    nlinarith

theorem tendsto_sqDist {F : ℝ → Space → Space} {a b : ℝ}
    (hFc : ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (Icc a b ×ˢ univ)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc a b) :
    Tendsto (fun s => Real.sqrt (∫ x in cell, ‖F s x - F s₀ x‖ ^ 2)) (𝓝[Icc a b] s₀) (𝓝 0) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hFc.mono (prod_mono (subset_refl (Icc a b)) (subset_univ _)))
  have hg : ContinuousOn (fun s => ∫ x in cell, ‖F s x - F s₀ x‖ ^ 2) (Icc a b) := by
    refine continuousOn_of_dominated (bound := fun _ => (M + M) ^ 2) (fun s hs => ?_)
      (fun s hs => ?_) (integrable_const _) (Eventually.of_forall fun x => ?_)
    · exact (((Forced.Internal.sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc hs).sub
        (Forced.Internal.sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc hs₀)).norm.pow
          2).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_cell fun x hx => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      exact add_le_add (hM (s, x) ⟨hs, hx⟩) (hM (s₀, x) ⟨hs₀, hx⟩)
    · have hc : ContinuousOn (fun s => F s x) (Icc a b) :=
        hFc.comp (Continuous.continuousOn (by fun_prop))
          (show MapsTo (fun s : ℝ => (s, x)) (Icc a b) (Icc a b ×ˢ univ) from
            fun s hs => ⟨hs, mem_univ x⟩)
      exact (hc.sub continuousOn_const).norm.pow 2
  have h0 := hg s₀ hs₀
  have e : (∫ x in cell, ‖F s₀ x - F s₀ x‖ ^ 2) = 0 := by simp
  rw [ContinuousWithinAt, e] at h0
  have := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at this
  exact this

theorem continuousOn_force {α : ℝ} (hH : FracTorusHeatAlgebra α) (hF : FracTorusForceAlgebra α)
    (hFS : FracForceSmoothing α) {F : ℝ → Space → Space} {a b t : ℝ} (htb : t ≤ b)
    (hFc : ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (Icc a b ×ˢ univ))
    (hFp : ∀ s ∈ Icc a b, IsPeriodic (F s)) :
    ContinuousOn (fun s => fracTorusForce α (t - s) (F s)) (Ioo a t) := by
  obtain ⟨C, hC0, hC⟩ := norm_force_le hH hF hFS
  intro s₀ hs₀
  have hsub : Ioo a t ⊆ Icc a b := fun s hs => ⟨hs.1.le, hs.2.le.trans htb⟩
  have hs₀' := hsub hs₀
  have hpos : 0 < t - s₀ := sub_pos.2 hs₀.2
  have hcF : ∀ s ∈ Icc a b, Continuous (F s) := fun s hs =>
    Forced.Internal.sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc hs
  have h2 : Tendsto (fun s => fracTorusForce α (t - s) (F s₀)) (𝓝[Ioo a t] s₀)
      (𝓝 (fracTorusForce α (t - s₀) (F s₀))) := by
    have hc : ContinuousAt (fun τ => fracTorusForce α τ (F s₀)) (t - s₀) :=
      ((hF.2.2 (F s₀)) (t - s₀) hpos).continuousAt (Ioi_mem_nhds hpos)
    have hc2 : ContinuousAt (fun s => fracTorusForce α (t - s) (F s₀)) s₀ :=
      hc.comp (f := fun s => t - s) (continuous_const.sub continuous_id).continuousAt
    exact hc2.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s => fracTorusForce α (t - s) (F s) - fracTorusForce α (t - s) (F s₀))
      (𝓝[Ioo a t] s₀) (𝓝 0) := by
    have hq : ContinuousAt (fun s => C * (t - s) ^ (-(1 / (2 * α))) + C) s₀ :=
      (((continuous_const.sub continuous_id).continuousAt.rpow_const (Or.inl hpos.ne')).const_mul
        C).add continuousAt_const
    have hb := (hq.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((tendsto_sqDist hFc hs₀').mono_left (nhdsWithin_mono _ hsub))
    rw [mul_zero] at hb
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hb
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [force_sub hF _ (hcF s (hsub hs)) (hcF s₀ hs₀')]
    exact hC _ (sub_pos.2 hs.2) _ ((hcF s (hsub hs)).sub (hcF s₀ hs₀'))
      (periodic_sub (hFp s (hsub hs)) (hFp s₀ hs₀'))
  have h3 := h1.add h2
  simp only [sub_add_cancel, zero_add] at h3
  exact h3

theorem integrable_force {α : ℝ} (hα : 1 < α) (hH : FracTorusHeatAlgebra α)
    (hF : FracTorusForceAlgebra α) (hFS : FracForceSmoothing α) {F : ℝ → Space → Space} {a b t : ℝ}
    (ht : t ∈ Icc a b) (hFc : ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (Icc a b ×ˢ univ))
    (hFp : ∀ s ∈ Icc a b, IsPeriodic (F s)) :
    IntervalIntegrable (fun s => fracTorusForce α (t - s) (F s)) volume a t := by
  obtain ⟨C, hC0, hC⟩ := norm_force_le hH hF hFS
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hFc.mono (prod_mono (subset_refl (Icc a b)) (subset_univ _)))
  set R := Real.sqrt (M ^ 2 * volume.real cell)
  have hsub : Ioo a t ⊆ Icc a b := fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hR : ∀ s ∈ Icc a b, Real.sqrt (∫ x in cell, ‖F s x‖ ^ 2) ≤ R := by
    intro s hs
    refine Real.sqrt_le_sqrt ?_
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell)
      (f := fun x => ‖F s x‖ ^ 2) (C := M ^ 2) isCompact_cell.measure_lt_top (fun x hx => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM (s, x) ⟨hs, hx⟩) 2)
    exact (Real.le_norm_self _).trans h
  have hr : -1 < -(1 / (2 * α)) := by
    have : 1 / (2 * α) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    linarith
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(1 / (2 * α))) + C) * R) (Ioo a t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / (2 * α)))) volume a t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
        (r := -(1 / (2 * α))) hr).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume a t := intervalIntegrable_const
    have h2 := ((h1.const_mul C).add h0).mul_const R
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1 h2
  refine Integrable.mono' hg ?_ ?_
  · exact (continuousOn_force hH hF hFS ht.2 hFc hFp).aestronglyMeasurable_of_isSeparable
      measurableSet_Ioo (TopologicalSpace.IsSeparable.of_separableSpace _)
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hst : 0 < t - s := sub_pos.2 hs.2
    have hA : 0 ≤ C * (t - s) ^ (-(1 / (2 * α))) + C :=
      add_nonneg (mul_nonneg hC0.le (rpow_nonneg hst.le _)) hC0.le
    calc ‖fracTorusForce α (t - s) (F s)‖
        ≤ (C * (t - s) ^ (-(1 / (2 * α))) + C) * Real.sqrt (∫ x in cell, ‖F s x‖ ^ 2) :=
          hC _ hst _ (Forced.Internal.sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc
            (hsub hs)) (hFp s (hsub hs))
      _ ≤ (C * (t - s) ^ (-(1 / (2 * α))) + C) * R := mul_le_mul_of_nonneg_left (hR s (hsub hs)) hA

end FracTorusForced.Internal

open FracTorusForced.Internal in
theorem fracForcedPeriodicIsMild_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4)
    (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α) (hS : FracTorusKernelSharpBound α)
    (hC : CoefFractional α) (hF : FracTorusForceAlgebra α) (hFS : FracForceSmoothing α) :
    FracForcedPeriodicIsMild α := by
  intro u p F a b hab h
  have hUc : ContinuousOn (fun t => toV (u t)) (Icc a b) :=
    Forced.Internal.continuousOn_toV hab h.1 (fun t ht => (h.2.2.2.1 t ht).1) h.2.2.2.2.1
  refine ⟨hUc, fun t ht => ?_⟩
  have hI : IntervalIntegrable (fun s => fracTorusKernel α (t - s) (toV (u s)) (toV (u s)))
      volume a t :=
    integrable_kernel (U := fun s => toV (u s)) h1 hH hK hS ht.1
      (hUc.mono (Icc_subset_Icc_right ht.2))
  have hJ : IntervalIntegrable (fun s => fracTorusForce α (t - s) (F s)) volume a t :=
    integrable_force h1 hH hF hFS ht h.2.2.1 (fun s hs => (h.2.2.2.1 s hs).2.2)
  refine ⟨hI, hJ, ?_⟩
  apply coeff_injective
  intro k
  have e : coeff (fracTorusHeat α (t - a) (toV (u a)) +
      (∫ s in a..t, fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) +
      ∫ s in a..t, fracTorusForce α (t - s) (F s)) k =
      coeff (fracTorusHeat α (t - a) (toV (u a))) k +
        (∫ s in a..t, coeff (fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) k) +
        ∫ s in a..t, coeff (fracTorusForce α (t - s) (F s)) k := by
    rw [← Internal.Mild.coeffL_apply, map_add, map_add,
      ← (Internal.Mild.coeffL k).intervalIntegral_comp_comm hI,
      ← (Internal.Mild.coeffL k).intervalIntegral_comp_comm hJ]
    rfl
  rw [e, hH.1]
  exact FracTorusForcedModes.Internal.mode_identity hK hC hF hab h hUc ht hI hJ k

end Breakdown.Periodic
