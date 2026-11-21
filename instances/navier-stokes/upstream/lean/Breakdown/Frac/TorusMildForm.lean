import Breakdown.Frac.StTorusReduce
import Breakdown.Torus.VarConst
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.Advection
import Breakdown.Torus.TimeCoef

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.FracMild

open Internal.Mild

variable {α : ℝ}

theorem fracHeat_tendsto (hH : FracTorusHeatAlgebra α) {ι : Type*} {l : Filter ι} {σ : ι → ℝ}
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

theorem fracKernel_eq_heat (hK : FracTorusKernelAlgebra α) {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ)
    (x y : V) : fracTorusKernel α τ x y = fracTorusHeat α (τ - σ) (fracTorusKernel α σ x y) := by
  rw [hK.2.2.2 (τ - σ) σ (sub_nonneg.2 h) hσ, sub_add_cancel]

theorem fracKernel_tendsto (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
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
  have hH' := fracHeat_tendsto hH (hτ.sub_const (τ₀ / 2)) hB
  have hev : ∀ᶠ a in l, τ₀ / 2 ≤ τ a := hτ.eventually (le_mem_nhds (half_lt_self h0))
  rw [fracKernel_eq_heat hK hσ (half_le_self h0.le) x₀ y₀]
  exact hH'.congr' (hev.mono fun a ha => (fracKernel_eq_heat hK hσ ha (x a) (y a)).symm)

theorem fracKernel_opNorm_anti (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
    {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) : ‖fracTorusKernel α τ‖ ≤ ‖fracTorusKernel α σ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _) fun x y => ?_
  rw [fracKernel_eq_heat hK hσ h x y]
  calc ‖fracTorusHeat α (τ - σ) (fracTorusKernel α σ x y)‖
        ≤ ‖fracTorusHeat α (τ - σ)‖ * ‖fracTorusKernel α σ x y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖fracTorusKernel α σ x y‖ := by gcongr; exact hH.2.2.2.1 _
    _ ≤ ‖fracTorusKernel α σ‖ * ‖x‖ * ‖y‖ := by
        rw [one_mul]; exact ContinuousLinearMap.le_opNorm₂ _ _ _

theorem fracKernel_norm_le (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
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
      have h2 := fracKernel_opNorm_anti hH hK one_pos h.le
      linarith
  calc ‖fracTorusKernel α τ x y‖ ≤ ‖fracTorusKernel α τ‖ * ‖x‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (C * τ ^ (-(3 / (4 * α))) + C) * ‖x‖ * ‖y‖ := by gcongr

theorem fracIntegrable_kernel (h1 : 1 < α) (hH : FracTorusHeatAlgebra α)
    (hK : FracTorusKernelAlgebra α) (hS : FracTorusKernelSharpBound α) {U : ℝ → V} {t : ℝ}
    (ht : 0 ≤ t) (hU : ContinuousOn U (Icc 0 t)) :
    IntervalIntegrable (fun s => fracTorusKernel α (t - s) (U s) (U s)) volume 0 t := by
  obtain ⟨C, hC, hb⟩ := fracKernel_norm_le hH hK hS
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  have hr : -1 < -(3 / (4 * α)) := by
    have : 3 / (4 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(3 / (4 * α))) + C) * M * M) (Ioo 0 t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / (4 * α)))) volume 0 t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
        (r := -(3 / (4 * α))) hr).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume 0 t := intervalIntegrable_const
    have h2 := (((h1.const_mul C).add h0).mul_const M).mul_const M
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).1 h2
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable_of_isSeparable (fun s hs => ?_) measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace _)
    have hUs : ContinuousWithinAt U (Ioo 0 t) s :=
      (hU s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    exact fracKernel_tendsto hH hK (sub_pos.2 hs.2)
      (((continuous_const.sub continuous_id).tendsto s).mono_left nhdsWithin_le_nhds) hUs hUs
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hu := hM s (Ioo_subset_Icc_self hs)
    have hA : 0 ≤ C * (t - s) ^ (-(3 / (4 * α))) + C :=
      add_nonneg (mul_nonneg hC.le (rpow_nonneg (sub_pos.2 hs.2).le _)) hC.le
    calc ‖fracTorusKernel α (t - s) (U s) (U s)‖
        ≤ (C * (t - s) ^ (-(3 / (4 * α))) + C) * ‖U s‖ * ‖U s‖ := hb _ (sub_pos.2 hs.2) _ _
      _ ≤ (C * (t - s) ^ (-(3 / (4 * α))) + C) * M * M := by gcongr

theorem fracDivergence_nonneg {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (h : IsFractionalSolution α 1 u₀ u p) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    divergenceAt (u t) x = 0 := by
  set S : Set (ℝ × Space) := Ici 0 ×ˢ univ
  set F : ℝ × Space → Space := fun z => u z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ∀ τ, 0 ≤ τ → HasFDerivAt (u τ)
      ((fderivWithin ℝ F S (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    intro τ hτ
    have h1 : HasFDerivWithinAt F (fderivWithin ℝ F S (τ, x)) S (τ, x) :=
      ((h.smooth_velocity.differentiableOn (by simp)) (τ, x) ⟨hτ, trivial⟩).hasFDerivWithinAt
    have h2 := h1.comp x (hasFDerivAt_prodMk_right τ x).hasFDerivWithinAt (s := univ)
      (fun _ _ => ⟨hτ, trivial⟩)
    exact hasFDerivWithinAt_univ.1 h2
  set G : ℝ → ℝ := fun τ => ∑ i, (fderivWithin ℝ F S (τ, x) (0, unitVector i)) i
  have hG : ∀ τ, 0 ≤ τ → divergenceAt (u τ) x = G τ := by
    intro τ hτ
    simp only [divergenceAt, (hD τ hτ).fderiv, G]
    rfl
  have hc : ContinuousOn G (Ici 0) := by
    have h1 : ContinuousOn (fun τ : ℝ => fderivWithin ℝ F S (τ, x)) (Ici 0) :=
      (h.smooth_velocity.continuousOn_fderivWithin hS (by simp)).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => ⟨hτ, trivial⟩)
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (PiLp.continuous_apply 2 _ i).comp_continuousOn (h1.clm_apply continuousOn_const)
  have hG0 : G 0 = 0 := by
    have h1 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) := (hc 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
    have h2 : Tendsto G (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun τ hτ => by
        rw [← hG τ (le_of_lt hτ)]
        exact (h.incompressible τ hτ x).symm)
    exact tendsto_nhds_unique h1 h2
  rcases ht.lt_or_eq with h' | h'
  · exact h.incompressible t h' x
  · subst h'
    rw [hG 0 le_rfl, hG0]

theorem coefField_neg (f : Space → Space) (k : Lattice) :
    freqTrCoef (fun x => -f x) k = -freqTrCoef f k := by
  unfold freqTrCoef
  rw [← integral_neg]
  congr 1
  funext x
  rw [show complexify (-f x) = -complexify (f x) by ext i; simp [complexify], smul_neg]

theorem continuous_timeDeriv {u : ℝ → Space → Space}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ici 0 ×ˢ univ)) {τ : ℝ} (hτ : 0 < τ) :
    Continuous (fun x => deriv (fun σ => u σ x) τ) := by
  have hDc : ContinuousOn (fun z : ℝ × Space =>
      fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2) (Ici 0 ×ˢ univ) z (1, 0)) (Ici 0 ×ˢ univ) :=
    ((hu.fderivWithin TimeCoef.Internal.uniqueDiffOn_halfSpace
      TimeCoef.Internal.infty_add_one_le).clm_apply contDiffOn_const).continuousOn
  have e : (fun x => deriv (fun σ => u σ x) τ) = fun x =>
      fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2) (Ici 0 ×ˢ univ) (τ, x) (1, 0) :=
    funext fun x => (TimeCoef.Internal.hasDerivAt_time (g := fun z : ℝ × Space => u z.1 z.2)
      hu hτ x).deriv
  rw [e]
  exact TimeCoef.Internal.continuous_slice hDc hτ.le

theorem fracMode_deriv (hC : CoefFractional α) (hF : FreqTrSeriesSpec) (hG : CoefGradient)
    (hA : CoefAdvection) (hT : CoefTimeDeriv)
    {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsFractionalSolution α 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    (hp : ∀ t ≥ 0, IsPeriodic (p t)) (hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0)
    (k : Lattice) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun σ => freqTrCoef (u σ) k)
      ((-((2 * π * ‖freq k‖) ^ (2 * α))) • freqTrCoef (u τ) k
        - divFree k (advCoef (toV (u τ)) (toV (u τ)) k)) τ := by
  have hφ : ContDiff ℝ ∞ (u τ) := contDiff_slice h.smooth_velocity hτ.le
  have hq : ContDiff ℝ ∞ (p τ) := contDiff_slice h.smooth_pressure hτ.le
  have hd := (hT u h.smooth_velocity hu k).2 τ hτ
  have hmom : ∀ x, deriv (fun σ => u σ x) τ + advectionAt (u τ) x +
      fractionalPowerAt α (u τ) x = -gradientAt (p τ) x := by
    intro x
    have := h.momentum τ hτ x
    rwa [one_smul] at this
  have hga : Continuous (fun x => -gradientAt (p τ) x - advectionAt (u τ) x) :=
    (continuous_gradientAt hq).neg.sub (continuous_advectionAt hφ)
  have hfrac : fractionalPowerAt α (u τ) =
      fun x => (-gradientAt (p τ) x - advectionAt (u τ) x) - deriv (fun σ => u σ x) τ := by
    funext x
    rw [← hmom x]
    abel
  have hfc : Continuous (fractionalPowerAt α (u τ)) := by
    rw [hfrac]
    exact hga.sub (continuous_timeDeriv h.smooth_velocity hτ)
  have hm : (fun x => deriv (fun σ => u σ x) τ) =
      fun x => (-gradientAt (p τ) x - advectionAt (u τ) x) - fractionalPowerAt α (u τ) x := by
    funext x
    rw [← hmom x]
    abel
  have hgn : Continuous (fun x => -gradientAt (p τ) x) := (continuous_gradientAt hq).neg
  rw [hm, freqTrCoef_sub hga hfc,
    freqTrCoef_sub hgn (continuous_advectionAt hφ),
    coefField_neg (gradientAt (p τ)), hG _ (hq.of_le ENat.LEInfty.out) (hp τ hτ.le),
    hA _ hφ (hu τ hτ.le) (h.incompressible τ hτ), hC _ hφ (hu τ hτ.le)] at hd
  have hfix : ∀ σ, 0 ≤ σ → divFree k (freqTrCoef (u σ) k) = freqTrCoef (u σ) k := by
    intro σ hσ
    rw [← (hF _ (contDiff_slice h.smooth_velocity hσ) (hu σ hσ) (hdiv σ hσ)).1 k, divFree_coeff]
  set LR : Coef →L[ℝ] Coef := (divFreeL k).restrictScalars ℝ with hLR
  have hL' := LR.hasFDerivAt.comp_hasDerivAt τ hd
  have hev : (fun σ => freqTrCoef (u σ) k) =ᶠ[𝓝 τ] (LR ∘ fun σ => freqTrCoef (u σ) k) := by
    filter_upwards [Ioi_mem_nhds hτ] with σ hσ
    exact (hfix σ (le_of_lt hσ)).symm
  refine (hL'.congr_of_eventuallyEq hev).congr_deriv ?_
  have e2 : LR ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0 := by
    show divFreeL k ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0
    rw [map_smul, divFreeL_apply, divFree_latVec, smul_zero]
  rw [map_sub, map_sub, map_neg, e2, neg_zero, zero_sub, map_smul]
  show -divFree k _ - _ • divFree k _ = _
  rw [hfix τ hτ.le, neg_smul]
  abel

theorem fracMode_identity (hK : FracTorusKernelAlgebra α)
    (hC : CoefFractional α) (hF : FreqTrSeriesSpec) (hG : CoefGradient)
    (hA : CoefAdvection) (hT : CoefTimeDeriv)
    {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsFractionalSolution α 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    (hp : ∀ t ≥ 0, IsPeriodic (p t)) (hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0)
    (hUc : ContinuousOn (fun t => toV (u t)) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) (k : Lattice) :
    coeff (toV (u t)) k = fracLatticeFactor α t k • coeff (toV (u 0)) k +
      ∫ s in (0 : ℝ)..t, coeff (fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) k := by
  have hcU : ∀ s, 0 ≤ s → coeff (toV (u s)) k = freqTrCoef (u s) k := fun s hs =>
    (hF _ (contDiff_slice h.smooth_velocity hs) (hu s hs) (hdiv s hs)).1 k
  have hK1 : ∀ τ, 0 < τ → ∀ a b : V, coeff (fracTorusKernel α τ a b) k =
      (-(1 / 2) * fracLatticeFactor α τ k) • divFree k (advCoef a b k + advCoef b a k) := by
    intro τ hτ a b
    rw [hK.1, fracTorusKernelCoef, if_pos hτ]
  have hpos : 0 < fracLatticeFactor α 1 k := Real.exp_pos _
  have hne : fracLatticeFactor α 1 k ≠ 0 := hpos.ne'
  have hB : ∀ s, divFree k (advCoef (toV (u s)) (toV (u s)) k) =
      (-(fracLatticeFactor α 1 k)⁻¹) • coeff (fracTorusKernel α 1 (toV (u s)) (toV (u s))) k := by
    intro s
    rw [hK1 1 one_pos, divFree_add, ← two_smul ℝ (divFree k _), smul_smul, smul_smul,
      show -(fracLatticeFactor α 1 k)⁻¹ * (-(1 / 2) * fracLatticeFactor α 1 k) * 2 = 1 by
        field_simp, one_smul]
  have hUt : ContinuousOn (fun s => toV (u s)) (Icc 0 t) := hUc.mono Icc_subset_Ici_self
  have hBc : ContinuousOn (fun s => divFree k (advCoef (toV (u s)) (toV (u s)) k)) (Icc 0 t) := by
    simp only [hB]
    exact ((coeffL k).continuous.comp_continuousOn
      (((fracTorusKernel α 1).continuous.comp_continuousOn hUt).clm_apply hUt)).const_smul
        (-(fracLatticeFactor α 1 k)⁻¹)
  have hcc : ContinuousOn (fun s => freqTrCoef (u s) k) (Icc 0 t) :=
    (hT u h.smooth_velocity hu k).1.mono Icc_subset_Ici_self
  have hv := variation_of_constants ht hcc hBc
    (fun s hs => fracMode_deriv hC hF hG hA hT h hu hp hdiv k hs.1)
  beta_reduce at hv
  have hh : fracLatticeFactor α t k = Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * t)) := by
    simp only [fracLatticeFactor, max_eq_left ht]
  rw [hcU t ht, hcU 0 le_rfl, hv, hh]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne' : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hne'] with s hs hmem
  rw [uIoc_of_le ht] at hmem
  have hst : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hmem.2 hs)
  rw [hK1 _ hst, divFree_add, ← two_smul ℝ (divFree k _), smul_smul, fracLatticeFactor,
    max_eq_left hst.le]
  congr 1
  ring

end Internal.FracMild

open Internal.Mild Internal.FracMild in
theorem fracTorusSmoothIsMild_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4)
    (hH : FracTorusHeatAlgebra α) (hK : FracTorusKernelAlgebra α)
    (hS : FracTorusKernelSharpBound α) (hC : CoefFractional α) : FracTorusSmoothIsMild α := by
  have hF : FreqTrSeriesSpec := freqTrSeriesSpec coefDeriv
  have hA : CoefAdvection := coefAdvection coefDeriv hF
  intro u₀ u p h hu hp T _
  have hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0 := fun t ht x =>
    fracDivergence_nonneg h t ht x
  have hUc : ContinuousOn (fun t => toV (u t)) (Ici 0) :=
    toVContinuous coefDeriv hF u h.smooth_velocity hu hdiv
  refine ⟨hUc.mono Icc_subset_Ici_self, fun t ht => ?_⟩
  have hI : IntervalIntegrable (fun s => fracTorusKernel α (t - s) (toV (u s)) (toV (u s)))
      volume 0 t :=
    fracIntegrable_kernel (U := fun s => toV (u s)) h1 hH hK hS ht.1 (hUc.mono Icc_subset_Ici_self)
  refine ⟨hI, ?_⟩
  apply coeff_injective
  intro k
  have e : coeff (fracTorusHeat α (t - 0) (toV (u 0)) +
      ∫ s in (0 : ℝ)..t, fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) k =
      coeff (fracTorusHeat α t (toV (u 0))) k +
        ∫ s in (0 : ℝ)..t, coeff (fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) k := by
    rw [sub_zero, ← coeffL_apply, map_add, ← (coeffL k).intervalIntegral_comp_comm hI]
    rfl
  rw [e, hH.1]
  exact fracMode_identity hK hC hF coefGradient hA coefTimeDeriv h hu hp hdiv hUc ht.1 k

end Breakdown.Periodic
