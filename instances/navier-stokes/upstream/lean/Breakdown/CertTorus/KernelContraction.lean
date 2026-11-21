import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

private theorem coord_continuous (m : Fin 3) : Continuous fun x : Space => x m :=
  (EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous

private theorem coord_differentiable (m : Fin 3) :
    Differentiable ℝ (fun x : Space => x m) :=
  (EuclideanSpace.proj m : Space →L[ℝ] ℝ).differentiable

private theorem heatKernel_continuous (τ : ℝ) : Continuous (heatKernel τ) := by
  unfold heatKernel
  fun_prop

private theorem ite_coord_continuous (a b m : Fin 3) :
    Continuous fun x : Space => if a = b then x m else 0 := by
  by_cases h : a = b
  · simpa [h] using coord_continuous m
  · simp [h]; exact continuous_const

private theorem heatKernelThird_continuous (i j k : Fin 3) (ρ : ℝ) :
    Continuous (heatKernelThird i j k ρ) := by
  have h1 := ite_coord_continuous j k i
  have h2 := ite_coord_continuous i k j
  have h3 := ite_coord_continuous i j k
  have hi := coord_continuous i
  have hj := coord_continuous j
  have hk := coord_continuous k
  have hG := heatKernel_continuous ρ
  unfold heatKernelThird
  fun_prop

private theorem heatKernelThird_measurable (i j k : Fin 3) :
    Measurable (fun p : ℝ × Space => heatKernelThird i j k p.1 p.2) := by
  have hc : ∀ m : Fin 3, Measurable fun p : ℝ × Space => p.2 m :=
    fun m => ((coord_continuous m).comp continuous_snd).measurable
  have hite : ∀ a b m : Fin 3, Measurable fun p : ℝ × Space => if a = b then p.2 m else 0 := by
    intro a b m
    by_cases h : a = b
    · simpa [h] using hc m
    · simp [h]
  have h1 := hite j k i
  have h2 := hite i k j
  have h3 := hite i j k
  have hi := hc i
  have hj := hc j
  have hk := hc k
  have hn : Measurable fun p : ℝ × Space => ‖p.2‖ := (continuous_norm.comp continuous_snd).measurable
  unfold heatKernelThird heatKernel
  fun_prop

private theorem fderiv_component {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3)
    (z v : Space) : fderiv ℝ (fun y => χ y i) z v = fderiv ℝ χ z v i := by
  have h : HasFDerivAt (fun y => χ y i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ χ z)) z :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp z
      ((hχ.differentiable (by simp)) z).hasFDerivAt
  rw [h.fderiv]
  rfl

private theorem component_differentiable {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3) :
    Differentiable ℝ (fun y => χ y i) := fun z =>
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp z
    ((hχ.differentiable (by simp)) z).hasFDerivAt).differentiableAt

private theorem component_continuous {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3) :
    Continuous (fun y => χ y i) :=
  (component_differentiable hχ i).continuous

private theorem component_compact {χ : Space → Space} (hc : HasCompactSupport χ) (i : Fin 3) :
    HasCompactSupport (fun y => χ y i) :=
  hc.comp_left (f := χ) (g := fun v : Space => v i) (by simp)

private theorem component_deriv_continuous {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3)
    (v : Space) : Continuous (fun z => fderiv ℝ (fun y => χ y i) z v) := by
  simp_rw [fderiv_component hχ i]
  exact (coord_continuous i).comp ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)

private theorem component_deriv_compact {χ : Space → Space} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (i : Fin 3) (v : Space) :
    HasCompactSupport (fun z => fderiv ℝ (fun y => χ y i) z v) := by
  simp_rw [fderiv_component hχ i]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun A : Space →L[ℝ] Space => A v i) (by simp)

private theorem integrable_mul_compact_left {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport a) : Integrable (fun z => a z * b z) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem integrable_mul_compact_right {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport b) : Integrable (fun z => a z * b z) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_left (f := a))

private theorem fderiv_comp_sub_apply {f : Space → ℝ} (x z v : Space)
    (hf : DifferentiableAt ℝ f (x - z)) :
    fderiv ℝ (fun y => f (x - y)) z v = -fderiv ℝ f (x - z) v := by
  have h : HasFDerivAt (fun y => f (x - y))
      ((fderiv ℝ f (x - z)).comp (-(ContinuousLinearMap.id ℝ Space))) z :=
    hf.hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  rw [h.fderiv]
  simp

private theorem third_pairing_zero (hHP : HeatKernelPartials) {χ : Space → Space}
    (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχd : ∀ y, divergenceAt χ y = 0)
    (j k : Fin 3) (x : Space) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z, ∑ i : Fin 3, heatKernelThird i j k ρ (x - z) * χ z i = 0 := by
  set H : Space → ℝ := fun z =>
    (z j * z k / (4 * ρ ^ 2) - (if j = k then 1 / (2 * ρ) else 0)) * heatKernel ρ z with hH
  have hHd : Differentiable ℝ H := by
    have h1 : Differentiable ℝ (heatKernel ρ) := fun w => (hHP ρ hρ w).1.differentiableAt
    have hj := coord_differentiable j
    have hk := coord_differentiable k
    rw [hH]
    fun_prop
  have hgc : Continuous fun z => H (x - z) := hHd.continuous.comp (continuous_const.sub continuous_id)
  have hTc : ∀ i : Fin 3, Continuous fun z => heatKernelThird i j k ρ (x - z) :=
    fun i => (heatKernelThird_continuous i j k ρ).comp (continuous_const.sub continuous_id)
  have hderiv : ∀ (i : Fin 3) (z : Space),
      fderiv ℝ (fun y => H (x - y)) z (unitVector i) = -heatKernelThird i j k ρ (x - z) := by
    intro i z
    rw [fderiv_comp_sub_apply x z _ (hHd (x - z))]
    exact congrArg Neg.neg ((hHP ρ hρ (x - z)).2 i j k)
  have hibp : ∀ i : Fin 3, ∫ z, heatKernelThird i j k ρ (x - z) * χ z i =
      ∫ z, fderiv ℝ (fun y => χ y i) z (unitVector i) * H (x - z) := by
    intro i
    have hfg' : Integrable (fun z => χ z i * fderiv ℝ (fun y => H (x - y)) z (unitVector i)) := by
      have e : (fun z => χ z i * fderiv ℝ (fun y => H (x - y)) z (unitVector i)) =
          fun z => χ z i * -heatKernelThird i j k ρ (x - z) := by
        funext z
        rw [hderiv]
      rw [e]
      exact integrable_mul_compact_left (component_continuous hχs i) (hTc i).neg
        (component_compact hχc i)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y => χ y i) (g := fun y => H (x - y)) (v := unitVector i)
      (integrable_mul_compact_left (component_deriv_continuous hχs i _) hgc
        (component_deriv_compact hχs hχc i _))
      hfg'
      (integrable_mul_compact_left (component_continuous hχs i) hgc (component_compact hχc i))
      (fun z _ => component_differentiable hχs i z)
      (fun z _ => (hHd.comp (differentiable_const x |>.sub differentiable_id)) z)
    have e2 : (fun z => χ z i * fderiv ℝ (fun y => H (x - y)) z (unitVector i)) =
        fun z => -(heatKernelThird i j k ρ (x - z) * χ z i) := by
      funext z
      rw [hderiv]
      ring
    rw [e2, integral_neg] at h
    exact neg_injective h
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z => heatKernelThird i j k ρ (x - z) * χ z i) :=
    fun i _ => integrable_mul_compact_right (hTc i) (component_continuous hχs i)
      (component_compact hχc i)
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z => fderiv ℝ (fun y => χ y i) z (unitVector i) * H (x - z)) :=
    fun i _ => integrable_mul_compact_left (component_deriv_continuous hχs i _) hgc
      (component_deriv_compact hχs hχc i _)
  rw [integral_finsetSum _ hint]
  simp_rw [hibp]
  rw [← integral_finsetSum _ hint2]
  have hzero : ∀ z, ∑ i : Fin 3, fderiv ℝ (fun y => χ y i) z (unitVector i) = 0 := by
    intro z
    simp only [fderiv_component hχs]
    exact hχd z
  simp [← Finset.sum_mul, hzero]

private theorem third_bound {C : ℝ} (hC0 : 0 ≤ C) {ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (w : Space)
    (h : |t| ≤ C / (‖w‖ + Real.sqrt ρ) ^ 6) : |t| ≤ C * ρ ^ (-3 : ℝ) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hle : Real.sqrt ρ ^ 6 ≤ (‖w‖ + Real.sqrt ρ) ^ 6 :=
    pow_le_pow_left₀ hs.le (le_add_of_nonneg_left (norm_nonneg w)) 6
  have h6 : Real.sqrt ρ ^ 6 = ρ ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hρ.le]
  have hr : ρ ^ (-3 : ℝ) = (ρ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hρ.le]
    norm_cast
  calc |t| ≤ C / (‖w‖ + Real.sqrt ρ) ^ 6 := h
    _ ≤ C / Real.sqrt ρ ^ 6 := div_le_div_of_nonneg_left hC0 (pow_pos hs 6) hle
    _ = C * ρ ^ (-3 : ℝ) := by rw [h6, hr, div_eq_mul_inv]

private theorem third_integral_part (hHB : HeatKernelBounds) (hHP : HeatKernelPartials) {τ : ℝ}
    (hτ : 0 < τ) {χ : Space → Space} (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχd : ∀ y, divergenceAt χ y = 0) (j k : Fin 3) (x : Space) :
    Integrable (fun z => ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i) ∧
      ∫ z, ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i = 0 := by
  obtain ⟨C, hC⟩ := hHB
  have hC0 : 0 ≤ C := by
    have h := (hC 1 one_pos 0).2.2 0 0 0
    have hpos : (0 : ℝ) < (‖(0 : Space)‖ + Real.sqrt 1) ^ 6 := by simp
    have h' := (le_div_iff₀ hpos).1 ((abs_nonneg _).trans h)
    simpa using h'
  have hbound : ∀ (i : Fin 3) (ρ : ℝ), ρ ∈ Ioi τ → ∀ w : Space,
      |heatKernelThird i j k ρ w| ≤ C * ρ ^ (-3 : ℝ) := by
    intro i ρ hρ w
    have hρ0 : 0 < ρ := hτ.trans hρ
    exact third_bound hC0 hρ0 w ((hC ρ hρ0 w).2.2 i j k)
  have hbint : IntegrableOn (fun ρ : ℝ => C * ρ ^ (-3 : ℝ)) (Ioi τ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hτ).const_mul C
  have hTint : ∀ (i : Fin 3) (w : Space),
      IntegrableOn (fun ρ => heatKernelThird i j k ρ w) (Ioi τ) := by
    intro i w
    refine Integrable.mono' hbint
      ((heatKernelThird_measurable i j k).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_)
    rw [Real.norm_eq_abs]
    exact hbound i ρ hρ w
  have hae : ∀ᵐ p ∂((volume : Measure Space).prod (volume.restrict (Ioi τ))), p.2 ∈ Ioi τ :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
  set ν : Measure ℝ := volume.restrict (Ioi τ) with hν
  set F : Space × ℝ → ℝ := fun p => ∑ i : Fin 3, heatKernelThird i j k p.2 (x - p.1) * χ p.1 i
    with hF
  have hFmeas : Measurable F := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((heatKernelThird_measurable i j k).comp
      (measurable_snd.prodMk (continuous_const.sub continuous_fst).measurable)).mul
      ((component_continuous hχs i).measurable.comp measurable_fst)
  set K : Space → ℝ := fun z => ∑ i : Fin 3, |χ z i| with hK
  have hKint : Integrable K := by
    have hKc : Continuous K := by
      rw [hK]
      exact continuous_finsetSum _ fun i _ => (component_continuous hχs i).abs
    refine hKc.integrable_of_hasCompactSupport ?_
    exact hχc.comp_left (f := χ) (g := fun v : Space => ∑ i : Fin 3, |v i|) (by simp)
  have hmaj : Integrable (fun p : Space × ℝ => K p.1 * (C * p.2 ^ (-3 : ℝ))) (volume.prod ν) :=
    hKint.mul_prod hbint
  have hFint : Integrable F (volume.prod ν) := by
    refine hmaj.mono' hFmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [hF]
    calc ‖∑ i : Fin 3, heatKernelThird i j k p.2 (x - p.1) * χ p.1 i‖
        ≤ ∑ i : Fin 3, ‖heatKernelThird i j k p.2 (x - p.1) * χ p.1 i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, C * p.2 ^ (-3 : ℝ) * |χ p.1 i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hbound i p.2 hp _) (abs_nonneg _)
      _ = K p.1 * (C * p.2 ^ (-3 : ℝ)) := by
          rw [hK, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hpt : ∀ z : Space, ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i =
      ∫ ρ, F (z, ρ) ∂ν := by
    intro z
    rw [hF, hν]
    show ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i =
      ∫ ρ in Ioi τ, ∑ i : Fin 3, heatKernelThird i j k ρ (x - z) * χ z i
    rw [integral_finsetSum _ fun i _ => (hTint i (x - z)).mul_const _]
    exact Finset.sum_congr rfl fun i _ => (integral_mul_const _ _).symm
  have hfun : (fun z => ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i) =
      fun z => ∫ ρ, F (z, ρ) ∂ν := funext hpt
  rw [hfun]
  refine ⟨hFint.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun z ρ => F (z, ρ)) hFint, hν]
  refine setIntegral_eq_zero_of_forall_eq_zero fun ρ hρ => ?_
  exact third_pairing_zero hHP hχs hχc hχd j k x (hτ.trans hρ)

private theorem gradient_part (hHP : HeatKernelPartials) {τ : ℝ} (hτ : 0 < τ) {χ : Space → Space}
    (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (j k : Fin 3) (x : Space) :
    ∫ z, -((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j =
      fderiv ℝ (heatConv τ χ) x (unitVector k) j := by
  have hGd : Differentiable ℝ (heatKernel τ) := fun w => (hHP τ hτ w).1.differentiableAt
  have hGc : Continuous (heatKernel τ) := heatKernel_continuous τ
  have hgc : Continuous fun z => heatKernel τ (x - z) := hGc.comp (continuous_const.sub continuous_id)
  have hGk : ∀ w : Space, fderiv ℝ (heatKernel τ) w (unitVector k) =
      -(w k / (2 * τ)) * heatKernel τ w := by
    intro w
    rw [(hHP τ hτ w).1.fderiv]
    simp [unitVector]
  have hderiv : ∀ z : Space, fderiv ℝ (fun y => heatKernel τ (x - y)) z (unitVector k) =
      -(-((x - z) k / (2 * τ)) * heatKernel τ (x - z)) := by
    intro z
    rw [fderiv_comp_sub_apply x z _ (hGd (x - z)), hGk]
  have hDc : Continuous fun z => -((x - z) k / (2 * τ)) * heatKernel τ (x - z) := by
    have hk := (coord_continuous k).comp (continuous_const.sub continuous_id : Continuous fun z : Space => x - z)
    have := hgc
    fun_prop
  have hstep1 : ∫ z, -((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j =
      ∫ z, fderiv ℝ (fun y => χ y j) z (unitVector k) * heatKernel τ (x - z) := by
    have e : (fun z => χ z j * fderiv ℝ (fun y => heatKernel τ (x - y)) z (unitVector k)) =
        fun z => -(-((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j) := by
      funext z
      rw [hderiv]
      ring
    have hfg' : Integrable (fun z => χ z j * fderiv ℝ (fun y => heatKernel τ (x - y)) z (unitVector k)) := by
      rw [e]
      exact (integrable_mul_compact_right hDc (component_continuous hχs j)
        (component_compact hχc j)).neg
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y => χ y j) (g := fun y => heatKernel τ (x - y)) (v := unitVector k)
      (integrable_mul_compact_left (component_deriv_continuous hχs j _) hgc
        (component_deriv_compact hχs hχc j _))
      hfg'
      (integrable_mul_compact_left (component_continuous hχs j) hgc (component_compact hχc j))
      (fun z _ => component_differentiable hχs j z)
      (fun z _ => (hGd.comp (differentiable_const x |>.sub differentiable_id)) z)
    rw [e, integral_neg] at h
    exact neg_injective h
  have hconv : heatConv τ χ = convolution (heatKernel τ) χ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y
    rw [convolution_lsmul_swap]
    rfl
  have hd := hχc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (hGc.locallyIntegrable (μ := volume)) (hχs.of_le (by simp)) x
  set L' := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).precompR Space with hL'
  have hfd : Continuous (fderiv ℝ χ) := hχs.continuous_fderiv (by simp)
  have hΦc : Continuous fun t => L' (heatKernel τ (x - t)) (fderiv ℝ χ t) :=
    L'.continuous₂.comp (hgc.prodMk hfd)
  have hΦs : HasCompactSupport fun t => L' (heatKernel τ (x - t)) (fderiv ℝ χ t) := by
    refine (hχc.fderiv (𝕜 := ℝ)).mono ?_
    intro t ht h0
    exact ht (by simp [h0])
  have hΦi := hΦc.integrable_of_hasCompactSupport (μ := volume) hΦs
  have hstep2 : fderiv ℝ (heatConv τ χ) x (unitVector k) j =
      ∫ t, heatKernel τ (x - t) * fderiv ℝ χ t (unitVector k) j := by
    rw [hconv, hd.fderiv, convolution_eq_swap, ContinuousLinearMap.integral_apply hΦi]
    have hψ : Integrable fun t => L' (heatKernel τ (x - t)) (fderiv ℝ χ t) (unitVector k) :=
      (ContinuousLinearMap.apply ℝ Space (unitVector k)).integrable_comp hΦi
    have := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).integral_comp_comm hψ
    refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
    simp [hL']
  rw [hstep1, hstep2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [fderiv_component hχs]
  ring

theorem kernelContraction_of_heat : HeatKernelBounds → HeatKernelPartials → KernelContraction := by
  intro hHB hHP τ hτ χ hχ j k x
  obtain ⟨hχs, hχc, hχd⟩ := hχ
  obtain ⟨hBint, hB0⟩ := third_integral_part hHB hHP hτ hχs hχc hχd j k x
  have hAint : Integrable (fun z => -((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j) := by
    have hk := (coord_continuous k).comp (continuous_const.sub continuous_id : Continuous fun z : Space => x - z)
    have hg := (heatKernel_continuous τ).comp (continuous_const.sub continuous_id : Continuous fun z : Space => x - z)
    exact integrable_mul_compact_right (by fun_prop) (component_continuous hχs j) (component_compact hχc j)
  have hpt : ∀ z : Space, ∑ i : Fin 3, lerayKernel i j k τ (x - z) * χ z i =
      -((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j +
        ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i := by
    intro z
    simp only [lerayKernel, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hfun : (fun z => ∑ i : Fin 3, lerayKernel i j k τ (x - z) * χ z i) =
      fun z => -((x - z) k / (2 * τ)) * heatKernel τ (x - z) * χ z j +
        ∑ i : Fin 3, (∫ ρ in Ioi τ, heatKernelThird i j k ρ (x - z)) * χ z i := funext hpt
  rw [hfun, integral_add hAint hBint, hB0, add_zero]
  exact gradient_part hHP hτ hχs hχc j k x

end Breakdown.FarField
