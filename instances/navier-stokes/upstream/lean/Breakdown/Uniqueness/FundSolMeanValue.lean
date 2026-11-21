import Breakdown.Uniqueness.FundSolPotential
import Breakdown.Uniqueness.FundSolPointwiseAux2
import Breakdown.Uniqueness.FundSolMeanValueAux

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FundSol

private theorem contDiff_bumpProfile : ContDiff ℝ ∞ bumpProfile := by
  unfold bumpProfile
  exact smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

private theorem bumpProfile_nonneg (x : Space) : 0 ≤ bumpProfile x := smoothTransition.nonneg _

private theorem bumpProfile_le_one (x : Space) : bumpProfile x ≤ 1 := smoothTransition.le_one _

private theorem bumpProfile_eq_zero {x : Space} (hx : 1 / 2 ≤ ‖x‖ ^ 2) : bumpProfile x = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

private theorem bumpProfile_zero : bumpProfile 0 = 1 := by
  simp [bumpProfile]

private theorem hasCompactSupport_bumpProfile : HasCompactSupport bumpProfile := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  apply bumpProfile_eq_zero
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  nlinarith

private theorem integral_bumpProfile_pos : 0 < ∫ y, bumpProfile y :=
  contDiff_bumpProfile.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_bumpProfile (fun x => bumpProfile_nonneg x) (x := 0)
    (by rw [bumpProfile_zero]; norm_num)

theorem contDiff_mollifier (ρ : ℝ) : ContDiff ℝ ∞ (mollifier ρ) := by
  unfold mollifier
  exact contDiff_const.mul (contDiff_bumpProfile.comp (contDiff_const_smul ρ⁻¹))

theorem mollifier_nonneg {ρ : ℝ} (hρ : 0 < ρ) (x : Space) : 0 ≤ mollifier ρ x := by
  unfold mollifier
  exact mul_nonneg (inv_nonneg.2 (mul_nonneg (pow_nonneg hρ.le 3) integral_bumpProfile_pos.le))
    (bumpProfile_nonneg _)

private theorem mollifier_eq_zero_of_sq {ρ : ℝ} (hρ : 0 < ρ) {x : Space} (hx : ρ ^ 2 / 2 ≤ ‖x‖ ^ 2) :
    mollifier ρ x = 0 := by
  unfold mollifier
  rw [bumpProfile_eq_zero, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, mul_pow, inv_pow,
    le_inv_mul_iff₀ (by positivity)]
  linarith

theorem mollifier_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {x : Space} (hx : ρ ≤ ‖x‖) : mollifier ρ x = 0 := by
  apply mollifier_eq_zero_of_sq hρ
  have : ρ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hρ.le hx 2
  nlinarith

theorem integral_mollifier {ρ : ℝ} (hρ : 0 < ρ) : ∫ x, mollifier ρ x = 1 := by
  unfold mollifier
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ hρ.le,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have := integral_bumpProfile_pos
  field_simp

theorem mollifier_le : ∃ C : ℝ, ∀ ρ, 0 < ρ → ∀ x, mollifier ρ x ≤ C * ρ⁻¹ ^ 3 := by
  refine ⟨(∫ y, bumpProfile y)⁻¹, fun ρ hρ x => ?_⟩
  unfold mollifier
  have hI := integral_bumpProfile_pos
  calc _ ≤ (ρ ^ 3 * ∫ y, bumpProfile y)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (bumpProfile_le_one _) (by positivity)
    _ = _ := by rw [mul_one, mul_inv, inv_pow]; ring

private theorem norm_iteratedFDeriv_mollifier_le (k : ℕ) : ∃ C : ℝ, ∀ ρ, 0 < ρ → ∀ x,
    ‖iteratedFDeriv ℝ k (mollifier ρ) x‖ ≤ C * ρ⁻¹ ^ (3 + k) := by
  obtain ⟨M, hM⟩ := (contDiff_bumpProfile.continuous_iteratedFDeriv (m := k)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (hasCompactSupport_bumpProfile.iteratedFDeriv k)
  refine ⟨(∫ y, bumpProfile y)⁻¹ * M, fun ρ hρ x => ?_⟩
  have hI := integral_bumpProfile_pos
  set L : Space →L[ℝ] Space := ρ⁻¹ • ContinuousLinearMap.id ℝ Space with hLdef
  have hmol : mollifier ρ = fun y => (ρ ^ 3 * ∫ y, bumpProfile y)⁻¹ • (bumpProfile ∘ L) y := by
    funext y; simp [mollifier, L]
  have hL : ‖L‖ ≤ ρ⁻¹ := by
    rw [hLdef, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  rw [hmol, iteratedFDeriv_const_smul_apply'
    ((contDiff_bumpProfile.comp L.contDiff).contDiffAt.of_le (by exact_mod_cast le_top)),
    L.iteratedFDeriv_comp_right contDiff_bumpProfile x (by exact_mod_cast le_top), norm_smul,
    Real.norm_of_nonneg (by positivity)]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc (ρ ^ 3 * ∫ y, bumpProfile y)⁻¹ *
        ‖(iteratedFDeriv ℝ k bumpProfile (L x)).compContinuousLinearMap fun _ => L‖
      ≤ (ρ ^ 3 * ∫ y, bumpProfile y)⁻¹ * (M * ρ⁻¹ ^ k) := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) hL k) (by positivity) hM0
    _ = _ := by rw [mul_inv, inv_pow, pow_add]; ring

theorem norm_fderiv_mollifier_le : ∃ C : ℝ, ∀ ρ, 0 < ρ → ∀ x,
    ‖fderiv ℝ (mollifier ρ) x‖ ≤ C * ρ⁻¹ ^ 4 := by
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_mollifier_le 1
  exact ⟨C, fun ρ hρ x => by simpa [norm_iteratedFDeriv_one] using hC ρ hρ x⟩

theorem norm_iteratedFDeriv_two_mollifier_le : ∃ C : ℝ, ∀ ρ, 0 < ρ → ∀ x,
    ‖iteratedFDeriv ℝ 2 (mollifier ρ) x‖ ≤ C * ρ⁻¹ ^ 5 := by
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_mollifier_le 2
  exact ⟨C, fun ρ hρ x => by simpa using hC ρ hρ x⟩

private theorem hasCompactSupport_mollifier {ρ : ℝ} (hρ : 0 < ρ) : HasCompactSupport (mollifier ρ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) ρ)
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact mollifier_eq_zero hρ hx.le

private theorem potential_eq_integral (g : Space → ℝ) (x : Space) :
    potential g x = ∫ y, g y * kernel (x - y) := by
  rw [potential, convolution_def]
  simp

private theorem potential_mollifier_map (ρ : ℝ) (A : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    potential (mollifier ρ) (A x) = potential (mollifier ρ) x := by
  have hm : ∀ y, mollifier ρ (A y) = mollifier ρ y := by
    intro y
    simp [mollifier, bumpProfile, norm_smul]
  have hk : ∀ y, kernel (A x - A y) = kernel (x - y) := by
    intro y
    simp only [kernel, ← map_sub, LinearIsometryEquiv.norm_map]
  have h := (LinearIsometryEquiv.measurePreserving A).integral_comp
    A.toHomeomorph.measurableEmbedding (fun y => mollifier ρ y * kernel (A x - y))
  rw [potential_eq_integral, potential_eq_integral, ← h]
  simp only [LinearIsometryEquiv.coe_toHomeomorph, hm, hk]

private theorem potential_mollifier_radial (ρ : ℝ) (x : Space) :
    potential (mollifier ρ) x = potential (mollifier ρ) (√(‖x‖ ^ 2) • unitVector 0) := by
  have hn : ‖‖x‖ • unitVector 0‖ = ‖x‖ := by
    simp [norm_smul, unitVector, EuclideanSpace.norm_single]
  rw [Real.sqrt_sq (norm_nonneg x)]
  conv_lhs => rw [← Submodule.reflection_sub hn]
  exact potential_mollifier_map ρ _ _

private theorem abs_potential_mollifier_sub_kernel_le {ρ : ℝ} (hρ : 0 < ρ) {x : Space}
    (hx : 2 * ρ ≤ ‖x‖) :
    |potential (mollifier ρ) x - kernel x| ≤ (4 * π)⁻¹ * (2 * ρ) / ‖x‖ ^ 2 := by
  set r := ‖x‖ with hr
  have hr0 : 0 < r := by linarith
  have hπ : 0 < (4 * π)⁻¹ := by positivity
  have hmi : Integrable (mollifier ρ) :=
    (contDiff_mollifier ρ).continuous.integrable_of_hasCompactSupport (hasCompactSupport_mollifier hρ)
  have hsupp : ∀ y, mollifier ρ y ≠ 0 → ‖y‖ < ρ := fun y hy => by
    by_contra h
    exact hy (mollifier_eq_zero hρ (not_lt.1 h))
  have hdist : ∀ y, ‖y‖ < ρ → r / 2 ≤ ‖x - y‖ := fun y hy => by
    have := norm_sub_norm_le x y
    linarith
  have hkm : Measurable fun y : Space => kernel (x - y) := by
    unfold kernel
    fun_prop
  have hmeas : AEStronglyMeasurable (fun y => mollifier ρ y * kernel (x - y)) volume :=
    ((contDiff_mollifier ρ).continuous.measurable.mul hkm).aestronglyMeasurable
  have hint : Integrable (fun y => mollifier ρ y * kernel (x - y)) := by
    refine (hmi.mul_const ((4 * π)⁻¹ * (2 / r))).mono' hmeas (Eventually.of_forall fun y => ?_)
    by_cases hy : mollifier ρ y = 0
    · simp [hy]
    have hd := hdist y (hsupp y hy)
    rw [norm_mul, Real.norm_of_nonneg (mollifier_nonneg hρ y)]
    apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg hρ y)
    rw [kernel, norm_mul, norm_neg, Real.norm_of_nonneg hπ.le, norm_inv, norm_norm]
    apply mul_le_mul_of_nonneg_left _ hπ.le
    calc ‖x - y‖⁻¹ ≤ (r / 2)⁻¹ := inv_anti₀ (by positivity) hd
      _ = 2 / r := by rw [inv_div]
  have hk : kernel x = ∫ y, mollifier ρ y * kernel x := by
    rw [integral_mul_const, integral_mollifier hρ, one_mul]
  rw [potential_eq_integral, hk, ← integral_sub hint (hmi.mul_const _)]
  have hbound : ∀ y, ‖mollifier ρ y * kernel (x - y) - mollifier ρ y * kernel x‖ ≤
      mollifier ρ y * ((4 * π)⁻¹ * (2 * ρ) / r ^ 2) := by
    intro y
    by_cases hy : mollifier ρ y = 0
    · simp [hy]
    have hyρ := hsupp y hy
    have hd := hdist y hyρ
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (mollifier_nonneg hρ y)]
    apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg hρ y)
    have hd0 : 0 < ‖x - y‖ := by linarith
    have e : kernel (x - y) - kernel x = (4 * π)⁻¹ * ((‖x - y‖ - r) / (‖x - y‖ * r)) := by
      simp only [kernel, ← hr]
      field_simp
      ring
    rw [e, norm_mul, Real.norm_of_nonneg hπ.le, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hπ.le
    rw [norm_div, Real.norm_eq_abs, abs_sub_comm, Real.norm_of_nonneg (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := abs_norm_sub_norm_le x (x - y)
    rw [sub_sub_cancel, ← hr] at h1
    have h2 : |r - ‖x - y‖| * r ^ 2 ≤ ‖y‖ * r ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg r)
    have h3 : ‖y‖ * r ^ 2 ≤ ρ * r ^ 2 := mul_le_mul_of_nonneg_right hyρ.le (sq_nonneg r)
    have h4 : ρ * r * r ≤ ρ * r * (2 * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  calc |∫ y, (mollifier ρ y * kernel (x - y) - mollifier ρ y * kernel x)|
      = ‖∫ y, (mollifier ρ y * kernel (x - y) - mollifier ρ y * kernel x)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, mollifier ρ y * ((4 * π)⁻¹ * (2 * ρ) / r ^ 2) :=
        norm_integral_le_of_norm_le (hmi.mul_const _) (Eventually.of_forall hbound)
    _ = (4 * π)⁻¹ * (2 * ρ) / r ^ 2 := by
        rw [integral_mul_const, integral_mollifier hρ, one_mul]

private def kernelFloor (δ s : ℝ) : ℝ :=
  δ ^ 2 / 2 * (1 - smoothTransition (2 * s / δ ^ 2 - 1)) + s * smoothTransition (2 * s / δ ^ 2 - 1)

private def smoothKernel (δ : ℝ) (w : Space) : ℝ := -(4 * π)⁻¹ * (√(kernelFloor δ (‖w‖ ^ 2)))⁻¹

private theorem contDiff_kernelFloor (δ : ℝ) : ContDiff ℝ ∞ (kernelFloor δ) := by
  have hτ : ContDiff ℝ ∞ fun s : ℝ => smoothTransition (2 * s / δ ^ 2 - 1) :=
    smoothTransition.contDiff.comp (((contDiff_const.mul contDiff_id).div_const _).sub contDiff_const)
  exact (contDiff_const.mul (contDiff_const.sub hτ)).add (contDiff_id.mul hτ)

private theorem kernelFloor_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 < kernelFloor δ s := by
  unfold kernelFloor
  have h0 := smoothTransition.nonneg (2 * s / δ ^ 2 - 1)
  have h1 := smoothTransition.le_one (2 * s / δ ^ 2 - 1)
  have hδ2 : 0 < δ ^ 2 := by positivity
  by_cases hs : δ ^ 2 / 2 ≤ s
  · nlinarith
  · have hneg : 2 * s / δ ^ 2 - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hδ2]
      linarith
    rw [smoothTransition.zero_of_nonpos hneg]
    linarith

private theorem kernelFloor_eq {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : δ ^ 2 ≤ s) : kernelFloor δ s = s := by
  unfold kernelFloor
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h1 : 1 ≤ 2 * s / δ ^ 2 - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδ2]
    linarith
  rw [smoothTransition.one_of_one_le h1]
  ring

private theorem contDiff_smoothKernel {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (smoothKernel δ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hp := kernelFloor_pos hδ (‖w‖ ^ 2)
  have hg : ContDiffAt ℝ ∞ (fun w : Space => kernelFloor δ (‖w‖ ^ 2)) w :=
    ((contDiff_kernelFloor δ).comp (contDiff_norm_sq ℝ)).contDiffAt
  have hs := (Real.contDiffAt_sqrt (n := ∞) hp.ne').comp w hg
  exact contDiffAt_const.mul (hs.inv (Real.sqrt_pos.2 hp).ne')

private theorem smoothKernel_eq {δ : ℝ} (hδ : 0 < δ) {w : Space} (hw : δ ≤ ‖w‖) :
    smoothKernel δ w = kernel w := by
  have h2 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ.le hw 2
  rw [smoothKernel, kernelFloor_eq hδ h2, Real.sqrt_sq (norm_nonneg w), kernel]

private theorem secondPartial_congr_nhds {θ₁ θ₂ : Space → ℝ} {x : Space} (h : θ₁ =ᶠ[𝓝 x] θ₂)
    (i j : Fin 3) : secondPartial θ₁ i j x = secondPartial θ₂ i j x := by
  simp only [secondPartial, (h.iteratedFDeriv ℝ 2).eq_of_nhds]

private theorem scalarSumSecondPartials_potential_mollifier_far {ρ : ℝ} (hρ : 0 < ρ) {y : Space}
    (hy : ρ ^ 2 / 2 < ‖y‖ ^ 2) : scalarSumSecondPartials (potential (mollifier ρ)) y = 0 := by
  set a := √(ρ ^ 2 / 2) with ha_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ρ ^ 2 / 2 := Real.sq_sqrt (by positivity)
  have ha : a < ‖y‖ := by
    by_contra h
    have := pow_le_pow_left₀ (norm_nonneg y) (not_lt.1 h) 2
    linarith
  set δ := ‖y‖ - a with hδ_def
  have hδ : 0 < δ := by linarith
  have hsm := contDiff_smoothKernel hδ
  have hmc := hasCompactSupport_mollifier hρ
  have hms := contDiff_mollifier ρ
  have hmz : ∀ z : Space, a ≤ ‖z‖ → mollifier ρ z = 0 := fun z hz =>
    mollifier_eq_zero_of_sq hρ (by rw [← ha2]; exact pow_le_pow_left₀ ha0 hz 2)
  have hz1 : ∀ z : Space, ‖z‖ ≤ a → smoothKernel δ (y - z) = kernel (y - z) := fun z hz =>
    smoothKernel_eq hδ (by have := norm_sub_norm_le y z; linarith)
  have hsp : ∀ (i : Fin 3) (z : Space), a < ‖z‖ → secondPartial (mollifier ρ) i i z = 0 := by
    intro i z hz
    have h : mollifier ρ =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
        fun w hw => hmz w (le_of_lt hw)
    rw [secondPartial_congr_nhds h]
    simp [secondPartial]
  have hsk : ∀ z : Space, ‖z‖ < a → ∑ i, secondPartial (smoothKernel δ) i i (y - z) = 0 := by
    intro z hz
    have hlt : δ < ‖y - z‖ := by have := norm_sub_norm_le y z; linarith
    have h : smoothKernel δ =ᶠ[𝓝 (y - z)] kernel :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hlt)
        fun w hw => smoothKernel_eq hδ (le_of_lt hw)
    have hne : y - z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      linarith
    simp only [secondPartial_congr_nhds h, secondPartial_kernel hne]
    exact sum_kernelSecondDeriv_diag hne
  have step : ∀ i : Fin 3, potential (secondPartial (mollifier ρ) i i) y =
      ∫ z, mollifier ρ z * secondPartial (smoothKernel δ) i i (y - z) := by
    intro i
    rw [potential_eq_integral, ← Internal.integral_secondPartial_mul hms hmc hsm y i i]
    congr 1
    funext z
    by_cases hz : ‖z‖ ≤ a
    · rw [hz1 z hz]
    · rw [hsp i z (not_le.1 hz), zero_mul, zero_mul]
  have hcont : ∀ i : Fin 3, Continuous fun z : Space => secondPartial (smoothKernel δ) i i (y - z) :=
    fun i => ((continuous_eval_const _).comp
      (hsm.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.2 le_top))).comp
      (continuous_const.sub continuous_id)
  unfold scalarSumSecondPartials
  simp only [secondPartial_potential hms hmc, step]
  rw [← integral_finset_sum _ fun i _ =>
    Internal.integrable_mul_of_cpt hms.continuous (hcont i) (Or.inl hmc)]
  have hzero : ∀ z : Space, ∑ i, mollifier ρ z * secondPartial (smoothKernel δ) i i (y - z) = 0 := by
    intro z
    rw [← Finset.mul_sum]
    by_cases hz : ‖z‖ < a
    · rw [hsk z hz, mul_zero]
    · rw [hmz z (not_lt.1 hz), zero_mul]
  simp only [hzero, integral_zero]

theorem potential_mollifier_eq_kernel {ρ : ℝ} (hρ : 0 < ρ) {x : Space} (hx : ρ ≤ ‖x‖) :
    potential (mollifier ρ) x = kernel x := by
  have hPs : ContDiff ℝ ∞ (potential (mollifier ρ)) :=
    contDiff_potential (contDiff_mollifier ρ) (hasCompactSupport_mollifier hρ)
  set φ : ℝ → ℝ := fun s => potential (mollifier ρ) (√s • unitVector 0) with hφdef
  have hφs : ContDiffOn ℝ ∞ φ (Ioi 0) := fun s hs =>
    (hPs.contDiffAt.comp s
      ((Real.contDiffAt_sqrt (ne_of_gt hs)).smul contDiffAt_const)).contDiffWithinAt
  have hPeq : potential (mollifier ρ) = fun y => φ (‖y‖ ^ 2) :=
    funext fun y => potential_mollifier_radial ρ y
  have he : ‖unitVector 0‖ = 1 := by simp [unitVector, EuclideanSpace.norm_single]
  have hnorm : ∀ s, 0 ≤ s → ‖√s • unitVector 0‖ ^ 2 = s := fun s hs => by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg s), Real.sq_sqrt hs]
  have hd1 : ∀ s > 0, DifferentiableAt ℝ φ s := fun s hs =>
    (hφs.contDiffAt (isOpen_Ioi.mem_nhds hs)).differentiableAt (by simp)
  have hd2 : ∀ s > 0, DifferentiableAt ℝ (deriv φ) s := fun s hs =>
    ((hφs.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num; exact WithTop.coe_le_coe.2 le_top)).contDiffAt
      (isOpen_Ioi.mem_nhds hs)).differentiableAt (by norm_num)
  have hode : ∀ s > ρ ^ 2 / 2, 6 * deriv φ s + 4 * s * deriv (deriv φ) s = 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
    set y := √s • unitVector 0 with hy
    have hy2 : ‖y‖ ^ 2 = s := hnorm s hs0.le
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hy2
      linarith
    have h1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ φ (‖z‖ ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
      exact hd1 _ (by positivity)
    have hssp := Internal.scalarSumSecondPartials_comp_norm_sq h1 (by rw [hy2]; exact hd2 s hs0)
    rw [← hPeq, scalarSumSecondPartials_potential_mollifier_far hρ (by rw [hy2]; exact hs), hy2] at hssp
    linarith
  obtain ⟨A, B, hAB⟩ := Internal.eq_add_div_sqrt_of_radial_ode (by positivity : (0 : ℝ) ≤ ρ ^ 2 / 2)
    ((hφs.mono (Ioi_subset_Ioi (by positivity))).of_le (WithTop.coe_le_coe.2 le_top)) hode
  have hbd : ∀ s ≥ (2 * ρ) ^ 2, |A + (B + (4 * π)⁻¹) / √s| ≤ (4 * π)⁻¹ * (2 * ρ) / s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    have hy2 := hnorm s hs0.le
    have hy1 : ‖√s • unitVector 0‖ = √s := by
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg s)]
    have h2ρ : 2 * ρ ≤ √s := by
      have := Real.sqrt_le_sqrt hs
      rwa [Real.sqrt_sq (by positivity)] at this
    have hb := abs_potential_mollifier_sub_kernel_le hρ (hy1 ▸ h2ρ)
    rw [hy2] at hb
    have hφv : potential (mollifier ρ) (√s • unitVector 0) = A + B / √s :=
      hAB s (lt_of_lt_of_le (by nlinarith) hs)
    rw [hφv, kernel, hy1] at hb
    convert hb using 2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  obtain ⟨hA, hB⟩ := Internal.eq_zero_of_abs_add_div_sqrt_le hbd
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hρ hx
  have hxs : ‖x‖ ^ 2 > ρ ^ 2 / 2 := by nlinarith
  rw [hPeq]
  simp only
  rw [hAB _ hxs, hA, Real.sqrt_sq hx0.le, kernel, zero_add, eq_neg_of_add_eq_zero_left hB]
  ring

end Breakdown.FundSol
