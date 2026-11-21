import Breakdown.Cert.CoerciveSmoothApproxDerivative
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound
import Breakdown.Cert.CoerciveSmoothApproxIterated
import Breakdown.Cert.CoerciveSmoothApproxGeneral
import Breakdown.Cert.CoerciveFrequencySeminormWeight
import Breakdown.Cert.CoerciveSmoothApproxClassSixth
import Breakdown.Cert.CoerciveSmoothApproxClassTransport

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem kernel_support_subset (n : ℕ) :
    tsupport (kernel n) ⊆ {t : ℝ × Space | ‖t.2‖ ≤ 2} := by
  refine closure_minimal ?_ (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)
  intro t ht
  have h2 : (spaceBump n).normed volume t.2 ≠ 0 := by
    intro h0
    exact ht (by simp [kernel, h0])
  have hm : t.2 ∈ Function.support ((spaceBump n).normed volume) := h2
  rw [(spaceBump n).support_normed_eq, Metric.mem_ball, dist_zero_right] at hm
  have hr : (spaceBump n).rOut = 2 / ((n : ℝ) + 1) := rfl
  have hle : 2 / ((n : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  show ‖t.2‖ ≤ 2
  linarith

theorem weight_shift (y z : Space) (hz : ‖z‖ ≤ 2) :
    1 / (1 + ‖y‖) ^ 2 ≤ 9 * (1 / (1 + ‖y - z‖) ^ 2) := by
  have h1 : ‖y - z‖ ≤ ‖y‖ + 2 := (norm_sub_le y z).trans (by linarith)
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hq : 0 < 1 + ‖y - z‖ := by positivity
  rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, mul_one_div, le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg y, norm_nonneg (y - z)]

theorem velocity_weight_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 * (1 / (1 + ‖y‖) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (FrequencySeminorm.Internal.weighted_velocity_lt_top hv)
  refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  dsimp only
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [norm_nonneg y])

theorem weight_measurable : Measurable (fun y : Space => 1 / (1 + ‖y‖) ^ 2) :=
  measurable_const.div ((measurable_const.add measurable_norm).pow_const 2)

theorem mollify_divergence_free {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ σ y, divergenceAt (mollify n v σ) y = 0 := by
  intro σ y
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  unfold divergenceAt
  simp_rw [mollify_partial n hvl hGl hv.weak_gradient,
    mollify_component n (joint_apply_locallyIntegrable hGl _)]
  rw [← integral_finsetSum _ (fun i _ =>
    kernel_component_integrable n (joint_apply_locallyIntegrable hGl (unitVector i)) (σ, y) i)]
  simp_rw [← Finset.mul_sum]
  by_cases hI : Integrable (fun t => kernel n ((σ, y) - t) *
      ∑ i : Fin 3, joint (fun s x => G s x (unitVector i)) t i) volume
  · rw [Measure.volume_eq_prod] at hI ⊢
    rw [integral_prod _ hI]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv.divergence_free] with s hs
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hs] with z hz
    simp [joint, hz]
  · exact integral_undef hI

theorem mollify_sixth_power {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ σ, ∫⁻ y, ENNReal.ofReal (‖mollify n v σ y‖ ^ 6) < ⊤ :=
  mollify_sixth_power_bound hv n

theorem mollify_weighted_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    periodLIntegral (fun σ y => ‖mollify n v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
  have e : (fun σ y => ‖mollify n v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) = fun σ y =>
      ‖∫ t, kernel n t • joint v ((σ, y) - t)‖ ^ 2 * (1 / (1 + ‖y‖) ^ 2) := by
    funext σ y
    simp only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply, mul_one_div]
  rw [e]
  refine lt_of_le_of_lt (period_convolution_weighted_sq_le (kernel_contDiff n).continuous
    (kernel_hasCompactSupport n) hv.measurable_velocity hv.periodic_velocity weight_measurable
    (by norm_num : (0 : ℝ) ≤ 9) ?_) ?_
  · intro t ht y
    exact weight_shift y t.2 (kernel_support_subset n (subset_tsupport _ ht))
  · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ((kernel_contDiff n).continuous.integrable_of_hasCompactSupport
        (kernel_hasCompactSupport n)).2)) (velocity_weight_lt_top hv)

theorem mollify_derivatives_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ j : ℕ, 1 ≤ j →
      periodLIntegral (fun σ y => ‖iteratedFDeriv ℝ j (mollify n v σ) y‖ ^ 2) < ⊤ := by
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hH := volume_prod_invariantClass
  have hφc : Continuous (fun t => ‖iteratedFDeriv ℝ k (kernel n) t‖) :=
    ((kernel_contDiff n).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hφs : HasCompactSupport (fun t => ‖iteratedFDeriv ℝ k (kernel n) t‖) :=
    ((kernel_hasCompactSupport n).iteratedFDeriv k).norm
  have hconv : ContDiff ℝ ∞ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) :=
    (kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hGl
  have hpt : ∀ σ y, ‖iteratedFDeriv ℝ (k + 1) (mollify n v σ) y‖ ^ 2 ≤
      ‖∫ t, ‖iteratedFDeriv ℝ k (kernel n) t‖ • joint (fun s x => ‖G s x‖) ((σ, y) - t)‖ ^ 2 := by
    intro σ y
    rw [← norm_iteratedFDeriv_fderiv, mollify_fderiv_clm n hvl hGl hv.weak_gradient σ]
    have h1 := norm_iteratedFDeriv_slice_le hconv k σ y
    have h2 := norm_iteratedFDeriv_convolution_le hGl k (kernel n) (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernel_contDiff n) (kernel_hasCompactSupport n) ContinuousLinearMap.opNorm_lsmul_le (σ, y)
    have h3 : ∫ t, ‖iteratedFDeriv ℝ k (kernel n) t‖ * ‖joint G ((σ, y) - t)‖ =
        ‖∫ t, ‖iteratedFDeriv ℝ k (kernel n) t‖ • joint (fun s x => ‖G s x‖) ((σ, y) - t)‖ := by
      rw [Real.norm_of_nonneg (integral_nonneg fun t => by simp only [joint, smul_eq_mul]; positivity)]
      simp only [joint, smul_eq_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (h2.trans h3.le)) 2
  refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y =>
    ENNReal.ofReal_le_ofReal (hpt σ y)) ?_
  refine lt_of_le_of_lt (period_convolution_sq_le hφc hφs (w := fun s x => ‖G s x‖)
    hv.measurable_gradient.norm (fun σ y => by simp only [hv.periodic_gradient σ y])) ?_
  refine ENNReal.mul_lt_top (ENNReal.pow_lt_top (hφc.integrable_of_hasCompactSupport hφs).2) ?_
  simpa only [norm_norm] using gradient_sq_lt_top hv

theorem mollify_time_weighted_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    periodLIntegral (fun σ y => ‖deriv (fun s => mollify n v s y) σ‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have e : (fun σ y => ‖deriv (fun s => mollify n v s y) σ‖ ^ 2 / (1 + ‖y‖) ^ 2) = fun σ y =>
      ‖∫ t, fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)‖ ^ 2 * (1 / (1 + ‖y‖) ^ 2) := by
    funext σ y
    rw [mollify_time_deriv n hvl σ y, mul_one_div]
  have hc : Continuous (fun t => fderiv ℝ (kernel n) t (1, 0)) :=
    ((kernel_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun t => fderiv ℝ (kernel n) t (1, 0)) :=
    (kernel_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (1, 0)
  rw [e]
  refine lt_of_le_of_lt (period_convolution_weighted_sq_le hc hs hv.measurable_velocity hv.periodic_velocity
    weight_measurable (by norm_num : (0 : ℝ) ≤ 9) ?_) ?_
  · intro t ht y
    have h1 : fderiv ℝ (kernel n) t ≠ 0 := by
      intro h0
      exact ht (by simp [h0])
    exact weight_shift y t.2 (kernel_support_subset n (support_fderiv_subset ℝ h1))
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (hc.integrable_of_hasCompactSupport hs).2)) (velocity_weight_lt_top hv)

theorem mollify_time_derivatives_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ j : ℕ, 1 ≤ j → periodLIntegral (fun σ y =>
      ‖iteratedFDeriv ℝ j (fun x => deriv (fun s => mollify n v s x) σ) y‖ ^ 2) < ⊤ := by
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hH := volume_prod_invariantClass
  set ψ : ℝ × Space → ℝ := fun t => fderiv ℝ (kernel n) t (1, 0) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := ((kernel_contDiff n).fderiv_right (by simp)).clm_apply contDiff_const
  have hψc : HasCompactSupport ψ := (kernel_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (1, 0)
  have hfun : ∀ σ, (fun x => deriv (fun s => mollify n v s x) σ) =
      fun x => (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) (σ, x) := by
    intro σ
    funext x
    rw [mollify_time_deriv n hvl σ x, convolution_def]
    simp only [hψdef, ContinuousLinearMap.lsmul_apply]
  have hφc : Continuous (fun t => ‖iteratedFDeriv ℝ k ψ t‖) :=
    (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hφs : HasCompactSupport (fun t => ‖iteratedFDeriv ℝ k ψ t‖) := (hψc.iteratedFDeriv k).norm
  have hconv : ContDiff ℝ ∞ (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) :=
    hψc.contDiff_convolution_left _ hψ hGl
  have hpt : ∀ σ y, ‖iteratedFDeriv ℝ (k + 1) (fun x => deriv (fun s => mollify n v s x) σ) y‖ ^ 2 ≤
      ‖∫ t, ‖iteratedFDeriv ℝ k ψ t‖ • joint (fun s x => ‖G s x‖) ((σ, y) - t)‖ ^ 2 := by
    intro σ y
    rw [hfun σ, ← norm_iteratedFDeriv_fderiv, slice_fderiv_clm_of hψ hψc hvl hGl hv.weak_gradient σ]
    have h1 := norm_iteratedFDeriv_slice_le hconv k σ y
    have h2 := norm_iteratedFDeriv_convolution_le hGl k ψ (ContinuousLinearMap.lsmul ℝ ℝ)
      hψ hψc ContinuousLinearMap.opNorm_lsmul_le (σ, y)
    have h3 : ∫ t, ‖iteratedFDeriv ℝ k ψ t‖ * ‖joint G ((σ, y) - t)‖ =
        ‖∫ t, ‖iteratedFDeriv ℝ k ψ t‖ • joint (fun s x => ‖G s x‖) ((σ, y) - t)‖ := by
      rw [Real.norm_of_nonneg (integral_nonneg fun t => by simp only [joint, smul_eq_mul]; positivity)]
      simp only [joint, smul_eq_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (h2.trans h3.le)) 2
  refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y =>
    ENNReal.ofReal_le_ofReal (hpt σ y)) ?_
  refine lt_of_le_of_lt (period_convolution_sq_le hφc hφs (w := fun s x => ‖G s x‖)
    hv.measurable_gradient.norm (fun σ y => by simp only [hv.periodic_gradient σ y])) ?_
  refine ENNReal.mul_lt_top (ENNReal.pow_lt_top (hφc.integrable_of_hasCompactSupport hφs).2) ?_
  simpa only [norm_norm] using gradient_sq_lt_top hv

theorem mollify_transport_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ j : ℕ, periodLIntegral (fun σ y =>
      ‖iteratedFDeriv ℝ j (transportPart P (mollify n v) σ) y‖ ^ 2) < ⊤ :=
  transport_finite_bound hv n

theorem mollify_isSmoothPerturbation {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    IsSmoothPerturbation P (mollify n v) where
  smooth := mollify_smooth n (PerturbationFacts.velocity_locallyIntegrable hv)
  periodic := mollify_periodic n hv.periodic_velocity
  divergence_free := mollify_divergence_free hv n
  sixth_power := mollify_sixth_power hv n
  weighted_finite := mollify_weighted_finite hv n
  derivatives_finite := mollify_derivatives_finite hv n
  time_weighted_finite := mollify_time_weighted_finite hv n
  time_derivatives_finite := mollify_time_derivatives_finite hv n
  transport_finite := mollify_transport_finite hv n

end Internal.SmoothApprox

end Coercive

end Breakdown
