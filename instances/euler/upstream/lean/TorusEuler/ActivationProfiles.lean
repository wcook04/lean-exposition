import TorusEuler.Statement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The spatial envelope in §5.1 and the time switch and residual factor in §6.2. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

/-- The cutoff equals one through radius one and zero from radius two onward. -/
noncomputable def envelopeCutoff (s : ℝ) : ℝ := 1 - Real.smoothTransition (s - 1)

noncomputable def radialEnvelope (ℓ : ℝ) (a : Vec3) : ℝ := envelopeCutoff (‖a‖ / ℓ)

theorem radialEnvelope_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) {a : Vec3} (ha : ‖a‖ ≤ ℓ) :
    radialEnvelope ℓ a = 1 := by
  unfold radialEnvelope envelopeCutoff
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ((div_le_one hℓ).mpr ha)), sub_zero]

theorem radialEnvelope_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {a : Vec3} (ha : 2 * ℓ ≤ ‖a‖) :
    radialEnvelope ℓ a = 0 := by
  unfold radialEnvelope envelopeCutoff
  have h := (le_div_iff₀ hℓ).mpr ha
  rw [Real.smoothTransition.one_of_one_le (show 1 ≤ ‖a‖ / ℓ - 1 by linarith), sub_self]

theorem radialEnvelope_mem_Icc (ℓ : ℝ) (a : Vec3) : radialEnvelope ℓ a ∈ Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.mpr (Real.smoothTransition.le_one _), sub_le_self _ (Real.smoothTransition.nonneg _)⟩

theorem radialEnvelope_neg (ℓ : ℝ) (a : Vec3) : radialEnvelope ℓ (-a) = radialEnvelope ℓ a := by
  simp only [radialEnvelope, norm_neg]

theorem contDiff_radialEnvelope {ℓ : ℝ} (hℓ : 0 < ℓ) : ContDiff ℝ ∞ (radialEnvelope ℓ) := by
  have hc : ContDiff ℝ ∞ envelopeCutoff := by
    unfold envelopeCutoff
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
  refine contDiff_iff_contDiffAt.mpr fun a => ?_
  by_cases ha : a = 0
  · subst a
    have heq : radialEnvelope ℓ =ᶠ[𝓝 (0 : Vec3)] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Vec3) hℓ] with x hx
      exact radialEnvelope_eq_one hℓ (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hx))
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hc.contDiffAt.comp a ((contDiffAt_norm ℝ ha).div_const ℓ)

theorem tsupport_radialEnvelope_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (radialEnvelope ℓ) ⊆ {a | ‖a‖ ≤ 2 * ℓ} := by
  apply closure_minimal _ (isClosed_le continuous_norm continuous_const)
  intro x hx
  by_contra hn
  exact (Function.mem_support.mp hx) (radialEnvelope_eq_zero hℓ (le_of_lt (lt_of_not_ge hn)))

/-- The switch of §6.2 written with the same cutoff as the spatial envelope. -/
noncomputable def waveSwitch (t₀ r t : ℝ) : ℝ := Real.smoothTransition (r * (t - t₀))

theorem waveSwitch_eq_one_sub_envelopeCutoff (t₀ r t : ℝ) :
    waveSwitch t₀ r t = 1 - envelopeCutoff (1 + r * (t - t₀)) := by
  unfold waveSwitch envelopeCutoff
  rw [show 1 + r * (t - t₀) - 1 = r * (t - t₀) by ring, sub_sub_cancel]

theorem contDiff_waveSwitch (t₀ r : ℝ) : ContDiff ℝ ∞ (waveSwitch t₀ r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem waveSwitch_eq_zero_of_le {t₀ r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ t₀) :
    waveSwitch t₀ r t = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr ht))

theorem waveSwitch_eq_one_of_activation {t₀ r t : ℝ} (hr : 0 < r) (ht : t₀ + 1 / r ≤ t) :
    waveSwitch t₀ r t = 1 :=
  Real.smoothTransition.one_of_one_le (by
    have h := (div_le_iff₀ hr).mp (show 1 / r ≤ t - t₀ by linarith)
    rwa [mul_comm] at h)

private theorem deriv_smoothTransition_zero_of_not_mem {s : ℝ} (hs : s ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition s = 0 := by
  by_cases h₀ : s < 0
  · have hEq : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
      by filter_upwards [Iio_mem_nhds h₀] with _ hy using
        Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    exact ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hEq).deriv
  · have h₁ : 1 < s := lt_of_not_ge fun h => hs ⟨le_of_not_gt h₀, h⟩
    have hEq : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) :=
      by filter_upwards [Ioi_mem_nhds h₁] with _ hy using
        Real.smoothTransition.one_of_one_le (le_of_lt hy)
    exact ((hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq hEq).deriv

private theorem exists_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ (1 : ℕ∞ω) Real.smoothTransition).deriv'
      (n := 0)).continuous
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨(0 : ℝ), le_rfl, zero_le_one⟩ hc.abs.continuousOn
  refine ⟨|deriv Real.smoothTransition s|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hmax hx
  · rw [deriv_smoothTransition_zero_of_not_mem hx, abs_zero]
    exact abs_nonneg _

theorem deriv_waveSwitch (t₀ r t : ℝ) :
    deriv (waveSwitch t₀ r) t = deriv Real.smoothTransition (r * (t - t₀)) * r := by
  have h := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) (r * (t - t₀))).hasDerivAt
  change deriv (fun x => Real.smoothTransition (r * (x - t₀))) t = _
  simpa only [Function.comp_def, id_eq, mul_one] using
    (h.comp t (((hasDerivAt_id t).sub_const t₀).const_mul r)).deriv

/-- The switch derivative costs one growth rate and is zero outside the first unit
of normalized time. This gives the residual factor in (6.8). -/
theorem waveSwitch_weighted_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ r G : ℝ}, 0 < r → 0 ≤ G → ∀ γ : ℝ → ℝ,
      (∀ t ∈ Icc t₀ (t₀ + 1 / r), |γ t| ≤ G) →
      ∀ t, |deriv (waveSwitch t₀ r) t * γ t| ≤ C * r * G := by
  obtain ⟨C, hC, hB⟩ := exists_smoothTransition_deriv_bound
  refine ⟨C, hC, ?_⟩
  intro t₀ r G hr hG γ hγ t
  rw [deriv_waveSwitch, abs_mul, abs_mul, abs_of_pos hr]
  let τ := r * (t - t₀)
  by_cases ht : τ ∈ Icc (0 : ℝ) 1
  · have hnonneg : 0 ≤ t - t₀ := nonneg_of_mul_nonneg_right ht.1 hr
    have hleft : t₀ ≤ t := sub_nonneg.mp hnonneg
    have hright : t - t₀ ≤ 1 / r := (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using ht.2)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hB τ) hr.le)
      (hγ t ⟨hleft, by linarith⟩) (abs_nonneg _) (by positivity)
  · rw [deriv_smoothTransition_zero_of_not_mem ht, abs_zero, zero_mul, zero_mul]
    positivity

end TorusEuler
