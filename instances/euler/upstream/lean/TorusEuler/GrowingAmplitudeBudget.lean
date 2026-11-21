import TorusEuler.GrowingAmplitudeNorm
import TorusEuler.ReferenceRatio

/-! The error budget for the growing amplitude in Lemma 2.5. -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler.ReferenceAmplitude

open ReferenceComparison ReferencePropagator MovingWaveVector MovingAmplitude
open ReferenceRiccati (s s_pos rhs damping driving hasDerivAt_s inv_sq_window_le_s)

/-- The exponent and coefficient in (2.5) can absorb the matrix error and
geometric correction budgets for the logarithmic amplitude estimate. -/
theorem growing_budget_of_polynomial_smallness {C T δ ε : ℝ} {p C₀ : ℕ}
    (hT : 2 ≤ T) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hp : p + 3 ≤ C₀) (hfour : 4 ≤ C₀) (hC₀ : 64 * C + 40 ≤ C₀)
    (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) :
    64 * C * T ^ (p + 3) * δ + 40 * T ^ 4 * δ ≤ ε := by
  have hT₁ : 1 ≤ T := by linarith
  calc
    _ ≤ 64 * C * T ^ C₀ * δ + 40 * T ^ C₀ * δ := by
      refine add_le_add (mul_le_mul_of_nonneg_right ?_ hδ) (mul_le_mul_of_nonneg_right ?_ hδ)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT₁ hp) (by positivity)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT₁ hfour) (by norm_num)
    _ = (64 * C + 40) * T ^ C₀ * δ := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀ (pow_nonneg (by linarith) _)) hδ).trans hsmall

/-- The normalized matrix weight costs at most `4 * T ^ 3` after integration on a
window of length `T`, for a uniform raw error bound `η`. -/
theorem integrated_growing_error_le {ε T t η : ℝ} {Y : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T) (ht : t ∈ Icc 0 T) (hη : 0 ≤ η)
    (hYc : ContinuousOn Y (Icc 0 T)) (hYb : ∀ r ∈ Icc 0 T, |Y r| ≤ 1) :
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η
    0 ≤ D ∧ D ≤ 4 * T ^ 3 * η := by
  let w (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η
  change 0 ≤ (∫ r in 0..t, w r) ∧ (∫ r in 0..t, w r) ≤ 4 * T ^ 3 * η
  have hTc : 0 < T := by linarith
  have hw₀ (r : ℝ) : 0 ≤ w r := mul_nonneg (div_nonneg (sq_nonneg _) (s_pos ε r).le) hη
  have hs : Continuous (s ε) :=
    continuous_iff_continuousAt.2 (fun r => (hasDerivAt_s ε r).continuousAt)
  have hwc : ContinuousOn w (Icc 0 T) :=
    ((((continuousOn_const.add hYc.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul continuousOn_const)
  have hw (r : ℝ) (hr : r ∈ Icc 0 t) : w r ≤ 4 * T ^ 2 * η := by
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    have hsq : (1 + |Y r|) ^ 2 ≤ 4 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |Y r|) (by linarith [hYb r hrT] :
        1 + |Y r| ≤ 2) 2
      norm_num at h
      exact h
    have hinv : (s ε r)⁻¹ ≤ T ^ 2 := by
      simpa only [inv_inv] using inv_anti₀ (by positivity : 0 < (T ^ 2)⁻¹)
        (inv_sq_window_le_s hε hε₁ hT hrT)
    unfold w
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hsq hinv (inv_nonneg.mpr (s_pos ε r).le) (by norm_num)) hη
  refine ⟨intervalIntegral.integral_nonneg_of_forall ht.1 hw₀, ?_⟩
  calc
    _ ≤ ∫ r in 0..t, 4 * T ^ 2 * η := intervalIntegral.integral_mono_on ht.1
      ((hwc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
      intervalIntegrable_const hw
    _ = t * (4 * T ^ 2 * η) := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ T * (4 * T ^ 2 * η) :=
      mul_le_mul_of_nonneg_right ht.2 (by positivity)
    _ = _ := by ring

/-- A uniform polynomial bound on the raw matrix error and the wave-vector
window imply (2.9) under the displayed error budget. -/
theorem log_growing_physical_norm_of_raw_matrix {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {Y : ℝ → ℝ} {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {ε T t scale S C δ : ℝ} {p : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hsmall : 64 * C * T ^ (p + 3) * δ + 40 * T ^ 4 * δ ≤ ε)
    (hS : 1 ≤ S) (hSinv : S⁻¹ ≤ 2 * δ) (hscale : scale ≠ 0)
    (hY₀ : Y 0 = 1) (hYb : ∀ r ∈ Icc 0 T, |Y r| ≤ 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hR : ContinuousOn R (Icc 0 T)) (hRη : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ C * T ^ p * δ)
    (hU₀ : U e a S 0 = 1) (hV₀ : V e a 0 = 1)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt (U e a S)
      (-damping ε r * U e a S r + driving ε r * V e a r + (R r (U e a S r, V e a r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt (V e a)
      (U e a S r + (R r (U e a S r, V e a r)).2) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (he : Orthonormal ℝ (e t)) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (hX : |X e k scale t| ≤ T ^ 2) (hQ : |Q e k scale S t| ≤ T)
    (hZ : 1 / 2 ≤ Z e k scale t) :
    |Real.log (‖a t‖ / growingFactor Y t)| ≤ ε := by
  let η := C * T ^ p * δ
  let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η
  have hT₁ : 1 ≤ T := by linarith
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hgeom₀ : 0 ≤ 40 * T ^ 4 * δ := by positivity
  obtain ⟨hD₀, hbudgetRaw⟩ :=
    integrated_growing_error_le hε.le hε₁ hT ht hη (HasDerivWithinAt.continuousOn hY) hYb
  have hbudget : D ≤ 4 * C * T ^ (p + 3) * δ := by
    convert hbudgetRaw using 1
    rw [pow_add]
    unfold η
    ring
  change 0 ≤ D at hD₀
  have hD : D ≤ 1 / 4 := by
    nlinarith only [hbudget, hsmall, hgeom₀, hε₁]
  have hexp : Real.exp (2 * D) ≤ 2 := by
    have h := Real.abs_exp_sub_one_le (x := 2 * D)
      (by rw [abs_of_nonneg (by positivity)]; linarith)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * D)] at h
    linarith [(abs_le.mp h).2]
  let d := 32 * C * T ^ (p + 3) * δ
  have hd : d ≤ 1 / 2 := by dsimp [d]; nlinarith only [hsmall, hgeom₀, hε₁]
  have hstate := normalized_close_to_growing_of_raw_matrix hε hY₀ hU₀ hV₀ hY hR
    (hη := continuousOn_const) hRη hU hV ht
  change ‖normalizedState ε Y (U e a S) (V e a) t - (1, 0)‖ ≤
    4 * Real.exp (2 * D) * D at hstate
  have hclose : ‖normalizedState ε Y (U e a S) (V e a) t - (1, 0)‖ ≤ d := by
    calc
      _ ≤ 4 * Real.exp (2 * D) * D := hstate
      _ ≤ 8 * D := by nlinarith [mul_nonneg hD₀ (sub_nonneg.mpr hexp)]
      _ ≤ d := by dsimp [d]; nlinarith only [hbudget]
  have hS₀ : 0 < S := by linarith
  have hinv : (S ^ 2)⁻¹ ≤ 2 * δ := by
    rw [← inv_pow]
    have hS₁ : S⁻¹ ≤ 1 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hS
    exact (by nlinarith [mul_nonneg (inv_nonneg.mpr hS₀.le) (sub_nonneg.mpr hS₁)] :
      S⁻¹ ^ 2 ≤ S⁻¹).trans hSinv
  calc
    _ ≤ 2 * d + 20 * T ^ 4 * (S ^ 2)⁻¹ :=
      log_growing_physical_norm_le he hscale hS₀ hperp hT₁ hX hQ hZ (hYb t ht) hd hclose
    _ ≤ 2 * d + 20 * T ^ 4 * (2 * δ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = 64 * C * T ^ (p + 3) * δ + 40 * T ^ 4 * δ := by unfold d; ring
    _ ≤ ε := hsmall

end TorusEuler.ReferenceAmplitude
