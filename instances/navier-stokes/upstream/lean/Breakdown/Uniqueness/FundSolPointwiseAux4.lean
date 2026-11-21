import Breakdown.Uniqueness.FundSolPointwiseAux3

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.FundSol.Internal

theorem hasCompactSupport_mollifier {ρ : ℝ} (hρ : 0 < ρ) : HasCompactSupport (mollifier ρ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) ρ) fun x hx =>
    mollifier_eq_zero hρ (by rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le)

theorem isOpen_norm_gt (ρ : ℝ) : IsOpen {w : Space | ρ < ‖w‖} :=
  isOpen_lt continuous_const continuous_norm

theorem secondPartial_mollifier_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {t : Space} (ht : ρ < ‖t‖)
    (a b : Fin 3) : secondPartial (mollifier ρ) a b t = 0 := by
  have h : mollifier ρ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_norm_gt ρ).mem_nhds ht) fun w hw =>
      mollifier_eq_zero hρ (le_of_lt hw)
  rw [secondPartial_congr h]
  simp [secondPartial]

theorem secondPartial_potential_mollifier_far {ρ : ℝ} (hρ : 0 < ρ) {z : Space} (hz : ρ < ‖z‖)
    (a b : Fin 3) : secondPartial (potential (mollifier ρ)) a b z = kernelSecondDeriv a b z := by
  have h : potential (mollifier ρ) =ᶠ[𝓝 z] kernel :=
    Filter.eventually_of_mem ((isOpen_norm_gt ρ).mem_nhds hz) fun w hw =>
      potential_mollifier_eq_kernel hρ (le_of_lt hw)
  rw [secondPartial_congr h, secondPartial_kernel]
  intro h0
  rw [h0, norm_zero] at hz
  linarith

theorem exists_abs_potential_mollifier_le : ∃ c : ℝ, ∀ ρ, 0 < ρ → ∀ z : Space, ‖z‖ ≤ ρ →
    |potential (mollifier ρ) z| ≤ c * ρ⁻¹ := by
  obtain ⟨C, hC⟩ := mollifier_le
  refine ⟨C * (4 * π)⁻¹ * (3 / 2 * volume.real (ball (0 : Space) 1) * 9), fun ρ hρ z hz => ?_⟩
  have := abs_potential_le (g := mollifier ρ) (A := C * ρ⁻¹ ^ 3) hρ
    (fun t => by rw [abs_of_nonneg (mollifier_nonneg hρ t)]; exact hC ρ hρ t)
    (fun t ht => mollifier_eq_zero hρ ht.le) hz
  refine this.trans (le_of_eq ?_)
  rw [integral_ballPow_one (by positivity)]
  field_simp
  ring

theorem exists_abs_secondPartial_potential_mollifier_le : ∃ c : ℝ, ∀ ρ, 0 < ρ → ∀ z : Space,
    ‖z‖ ≤ ρ → ∀ a b : Fin 3, |secondPartial (potential (mollifier ρ)) a b z| ≤ c * ρ⁻¹ ^ 3 := by
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_two_mollifier_le
  refine ⟨C * (4 * π)⁻¹ * (3 / 2 * volume.real (ball (0 : Space) 1) * 9), fun ρ hρ z hz a b => ?_⟩
  rw [secondPartial_potential (contDiff_mollifier ρ) (hasCompactSupport_mollifier hρ)]
  have := abs_potential_le (g := secondPartial (mollifier ρ) a b) (A := C * ρ⁻¹ ^ 5) hρ
    (fun t => (abs_secondPartial_le _ a b t).trans (hC ρ hρ t))
    (fun t ht => secondPartial_mollifier_eq_zero hρ ht a b) hz
  refine this.trans (le_of_eq ?_)
  rw [integral_ballPow_one (by positivity)]
  field_simp
  ring

theorem hasCompactSupport_secondPartial {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (i j : Fin 3) : HasCompactSupport (secondPartial f i j) := by
  rw [secondPartial_eq_fun hf]
  exact (hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _

theorem near_estimate {f K : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hK : Continuous K) {ρ c M : ℝ} (hρ : 0 < ρ) (hKeq : ∀ z, ρ ≤ ‖z‖ → K z = kernel z)
    (hKb : ∀ z : Space, ‖z‖ ≤ ρ → |K z| ≤ c * ρ⁻¹) (i j : Fin 3)
    (hM : ∀ y, |secondPartial f i j y| ≤ M) (x₀ : Space) :
    |(∫ y, secondPartial f i j y * kernel (x₀ - y)) - ∫ y, secondPartial f i j y * K (x₀ - y)| ≤
      M * (4 * π)⁻¹ * (3 / 2 * volume.real (ball (0 : Space) 1) * ρ ^ 2) +
        M * (c * ρ⁻¹) * (volume.real (ball (0 : Space) 1) * ρ ^ 3) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc0 : 0 ≤ c * ρ⁻¹ := (abs_nonneg _).trans (hKb 0 (by simp [hρ.le]))
  set d : Space → ℝ := fun y => secondPartial f i j y * (kernel (x₀ - y) - K (x₀ - y)) with hd
  have hBint : Integrable (fun y => secondPartial f i j y * K (x₀ - y)) :=
    integrable_mul_of_cpt (continuous_secondPartial hf i j) (hK.comp (continuous_const.sub
      continuous_id)) (Or.inl (hasCompactSupport_secondPartial hf hc i j))
  set g : Space → ℝ := fun y => M * (4 * π)⁻¹ * ballPow 1 ρ (x₀ - y) +
    M * (c * ρ⁻¹) * ballPow 0 ρ (x₀ - y) with hg
  have hgint : Integrable g :=
    (((integrable_ballPow (n := 1) (by norm_num) ρ).comp_sub_left x₀).const_mul _).add
      (((integrable_ballPow (n := 0) (by norm_num) ρ).comp_sub_left x₀).const_mul _)
  have hbound : ∀ y, ‖d y‖ ≤ g y := by
    intro y
    rw [Real.norm_eq_abs]
    by_cases hz : ρ ≤ ‖x₀ - y‖
    · simp only [hd, hKeq _ hz, sub_self, mul_zero, abs_zero, hg]
      exact add_nonneg (mul_nonneg (mul_nonneg hM0 (by positivity)) (ballPow_nonneg _ _ _))
        (mul_nonneg (mul_nonneg hM0 hc0) (ballPow_nonneg _ _ _))
    · have hz' := lt_of_not_ge hz
      simp only [hd, hg, ballPow_of_lt hz', pow_one, pow_zero, mul_one, abs_mul]
      have h1 : |kernel (x₀ - y) - K (x₀ - y)| ≤ (4 * π)⁻¹ * ‖x₀ - y‖⁻¹ + c * ρ⁻¹ := by
        refine (abs_sub _ _).trans (add_le_add (le_of_eq (abs_kernel _)) (hKb _ hz'.le))
      calc |secondPartial f i j y| * |kernel (x₀ - y) - K (x₀ - y)|
          ≤ M * ((4 * π)⁻¹ * ‖x₀ - y‖⁻¹ + c * ρ⁻¹) :=
            mul_le_mul (hM y) h1 (abs_nonneg _) hM0
        _ = _ := by ring
  have hdm : AEStronglyMeasurable d :=
    ((continuous_secondPartial hf i j).measurable.mul
      ((measurable_kernel.comp (measurable_const.sub measurable_id)).sub
        (hK.measurable.comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hdint : Integrable d := hgint.mono' hdm (Eventually.of_forall hbound)
  have hsplit : ∫ y, secondPartial f i j y * kernel (x₀ - y) =
      (∫ y, secondPartial f i j y * K (x₀ - y)) + ∫ y, d y := by
    rw [← integral_add hBint hdint]
    exact integral_congr_ae (ae_of_all _ fun y => by simp only [hd]; ring)
  rw [hsplit, add_sub_cancel_left, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [hg, integral_add (((integrable_ballPow (n := 1) (by norm_num) ρ).comp_sub_left x₀).const_mul _)
      (((integrable_ballPow (n := 0) (by norm_num) ρ).comp_sub_left x₀).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self (ballPow 1 ρ) volume x₀,
    integral_sub_left_eq_self (ballPow 0 ρ) volume x₀,
    integral_ballPow_one hρ, integral_ballPow_zero hρ]

theorem far_estimate {f H : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hH : Continuous H) {x₀ : Space} (h0 : f x₀ = 0) {ρ c L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hfL : ∀ y, |f y| ≤ L * ‖x₀ - y‖) (i j : Fin 3)
    (hHeq : ∀ z, ρ < ‖z‖ → H z = kernelSecondDeriv i j z)
    (hHb : ∀ z : Space, ‖z‖ ≤ ρ → |H z| ≤ c * ρ⁻¹ ^ 3) :
    |(∫ y, f y * H (x₀ - y)) - ∫ y, kernelSecondDeriv i j (x₀ - y) * f y| ≤
      L * ρ * (c * ρ⁻¹ ^ 3) * (volume.real (ball (0 : Space) 1) * (2 * ρ) ^ 3) +
        L * (3 * volume.real (ball (0 : Space) 1) * (2 * ρ)) := by
  have hc0 : 0 ≤ c * ρ⁻¹ ^ 3 := (abs_nonneg _).trans (hHb 0 (by simp [hρ.le]))
  have hAint : Integrable (fun y => f y * H (x₀ - y)) :=
    integrable_mul_of_cpt hf.continuous (hH.comp (continuous_const.sub continuous_id)) (Or.inl hc)
  have hsub : (∫ y, f y * H (x₀ - y)) - ∫ y, kernelSecondDeriv i j (x₀ - y) * f y =
      ∫ y, (f y * H (x₀ - y) - kernelSecondDeriv i j (x₀ - y) * f y) :=
    (integral_sub hAint (integrable_kernelSecondDeriv_mul_aux hf hc h0 i j)).symm
  rw [hsub, ← Real.norm_eq_abs]
  have h2ρ : 0 < 2 * ρ := by positivity
  set g : Space → ℝ := fun y => L * ρ * (c * ρ⁻¹ ^ 3) * ballPow 0 (2 * ρ) (x₀ - y) +
    L * ballPow 2 (2 * ρ) (x₀ - y) with hg
  have hi0 := ((integrable_ballPow (n := 0) (by norm_num) (2 * ρ)).comp_sub_left x₀).const_mul
    (L * ρ * (c * ρ⁻¹ ^ 3))
  have hi2 := ((integrable_ballPow (n := 2) le_rfl (2 * ρ)).comp_sub_left x₀).const_mul L
  have hgint : Integrable g := hi0.add hi2
  have hbound : ∀ y, ‖f y * H (x₀ - y) - kernelSecondDeriv i j (x₀ - y) * f y‖ ≤ g y := by
    intro y
    rw [Real.norm_eq_abs]
    by_cases hz : ρ < ‖x₀ - y‖
    · rw [hHeq _ hz, mul_comm, sub_self, abs_zero]
      exact add_nonneg (mul_nonneg (by positivity) (ballPow_nonneg _ _ _))
        (mul_nonneg hL (ballPow_nonneg _ _ _))
    · have hz' := le_of_not_gt hz
      have hz2 : ‖x₀ - y‖ < 2 * ρ := by linarith
      simp only [hg, ballPow_of_lt hz2, pow_zero, mul_one]
      refine (abs_sub _ _).trans (add_le_add ?_ (abs_kernelSecondDeriv_mul_le hfL i j y))
      rw [abs_mul]
      exact mul_le_mul ((hfL y).trans (mul_le_mul_of_nonneg_left hz' hL)) (hHb _ hz')
        (abs_nonneg _) (by positivity)
  refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [hg, integral_add hi0 hi2, integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self (ballPow 0 (2 * ρ)) volume x₀,
    integral_sub_left_eq_self (ballPow 2 (2 * ρ)) volume x₀,
    integral_ballPow_zero h2ρ, integral_ballPow_two h2ρ]

theorem eq_of_abs_sub_le {a b P Q : ℝ} (h : ∀ ρ : ℝ, 0 < ρ → |a - b| ≤ P * ρ ^ 2 + Q * ρ) :
    a = b := by
  have ht : Tendsto (fun ρ : ℝ => P * ρ ^ 2 + Q * ρ) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun ρ : ℝ => P * ρ ^ 2 + Q * ρ) := by fun_prop
    have := hcont.tendsto (0 : ℝ)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ρ hρ => h ρ hρ)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

end Breakdown.FundSol.Internal
