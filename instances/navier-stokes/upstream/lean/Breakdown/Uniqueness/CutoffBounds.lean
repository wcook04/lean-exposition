import Breakdown.Uniqueness.EnergyDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem radialCutoff_eq_one_aux {r : ℝ} (hr : 0 < r) {x : Space} (hx : ‖x‖ ≤ r) :
    radialCutoff r x = 1 := by
  unfold radialCutoff
  apply Real.smoothTransition.one_of_one_le
  have : ‖x‖ / r ≤ 1 := (div_le_one hr).2 hx
  linarith

theorem contDiff_radialCutoff {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (radialCutoff r) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have h : radialCutoff r =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      subst hx
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hr] with y hy
      exact radialCutoff_eq_one_aux hr (le_of_lt (by simpa using hy))
    exact contDiffAt_const.congr_of_eventuallyEq h
  · unfold radialCutoff
    exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub ((contDiffAt_norm ℝ hx).div_const r))

theorem radialCutoff_nonneg (r : ℝ) (x : Space) : 0 ≤ radialCutoff r x :=
  Real.smoothTransition.nonneg _

theorem radialCutoff_le_one (r : ℝ) (x : Space) : radialCutoff r x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem radialCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : Space} (hx : ‖x‖ ≤ r) :
    radialCutoff r x = 1 :=
  radialCutoff_eq_one_aux hr hx

theorem radialCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : Space} (hx : 2 * r ≤ ‖x‖) :
    radialCutoff r x = 0 := by
  unfold radialCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 ≤ ‖x‖ / r := (le_div_iff₀ hr).2 hx
  linarith

theorem hasCompactSupport_radialCutoff {r : ℝ} (hr : 0 < r) : HasCompactSupport (radialCutoff r) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
    have : 2 * r ≤ ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    exact radialCutoff_eq_zero hr this

private theorem radialCutoff_scale {r : ℝ} (hr : 0 < r) :
    radialCutoff r = radialCutoff 1 ∘ (r⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  funext x
  simp only [radialCutoff, Function.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_one]
  rw [div_eq_inv_mul]

private theorem norm_scaleMap_le {r : ℝ} (hr : 0 < r) :
    ‖r⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ r⁻¹ := by
  calc _ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ Space‖ := norm_smul_le _ _
    _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = r⁻¹ := mul_one _

private theorem differentiable_radialCutoff {r : ℝ} (hr : 0 < r) :
    Differentiable ℝ (radialCutoff r) :=
  (contDiff_radialCutoff hr).differentiable (by simp)

private theorem fderiv_bound_one : ∃ C : ℝ, ∀ y, ‖fderiv ℝ (radialCutoff 1) y‖ ≤ C :=
  ((contDiff_radialCutoff one_pos).continuous_fderiv (by simp)).bounded_above_of_compact_support
    (HasCompactSupport.fderiv (𝕜 := ℝ) (hasCompactSupport_radialCutoff one_pos))

theorem norm_fderiv_radialCutoff_le : ∃ c : ℝ, ∀ r, 0 < r → ∀ x,
    ‖fderiv ℝ (radialCutoff r) x‖ ≤ c / r := by
  obtain ⟨C, hC⟩ := fderiv_bound_one
  refine ⟨C, fun r hr x => ?_⟩
  have hd : DifferentiableAt ℝ (radialCutoff 1) ((r⁻¹ • ContinuousLinearMap.id ℝ Space) x) :=
    (differentiable_radialCutoff one_pos).differentiableAt
  rw [radialCutoff_scale hr, fderiv_comp x hd (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  calc _ ≤ ‖fderiv ℝ (radialCutoff 1) ((r⁻¹ • ContinuousLinearMap.id ℝ Space) x)‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ Space‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * r⁻¹ :=
        mul_le_mul (hC _) (norm_scaleMap_le hr) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
    _ = C / r := by rw [div_eq_mul_inv]

theorem abs_radialCutoff_sub_le : ∃ c : ℝ, ∀ r, 0 < r → ∀ x y,
    |radialCutoff r x - radialCutoff r y| ≤ c * ‖x - y‖ / r := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  refine ⟨c, fun r hr x y => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (differentiable_radialCutoff hr).differentiableAt)
    (fun z _ => hc r hr z) (mem_univ y) (mem_univ x)
  rw [← Real.norm_eq_abs]
  calc _ ≤ c / r * ‖x - y‖ := h
    _ = c * ‖x - y‖ / r := by ring

private theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem norm_gradientAt_le (p : Space → ℝ) (x : Space) :
    ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  unfold gradientAt
  calc _ ≤ ∑ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ p x‖ := by
        gcongr with i
        rw [norm_smul, norm_unitVector, mul_one]
        simpa [norm_unitVector] using (fderiv ℝ p x).le_opNorm (unitVector i)
    _ = 3 * ‖fderiv ℝ p x‖ := by simp

private theorem fderiv_cutoffPow {r : ℝ} (hr : 0 < r) (x : Space) :
    fderiv ℝ (cutoffPow r) x = (4 * radialCutoff r x ^ 3) • fderiv ℝ (radialCutoff r) x := by
  have h := ((differentiable_radialCutoff hr x).hasFDerivAt.pow 4).fderiv
  unfold cutoffPow
  rw [h]
  congr 1
  simp [nsmul_eq_mul]

theorem norm_gradient_cutoffPow_le : ∃ c : ℝ, ∀ r, 0 < r → ∀ x,
    ‖gradientAt (cutoffPow r) x‖ ≤ c / r * radialCutoff r x ^ 3 := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  refine ⟨12 * c, fun r hr x => ?_⟩
  have h3 : 0 ≤ radialCutoff r x ^ 3 := pow_nonneg (radialCutoff_nonneg r x) 3
  have h4 : 0 ≤ 3 * (4 * radialCutoff r x ^ 3) := by positivity
  calc _ ≤ 3 * ‖fderiv ℝ (cutoffPow r) x‖ := norm_gradientAt_le _ _
    _ = 3 * (4 * radialCutoff r x ^ 3) * ‖fderiv ℝ (radialCutoff r) x‖ := by
        rw [fderiv_cutoffPow hr, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by norm_num) h3)]
        ring
    _ ≤ 3 * (4 * radialCutoff r x ^ 3) * (c / r) := mul_le_mul_of_nonneg_left (hc r hr x) h4
    _ = 12 * c / r * radialCutoff r x ^ 3 := by ring

private theorem abs_scalarSumSecondPartials_le (θ : Space → ℝ) (x : Space) :
    |FundSol.scalarSumSecondPartials θ x| ≤ 3 * ‖iteratedFDeriv ℝ 2 θ x‖ := by
  unfold FundSol.scalarSumSecondPartials FundSol.secondPartial
  rw [← Real.norm_eq_abs]
  calc _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ 2 θ x ![unitVector i, unitVector i]‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 2 θ x‖ := by
        gcongr with i
        calc _ ≤ ‖iteratedFDeriv ℝ 2 θ x‖ *
              ∏ j, ‖(![unitVector i, unitVector i] : Fin 2 → Space) j‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = _ := by simp [Fin.prod_univ_two, norm_unitVector]
    _ = 3 * ‖iteratedFDeriv ℝ 2 θ x‖ := by simp

private theorem cutoffPow_scale {r : ℝ} (hr : 0 < r) :
    cutoffPow r = cutoffPow 1 ∘ (r⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  funext x
  simp only [cutoffPow, Function.comp_apply]
  rw [radialCutoff_scale hr, Function.comp_apply]

private theorem contDiff_cutoffPow {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (cutoffPow r) :=
  (contDiff_radialCutoff hr).pow 4

private theorem hasCompactSupport_cutoffPow {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (cutoffPow r) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
    have : 2 * r ≤ ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    simp [cutoffPow, radialCutoff_eq_zero hr this]

theorem abs_scalarSumSecondPartials_cutoffPow_le : ∃ c : ℝ, ∀ r, 0 < r → ∀ x,
    |FundSol.scalarSumSecondPartials (cutoffPow r) x| ≤ c / r ^ 2 := by
  obtain ⟨C, hC⟩ := ((contDiff_cutoffPow one_pos).continuous_iteratedFDeriv (m := 2)
    (by norm_cast)).bounded_above_of_compact_support
    ((hasCompactSupport_cutoffPow one_pos).iteratedFDeriv 2)
  refine ⟨3 * C, fun r hr x => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have key : ‖iteratedFDeriv ℝ 2 (cutoffPow r) x‖ ≤ C * r⁻¹ ^ 2 := by
    rw [cutoffPow_scale hr, ContinuousLinearMap.iteratedFDeriv_comp_right _
      (contDiff_cutoffPow one_pos) x (by norm_cast)]
    calc _ ≤ ‖iteratedFDeriv ℝ 2 (cutoffPow 1) ((r⁻¹ • ContinuousLinearMap.id ℝ Space) x)‖ *
          ∏ _i : Fin 2, ‖r⁻¹ • ContinuousLinearMap.id ℝ Space‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ C * r⁻¹ ^ 2 := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) (norm_scaleMap_le hr) 2)
            (by positivity) hC0
  calc _ ≤ 3 * ‖iteratedFDeriv ℝ 2 (cutoffPow r) x‖ := abs_scalarSumSecondPartials_le _ _
    _ ≤ 3 * (C * r⁻¹ ^ 2) := by linarith
    _ = 3 * C / r ^ 2 := by rw [inv_pow, div_eq_mul_inv]; ring

end Breakdown
