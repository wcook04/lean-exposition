import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FundSol.Internal

theorem scalarSumSecondPartials_congr_nhds {θ₁ θ₂ : Space → ℝ} {x : Space} (h : θ₁ =ᶠ[𝓝 x] θ₂) :
    scalarSumSecondPartials θ₁ x = scalarSumSecondPartials θ₂ x := by
  simp only [scalarSumSecondPartials, secondPartial, (h.iteratedFDeriv ℝ 2).eq_of_nhds]

theorem scalarSumSecondPartials_comp_norm_sq {φ : ℝ → ℝ} {x : Space}
    (h1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ (‖y‖ ^ 2))
    (h2 : DifferentiableAt ℝ (deriv φ) (‖x‖ ^ 2)) :
    scalarSumSecondPartials (fun y => φ (‖y‖ ^ 2)) x =
      6 * deriv φ (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * deriv (deriv φ) (‖x‖ ^ 2) := by
  have hq : ∀ y : Space, HasFDerivAt (fun y : Space => ‖y‖ ^ 2) ((2 : ℕ) • innerSL ℝ y) y :=
    fun y => (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hD : (fderiv ℝ fun y : Space => φ (‖y‖ ^ 2)) =ᶠ[𝓝 x]
      fun y => (2 * deriv φ (‖y‖ ^ 2)) • innerSL ℝ y := by
    filter_upwards [h1] with y hy
    have h3 : HasFDerivAt (fun y : Space => φ (‖y‖ ^ 2)) (deriv φ (‖y‖ ^ 2) • (2 : ℕ) • innerSL ℝ y) y :=
      hy.hasDerivAt.comp_hasFDerivAt y (hq y)
    rw [h3.fderiv]
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hc := (h2.hasDerivAt.comp_hasFDerivAt x (hq x)).const_mul 2
  have hE := hc.smul (innerSL ℝ (E := Space)).hasFDerivAt
  have key : ∀ v : Space, iteratedFDeriv ℝ 2 (fun y => φ (‖y‖ ^ 2)) x ![v, v] =
      2 * deriv φ (‖x‖ ^ 2) * inner ℝ v v + 4 * deriv (deriv φ) (‖x‖ ^ 2) * inner ℝ x v ^ 2 := by
    intro v
    rw [iteratedFDeriv_two_apply, hD.fderiv_eq]
    have hE' : HasFDerivAt (fun y => (2 * deriv φ (‖y‖ ^ 2)) • innerSL ℝ y) _ x := hE
    rw [hE'.fderiv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply, Function.comp_apply]
    push_cast
    have hin : ∀ a b : Space, innerSL ℝ a b = inner ℝ a b := fun a b => rfl
    simp only [hin]
    ring
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp
  simp only [scalarSumSecondPartials, secondPartial, key, Fin.sum_univ_three, unitVector,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp only [map_one, one_mul, mul_one, EuclideanSpace.single_apply, if_true]
  rw [hn]
  simp
  ring

theorem eq_add_div_sqrt_of_radial_ode {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hφ : ContDiffOn ℝ 2 φ (Ioi a))
    (h : ∀ s > a, 6 * deriv φ s + 4 * s * deriv (deriv φ) s = 0) :
    ∃ A B : ℝ, ∀ s > a, φ s = A + B / √s := by
  have hU : IsOpen (Ioi a) := isOpen_Ioi
  have hpre : IsPreconnected (Ioi a) := isPreconnected_Ioi
  have hd1 : ∀ s > a, DifferentiableAt ℝ φ s := fun s hs =>
    (hφ.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)
  have hd2 : ∀ s > a, DifferentiableAt ℝ (deriv φ) s := fun s hs =>
    ((hφ.deriv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hs)).differentiableAt (by norm_num)
  have hsq : ∀ s > a, HasDerivAt (fun t => √t) (1 / (2 * √s)) s := fun s hs =>
    Real.hasDerivAt_sqrt (ne_of_gt (lt_of_le_of_lt ha hs))
  have hψ : ∀ s > a, HasDerivAt (fun t => t * √t * deriv φ t)
      (√s / 4 * (6 * deriv φ s + 4 * s * deriv (deriv φ) s)) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ha hs
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := ((hasDerivAt_id s).mul (hsq s hs)).mul (hd2 s hs).hasDerivAt
    refine this.congr_deriv ?_
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    simp only [Pi.mul_apply, id_eq]
    generalize √s = r at hrs hr ⊢
    subst hrs
    field_simp
    ring
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s > a, s * √s * deriv φ s = b :=
    ⟨_, fun s hs => hU.is_const_of_deriv_eq_zero hpre
      (fun t ht => (hψ t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => by simp [(hψ t ht).deriv, h t ht]) hs
      (show a + 1 ∈ Ioi a by simp)⟩
  have hχ : ∀ s > a, HasDerivAt (fun t => φ t + 2 * b * (√t)⁻¹) 0 s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ha hs
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := (hd1 s hs).hasDerivAt.add (((hsq s hs).inv hr.ne').const_mul (2 * b))
    refine this.congr_deriv ?_
    rw [← hb s hs]
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    generalize √s = r at hrs hr ⊢
    subst hrs
    field_simp
    ring
  refine ⟨φ (a + 1) + 2 * b * (√(a + 1))⁻¹, -2 * b, fun s hs => ?_⟩
  have := hU.is_const_of_deriv_eq_zero hpre (f := fun t => φ t + 2 * b * (√t)⁻¹)
    (fun t ht => (hχ t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by simp [(hχ t ht).deriv]) hs (show a + 1 ∈ Ioi a by simp)
  rw [div_eq_mul_inv]
  linarith

theorem eq_zero_of_abs_add_div_sqrt_le {A B C S : ℝ}
    (h : ∀ s ≥ S, |A + B / √s| ≤ C / s) : A = 0 ∧ B = 0 := by
  have hC : Tendsto (fun s : ℝ => C / s) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun s : ℝ => A + B / √s) atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop S).mono fun s hs => by
      rw [Real.norm_eq_abs]; exact h s hs) hC
  have h2 : Tendsto (fun s : ℝ => A + B / √s) atTop (𝓝 (A + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop)
  have hA : A = 0 := by simpa using tendsto_nhds_unique h2 h1
  subst hA
  have hC' : Tendsto (fun s : ℝ => C / √s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h3 : Tendsto (fun _ : ℝ => B) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hC'
    filter_upwards [eventually_ge_atTop (max S 1)] with s hs
    have hs1 : 1 ≤ s := le_of_max_le_right hs
    have hsS : S ≤ s := le_of_max_le_left hs
    have hs0 : 0 < s := by linarith
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := h s hsS
    rw [zero_add, abs_div, abs_of_pos hr, div_le_div_iff₀ hr hs0] at this
    rw [Real.norm_eq_abs, le_div_iff₀ hr]
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    nlinarith [abs_nonneg B]
  exact ⟨rfl, tendsto_nhds_unique tendsto_const_nhds h3⟩

end Breakdown.FundSol.Internal
