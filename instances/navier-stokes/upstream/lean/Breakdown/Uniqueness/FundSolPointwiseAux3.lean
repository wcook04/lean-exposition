import Breakdown.Uniqueness.FundSolPointwiseAux2
import Breakdown.Uniqueness.FundSolMeanValue

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.FundSol.Internal

theorem measurable_kernel : Measurable kernel := by
  unfold kernel
  exact measurable_const.mul measurable_norm.inv

theorem measurable_kernelSecondDeriv (i j : Fin 3) : Measurable (kernelSecondDeriv i j) := by
  unfold kernelSecondDeriv
  have hc : ∀ k : Fin 3, Measurable (fun z : Space => z k) := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable
  exact measurable_const.mul ((measurable_const.mul (measurable_norm.inv.pow_const 3)).sub
    (((measurable_const.mul (hc i)).mul (hc j)).mul (measurable_norm.inv.pow_const 5)))

theorem kernelSecondDeriv_symm (i j : Fin 3) (z : Space) : kernelSecondDeriv j i z = kernelSecondDeriv i j z := by
  unfold kernelSecondDeriv
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg (Ne.symm h), if_neg h]; ring

theorem exists_slope_bound {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {x₀ : Space} (h0 : f x₀ = 0) : ∃ L, 0 ≤ L ∧ ∀ y, |f y| ≤ L * ‖x₀ - y‖ := by
  obtain ⟨L, hL⟩ := (contDiff_infty_iff_fderiv.1 hf).2.continuous.bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  refine ⟨L, (norm_nonneg _).trans (hL 0), fun y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => differentiable_of_smooth hf x) (fun x _ => hL x) (mem_univ x₀) (mem_univ y)
  rw [h0, sub_zero, Real.norm_eq_abs] at this
  rwa [norm_sub_rev]

theorem secondPartial_eq_fun {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (a b : Fin 3) :
    secondPartial h a b = fun y => fderiv ℝ (fun y => fderiv ℝ h y (unitVector b)) y (unitVector a) := by
  ext y; exact secondPartial_eq_dir hh a b y

theorem continuous_secondPartial {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (a b : Fin 3) :
    Continuous (secondPartial h a b) := by
  rw [secondPartial_eq_fun hh]
  exact (smooth_dir (smooth_dir hh _) _).continuous

theorem exists_secondPartial_bound {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (i j : Fin 3) : ∃ M, ∀ y, |secondPartial f i j y| ≤ M := by
  have hcs : HasCompactSupport (secondPartial f i j) := by
    rw [secondPartial_eq_fun hf]
    exact (hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
  obtain ⟨M, hM⟩ := (continuous_secondPartial hf i j).bounded_above_of_compact_support hcs
  exact ⟨M, fun y => by rw [← Real.norm_eq_abs]; exact hM y⟩

theorem abs_kernelSecondDeriv_mul_le {f : Space → ℝ} {L : ℝ} {x₀ : Space}
    (hfL : ∀ y, |f y| ≤ L * ‖x₀ - y‖) (i j : Fin 3) (y : Space) :
    |kernelSecondDeriv i j (x₀ - y) * f y| ≤ L * ‖x₀ - y‖⁻¹ ^ 2 := by
  rw [abs_mul]
  calc |kernelSecondDeriv i j (x₀ - y)| * |f y| ≤ ‖x₀ - y‖⁻¹ ^ 3 * (L * ‖x₀ - y‖) :=
        mul_le_mul (abs_kernelSecondDeriv_le i j _) (hfL y) (abs_nonneg _) (by positivity)
    _ = L * ‖x₀ - y‖⁻¹ ^ 2 := by rw [mul_left_comm, inv_pow_three_mul]

theorem integrable_kernelSecondDeriv_mul_aux {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {x₀ : Space} (h0 : f x₀ = 0) (i j : Fin 3) :
    Integrable (fun y => kernelSecondDeriv i j (x₀ - y) * f y) := by
  obtain ⟨L, hL, hfL⟩ := exists_slope_bound hf hc h0
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall x₀
  set R' := max R 0 + 1 with hR'
  refine Integrable.mono' (((integrable_ballPow (n := 2) le_rfl R').comp_sub_left x₀).const_mul L)
    (((measurable_kernelSecondDeriv i j).comp (measurable_const.sub measurable_id)).mul
      hf.continuous.measurable).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy : y ∈ tsupport f
  · have h1 : ‖x₀ - y‖ < R' := by
      have := hR hy
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at this
      linarith [le_max_left R 0]
    rw [ballPow_of_lt h1]
    exact abs_kernelSecondDeriv_mul_le hfL i j y
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, abs_zero]
    exact mul_nonneg hL (ballPow_nonneg _ _ _)

end Breakdown.FundSol.Internal
