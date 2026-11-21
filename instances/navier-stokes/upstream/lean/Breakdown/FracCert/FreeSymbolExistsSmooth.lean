import Breakdown.FracCert.FreeSymbolExistsParts
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolSmoothInternal

theorem ofReal_smooth : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff

theorem rot_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℝ} {g : X → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x => axialRotationFormula (f x) (g x)) := by
  have hz : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => g x i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hg
  have hc : ContDiff ℝ ∞ (fun x => Real.cos (f x)) := Real.contDiff_cos.comp hf
  have hs : ContDiff ℝ ∞ (fun x => Real.sin (f x)) := Real.contDiff_sin.comp hf
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simp only [axialRotationFormula]
    simpa using (hc.mul (hz 0)).sub (hs.mul (hz 1))
  · simp only [axialRotationFormula]
    simpa using (hs.mul (hz 0)).add (hc.mul (hz 1))
  · simp only [axialRotationFormula]
    simpa using hz 2

theorem rotC_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℝ} {g : X → Freq.CSpace}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x => axialRotationC (f x) (g x)) := by
  have hc : ContDiff ℝ ∞ (fun x => ((Real.cos (f x) : ℝ) : ℂ)) := ofReal_smooth.comp (Real.contDiff_cos.comp hf)
  have hs : ContDiff ℝ ∞ (fun x => ((Real.sin (f x) : ℝ) : ℂ)) := ofReal_smooth.comp (Real.contDiff_sin.comp hf)
  have hz : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => g x i) := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff.comp hg
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simp only [axialRotationC]
    simpa using (hc.mul (hz 0)).sub (hs.mul (hz 1))
  · simp only [axialRotationC]
    simpa using (hs.mul (hz 0)).add (hc.mul (hz 1))
  · simp only [axialRotationC]
    simpa using hz 2

theorem pow_smoothAt (p : ℝ) {ξ : Space} (hξ : ξ ≠ 0) : ContDiffAt ℝ ∞ (freqPow p) ξ := by
  have h1 : ContDiffAt ℝ ∞ (fun η : Space => 2 * π * ‖η‖) ξ := contDiffAt_const.mul (contDiffAt_norm ℝ hξ)
  have h2 : 2 * π * ‖ξ‖ ≠ 0 := by positivity
  exact h1.rpow_const_of_ne h2

def damped (α : ℝ) (s : Space → Freq.CSpace) (η : Space) : Freq.CSpace :=
  Real.exp (-freqPow (2 * α) η) • s η

theorem damped_smooth (α : ℝ) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ContDiff ℝ ∞ (damped α s) := by
  obtain ⟨r, hr, hr0⟩ := hs.2.2.1
  refine contDiff_iff_contDiffAt.2 fun ξ => ?_
  by_cases hξ : ‖ξ‖ < r
  · refine (contDiffAt_const (c := (0 : Freq.CSpace))).congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hξ)) fun η hη => ?_
    simp [damped, hr0 η (mem_ball_zero_iff.1 hη)]
  · have h0 : ξ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hξ
      exact hξ hr
    exact ((Real.contDiff_exp.contDiffAt).comp ξ (pow_smoothAt (2 * α) h0).neg).smul hs.1.contDiffAt

def kernel (α a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) (τ : ℝ) : Freq.CSpace :=
  Real.exp (-((1 - 2 / α) * τ)) •
    axialRotationC (a * τ) (damped α s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ))

theorem kernel_smooth (α a : ℝ) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ContDiff ℝ ∞ (fun p : Space × ℝ => kernel α a s p.1 p.2) := by
  unfold kernel
  have hθ : ContDiff ℝ ∞ (fun p : Space × ℝ => a * p.2) := contDiff_const.mul contDiff_snd
  have hr : ContDiff ℝ ∞ (fun p : Space × ℝ => axialRotationFormula (-(a * p.2)) p.1) :=
    rot_comp hθ.neg contDiff_fst
  have he : ContDiff ℝ ∞ (fun p : Space × ℝ => Real.exp (p.2 / (2 * α))) :=
    Real.contDiff_exp.comp (contDiff_snd.div_const _)
  have hη : ContDiff ℝ ∞ (fun p : Space × ℝ => Real.exp (p.2 / (2 * α)) • axialRotationFormula (-(a * p.2)) p.1) :=
    he.smul hr
  have hd : ContDiff ℝ ∞ (fun p : Space × ℝ =>
      damped α s (Real.exp (p.2 / (2 * α)) • axialRotationFormula (-(a * p.2)) p.1)) :=
    (damped_smooth α hs).comp hη
  have hc : ContDiff ℝ ∞ (fun p : Space × ℝ => axialRotationC (a * p.2)
      (damped α s (Real.exp (p.2 / (2 * α)) • axialRotationFormula (-(a * p.2)) p.1))) :=
    rotC_comp hθ hd
  have hw : ContDiff ℝ ∞ (fun p : Space × ℝ => Real.exp (-((1 - 2 / α) * p.2))) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd).neg
  exact hw.smul hc

theorem rotC_smul (θ c : ℝ) (z : Freq.CSpace) : axialRotationC θ (c • z) = c • axialRotationC θ z := by
  ext i
  fin_cases i <;> simp [axialRotationC] <;> ring

theorem rot_norm' (θ : ℝ) (y : Space) : ‖axialRotationFormula θ y‖ = ‖y‖ := by
  have h0 : axialRotationFormula θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 := by simp [axialRotationFormula]
  have h1 : axialRotationFormula θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 := by simp [axialRotationFormula]
  have h2 : axialRotationFormula θ y 2 = y 2 := by simp [axialRotationFormula]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, h0, h1, h2]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem pow_scale {α : ℝ} (hα : 0 < α) (τ θ : ℝ) (ξ : Space) :
    freqPow (2 * α) (Real.exp (τ / (2 * α)) • axialRotationFormula θ ξ) = Real.exp τ * freqPow (2 * α) ξ := by
  unfold freqPow
  rw [norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show 2 * π * (Real.exp (τ / (2 * α)) * ‖ξ‖) = Real.exp (τ / (2 * α)) * (2 * π * ‖ξ‖) by ring]
  rw [Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
  congr 2
  field_simp

theorem integrand_eq {α : ℝ} (hα : 0 < α) (a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) (τ : ℝ) :
    freeWeight α τ ξ • axialRotationC (a * τ) (s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ)) =
      Real.exp (freqPow (2 * α) ξ) • kernel α a s ξ τ := by
  unfold kernel damped freeWeight
  rw [pow_scale hα, rotC_smul, smul_smul, smul_smul]
  congr 1
  simp only [← Real.exp_add]
  congr 1
  ring

theorem solution_eq {α : ℝ} (hα : 0 < α) (a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) :
    freeSolution α a s ξ = Real.exp (freqPow (2 * α) ξ) • ∫ τ in Set.Ioi (0 : ℝ), kernel α a s ξ τ := by
  unfold freeSolution
  simp_rw [integrand_eq hα]
  exact integral_smul _ _

theorem kernel_far {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ : Space, ∀ ε : ℝ, 0 < ε → ε < ‖ξ‖ → ∀ τ : ℝ, 2 * α * (R / ε) < τ →
      kernel α a s ξ τ = 0 := by
  obtain ⟨R0, hR0⟩ := hs.2.1.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun ξ ε hε hξ τ hτ => ?_⟩
  have hq : max R0 1 / ε < τ / (2 * α) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have he : max R0 1 / ε ≤ Real.exp (τ / (2 * α)) :=
    le_trans (le_trans (by linarith) (Real.add_one_le_exp (max R0 1 / ε))) (Real.exp_le_exp.2 hq.le)
  have hn : R0 < ‖Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ‖ := by
    rw [norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : max R0 1 = max R0 1 / ε * ε := by field_simp
    have h2 : max R0 1 / ε * ε < Real.exp (τ / (2 * α)) * ‖ξ‖ := by
      calc max R0 1 / ε * ε ≤ Real.exp (τ / (2 * α)) * ε := mul_le_mul_of_nonneg_right he hε.le
        _ < Real.exp (τ / (2 * α)) * ‖ξ‖ := mul_lt_mul_of_pos_left hξ (Real.exp_pos _)
    linarith [le_max_left R0 1]
  have hz : s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hR0 hm
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  simp [kernel, damped, hz]
  ext i
  fin_cases i <;> simp [axialRotationC]

theorem solution_smooth {α : ℝ} (hα : 0 < α) (a : ℝ) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ContDiffOn ℝ ∞ (freeSolution α a s) {ξ | ξ ≠ 0} := by
  obtain ⟨R, hR, hfar⟩ := kernel_far (a := a) hα hs
  intro ξ0 hξ0
  have hξ0' : ξ0 ≠ 0 := hξ0
  set ε : ℝ := ‖ξ0‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set T : ℝ := 2 * α * (R / ε) with hT
  have hT0 : 0 ≤ T := by positivity
  have hint : ContDiff ℝ ∞ (fun ξ => ∫ τ in (0 : ℝ)..T, kernel α a s ξ τ) :=
    contDiff_infty.2 fun n => Coercive.StretchInternal.contDiff_intervalIntegral_param 0 T n
      (kernel α a s) ((kernel_smooth α a hs).of_le (by exact_mod_cast le_top))
  have hloc : (fun ξ => ∫ τ in Set.Ioi (0 : ℝ), kernel α a s ξ τ) =ᶠ[nhds ξ0]
      fun ξ => ∫ τ in (0 : ℝ)..T, kernel α a s ξ τ := by
    have hopen : IsOpen {ξ : Space | ε < ‖ξ‖} := isOpen_lt continuous_const continuous_norm
    have hmem : ξ0 ∈ {ξ : Space | ε < ‖ξ‖} := by
      show ε < ‖ξ0‖
      have : 0 < ‖ξ0‖ := norm_pos_iff.2 hξ0'
      linarith
    refine Filter.eventually_of_mem (hopen.mem_nhds hmem) fun ξ hξ => ?_
    dsimp only
    rw [intervalIntegral.integral_of_le hT0]
    refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume) (f := fun τ => kernel α a s ξ τ)
      (measurableSet_Ioi (a := (0 : ℝ))).nullMeasurableSet
      (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) T ⊆ Set.Ioi 0) (Filter.Eventually.of_forall fun τ hτ => ?_))
    have hτT : T < τ := by
      by_contra h
      exact hτ.2 ⟨hτ.1, le_of_not_gt h⟩
    exact hfar ξ ε hεpos hξ τ hτT
  have hw : freeSolution α a s = fun ξ => Real.exp (freqPow (2 * α) ξ) • ∫ τ in Set.Ioi (0 : ℝ), kernel α a s ξ τ :=
    funext (solution_eq hα a s)
  rw [hw]
  refine ContDiffAt.contDiffWithinAt ?_
  exact ((Real.contDiff_exp.contDiffAt).comp ξ0 (pow_smoothAt (2 * α) hξ0')).smul
    (hint.contDiffAt.congr_of_eventuallyEq hloc)

end FreeSymbolSmoothInternal

theorem freeSolutionSmooth : FreeSolutionSmoothStatement := fun _ hα1 _ a _ hs =>
  FreeSymbolSmoothInternal.solution_smooth (by linarith) a hs

end SteadyCert

end Breakdown
