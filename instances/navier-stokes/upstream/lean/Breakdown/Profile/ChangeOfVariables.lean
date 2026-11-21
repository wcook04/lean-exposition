import Breakdown.Profile.StatementsFlow

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem expShift_hasDerivAt (s₀ σ : ℝ) :
    HasDerivAt (fun x : ℝ => 1 - exp (-(x - s₀))) (exp (-(σ - s₀))) σ := by
  have h : HasDerivAt (fun x : ℝ => 1 - exp (-(x - s₀))) (-(exp (-(σ - s₀)) * -1)) σ :=
    (((hasDerivAt_id' σ).sub_const s₀).neg.exp).const_sub 1
  exact h.congr_deriv (by ring)

private theorem expShift_image (s₀ s : ℝ) :
    (fun x : ℝ => 1 - exp (-(x - s₀))) '' Ioc s₀ s = Ioc 0 (1 - exp (-(s - s₀))) := by
  ext r
  constructor
  · rintro ⟨σ, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : exp (-(σ - s₀)) < exp 0 := exp_lt_exp.mpr (by linarith)
      rw [exp_zero] at this
      linarith
    · have : exp (-(s - s₀)) ≤ exp (-(σ - s₀)) := exp_le_exp.mpr (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    have hpos : 0 < 1 - r := by
      have := exp_pos (-(s - s₀))
      linarith
    refine ⟨s₀ - Real.log (1 - r), ⟨?_, ?_⟩, ?_⟩
    · have : Real.log (1 - r) < 0 := Real.log_neg hpos (by linarith)
      linarith
    · have : -(s - s₀) ≤ Real.log (1 - r) := by
        rw [Real.le_log_iff_exp_le hpos]
        linarith
      linarith
    · simp only
      rw [show -(s₀ - Real.log (1 - r) - s₀) = Real.log (1 - r) by ring, Real.exp_log hpos]
      ring

theorem expChangeOfVariables_holds : ExpChangeOfVariables := by
  intro E _ _ _ g s₀ s hs hg
  have hT : 0 ≤ 1 - exp (-(s - s₀)) := by
    have : exp (-(s - s₀)) ≤ exp 0 := exp_le_exp.mpr (by linarith)
    rw [exp_zero] at this
    linarith
  have hder : ∀ x ∈ Ioc s₀ s, HasDerivWithinAt (fun x : ℝ => 1 - exp (-(x - s₀)))
      (exp (-(x - s₀))) (Ioc s₀ s) x := fun x _ => (expShift_hasDerivAt s₀ x).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => 1 - exp (-(x - s₀))) (Ioc s₀ s) := by
    intro x _ y _ hxy
    have h : exp (-(x - s₀)) = exp (-(y - s₀)) := by
      simp only at hxy
      linarith
    have := Real.exp_injective h
    linarith
  have habs : ∀ x : ℝ, |exp (-(x - s₀))| = exp (-(x - s₀)) := fun x => abs_of_pos (exp_pos _)
  have himg := expShift_image s₀ s
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hder hinj g
  have key2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hder hinj g
  simp only [habs] at key key2
  rw [himg] at key key2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hg
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    exact key.mp hg
  · rw [intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hT, key2]

end Breakdown
