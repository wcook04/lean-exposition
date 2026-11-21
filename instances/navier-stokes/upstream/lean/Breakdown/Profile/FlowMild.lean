import Breakdown.Profile.StatementsFlow

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem flowOfMild_holds (hker : KernelDilate) (hcov : ExpChangeOfVariables) : FlowOfMild := by
  intro X _ _ _ F w u s₀ s hs hmild hu
  have ha0 : 0 < exp (-(s - s₀)) := exp_pos _
  have ha1 : exp (-(s - s₀)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(s - s₀) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hTmem : (1 - exp (-(s - s₀))) ∈ Icc (0 : ℝ) (1 - exp (-(s - s₀))) :=
    ⟨by linarith, le_rfl⟩
  obtain ⟨hint, heq⟩ := hmild.2 _ hTmem
  have hu0 : u 0 = w s₀ := by
    rw [hu 0 ⟨le_rfl, by linarith⟩]
    simp [F.D_one]
  have huT : u (1 - exp (-(s - s₀))) = F.D (exp (-(s - s₀)))⁻¹ (w s) := by
    rw [hu _ hTmem, show 1 - (1 - exp (-(s - s₀))) = exp (-(s - s₀)) by ring, Real.log_exp,
      show s₀ - -(s - s₀) = s by ring]
  have hDinv : ∀ c : ℝ, 0 < c → ∀ y : X, F.D c (F.D c⁻¹ y) = y := by
    intro c hc y
    rw [← ContinuousLinearMap.comp_apply, ← F.D_mul c c⁻¹ hc (inv_pos.mpr hc),
      mul_inv_cancel₀ hc.ne', F.D_one]
    rfl
  have hws : w s = F.D (exp (-(s - s₀))) (u (1 - exp (-(s - s₀)))) := by
    rw [huT, hDinv _ ha0]
  have hint' : IntervalIntegrable (fun r => F.D (exp (-(s - s₀)))
      (F.K ((1 - exp (-(s - s₀))) - r) (u r) (u r))) volume 0 (1 - exp (-(s - s₀))) :=
    ⟨(F.D _).integrable_comp hint.1, (F.D _).integrable_comp hint.2⟩
  have hcomm : (∫ r in (0 : ℝ)..(1 - exp (-(s - s₀))), F.D (exp (-(s - s₀)))
      (F.K ((1 - exp (-(s - s₀))) - r) (u r) (u r))) =
      F.D (exp (-(s - s₀))) (∫ r in (0 : ℝ)..(1 - exp (-(s - s₀))),
        F.K ((1 - exp (-(s - s₀))) - r) (u r) (u r)) :=
    (F.D _).intervalIntegral_comp_comm hint
  obtain ⟨hcI, hcE⟩ := hcov X _ s₀ s hs hint'
  have key : ∀ σ, s₀ ≤ σ → σ < s →
      exp (-(σ - s₀)) • F.D (exp (-(s - s₀))) (F.K ((1 - exp (-(s - s₀))) -
        (1 - exp (-(σ - s₀)))) (u (1 - exp (-(σ - s₀)))) (u (1 - exp (-(σ - s₀))))) =
        F.Ks (s - σ) (w σ) (w σ) := by
    intro σ h1 h2
    have hb0 : 0 < exp (-(σ - s₀)) := exp_pos _
    have hmem : 1 - exp (-(σ - s₀)) ∈ Icc (0 : ℝ) (1 - exp (-(s - s₀))) := by
      constructor
      · have h := Real.exp_le_exp.mpr (show -(σ - s₀) ≤ 0 by linarith)
        rw [Real.exp_zero] at h
        linarith
      · have h := Real.exp_le_exp.mpr (show -(s - s₀) ≤ -(σ - s₀) by linarith)
        linarith
    have huσ : u (1 - exp (-(σ - s₀))) = F.D (exp (-(σ - s₀)))⁻¹ (w σ) := by
      rw [hu _ hmem, show 1 - (1 - exp (-(σ - s₀))) = exp (-(σ - s₀)) by ring, Real.log_exp,
        show s₀ - -(σ - s₀) = σ by ring]
    have hτ : 0 < 1 - exp (-(s - σ)) := by
      have h := Real.exp_lt_exp.mpr (show -(s - σ) < 0 by linarith)
      rw [Real.exp_zero] at h
      linarith
    have hsplit : (1 - exp (-(s - s₀))) - (1 - exp (-(σ - s₀))) =
        exp (-(σ - s₀)) * (1 - exp (-(s - σ))) := by
      have h : -(σ - s₀) + -(s - σ) = -(s - s₀) := by ring
      rw [mul_sub, mul_one, ← Real.exp_add, h]
      ring
    have hratio : exp (-(s - s₀)) * (exp (-(σ - s₀)))⁻¹ = exp (-(s - σ)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [MildFramework.Ks, huσ, hsplit, hker X F _ _ _ (w σ) ha0 hb0 hτ, hratio, smul_smul,
      mul_inv_cancel₀ hb0.ne', one_smul]
  have hae : ∀ᵐ σ ∂volume, σ ∈ uIoc s₀ s →
      exp (-(σ - s₀)) • F.D (exp (-(s - s₀))) (F.K ((1 - exp (-(s - s₀))) -
        (1 - exp (-(σ - s₀)))) (u (1 - exp (-(σ - s₀)))) (u (1 - exp (-(σ - s₀))))) =
        F.Ks (s - σ) (w σ) (w σ) := by
    filter_upwards [Measure.ae_ne volume s] with σ hσ hmem
    rw [uIoc_of_le hs.le] at hmem
    exact key σ hmem.1.le (lt_of_le_of_ne hmem.2 hσ)
  refine ⟨hcI.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae), ?_⟩
  have hI := (intervalIntegral.integral_congr_ae hae).symm.trans hcE
  rw [hI, hcomm, hws, heq, map_add, sub_zero, hu0]
  rfl

end Breakdown
