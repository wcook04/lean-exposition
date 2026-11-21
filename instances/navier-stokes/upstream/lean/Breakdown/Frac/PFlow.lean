import Breakdown.Frac.StProfile
import Breakdown.Profile.ChangeOfVariables

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem scaledDilateJointContinuous : ScaledDilateJointContinuous := by
  intro X _ _ _ κ F
  rintro ⟨μ₀, x₀⟩ ⟨hμ₀, -⟩
  have hμ₀' : 0 < μ₀ := hμ₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hc : ContinuousAt (fun μ => F.D μ x₀) μ₀ :=
    (F.D_cont x₀).continuousAt (Ioi_mem_nhds hμ₀')
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  have hp : ContinuousAt (fun μ : ℝ => μ ^ κ) μ₀ :=
    Real.continuousAt_rpow_const μ₀ κ (Or.inl hμ₀'.ne')
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.mp hp 1 one_pos
  have hM0 : 0 ≤ μ₀ ^ κ := Real.rpow_nonneg hμ₀'.le _
  have hM1 : 0 < μ₀ ^ κ + 1 := by linarith
  refine ⟨min (min δ₁ (min μ₀ δ₂)) (ε / (2 * (μ₀ ^ κ + 1))),
    lt_min (lt_min hδ₁ (lt_min hμ₀' hδ₂)) (div_pos hε (by linarith)), ?_⟩
  rintro ⟨μ, x⟩ hd
  rw [Prod.dist_eq] at hd
  have hd1 : dist μ μ₀ < min (min δ₁ (min μ₀ δ₂)) (ε / (2 * (μ₀ ^ κ + 1))) :=
    lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist x x₀ < min (min δ₁ (min μ₀ δ₂)) (ε / (2 * (μ₀ ^ κ + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) hd
  have hd1' : dist μ μ₀ < min δ₁ (min μ₀ δ₂) := lt_of_lt_of_le hd1 (min_le_left _ _)
  have hμδ : dist μ μ₀ < δ₁ := lt_of_lt_of_le hd1' (min_le_left _ _)
  have hμμ : dist μ μ₀ < μ₀ :=
    lt_of_lt_of_le hd1' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hμδ₂ : dist μ μ₀ < δ₂ :=
    lt_of_lt_of_le hd1' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxε : dist x x₀ < ε / (2 * (μ₀ ^ κ + 1)) :=
    lt_of_lt_of_le hd2 (min_le_right _ _)
  have hpow' := h₂ hμδ₂
  rw [Real.dist_eq, abs_lt] at hpow'
  have hpow : μ ^ κ ≤ μ₀ ^ κ + 1 := by linarith [hpow'.2]
  rw [Real.dist_eq, abs_lt] at hμμ
  have hμpos : 0 < μ := by linarith [hμμ.1]
  rw [dist_eq_norm] at hxε
  have hA : ‖F.D μ (x - x₀)‖ < ε / 2 := by
    rw [F.D_norm μ hμpos]
    calc μ ^ κ * ‖x - x₀‖ ≤ (μ₀ ^ κ + 1) * ‖x - x₀‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ < (μ₀ ^ κ + 1) * (ε / (2 * (μ₀ ^ κ + 1))) :=
          mul_lt_mul_of_pos_left hxε hM1
      _ = ε / 2 := by field_simp
  have hB : dist (F.D μ x₀) (F.D μ₀ x₀) < ε / 2 := h₁ hμδ
  rw [dist_eq_norm] at hB
  show dist (F.D μ x) (F.D μ₀ x₀) < ε
  rw [dist_eq_norm]
  have heq : F.D μ x - F.D μ₀ x₀ = F.D μ (x - x₀) + (F.D μ x₀ - F.D μ₀ x₀) := by
    rw [map_sub]
    abel
  rw [heq]
  calc ‖F.D μ (x - x₀) + (F.D μ x₀ - F.D μ₀ x₀)‖
        ≤ ‖F.D μ (x - x₀)‖ + ‖F.D μ x₀ - F.D μ₀ x₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hA hB
    _ = ε := add_halves ε

private theorem scaledKernelDilate {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {κ : ℝ} (F : ScaledMildFramework X κ) (a b τ : ℝ) (x : X)
    (ha : 0 < a) (hb : 0 < b) (hτ : 0 < τ) :
    F.D a (F.K (b * τ) (F.D b⁻¹ x) (F.D b⁻¹ x)) = b⁻¹ • F.D (a * b⁻¹) (F.K τ x x) := by
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hDD : ∀ μ ν : ℝ, 0 < μ → 0 < ν → ∀ y : X, F.D μ (F.D ν y) = F.D (μ * ν) y := by
    intro μ ν hμ hν y
    rw [F.D_mul μ ν hμ hν, ContinuousLinearMap.comp_apply]
  have hu : F.D b (F.D b⁻¹ x) = x := by
    rw [hDD b b⁻¹ hb hbi, mul_inv_cancel₀ hb.ne', F.D_one, ContinuousLinearMap.id_apply]
  have hK := F.D_K b τ hb hτ (F.D b⁻¹ x) (F.D b⁻¹ x)
  rw [hu] at hK
  have hz : F.K (b * τ) (F.D b⁻¹ x) (F.D b⁻¹ x) = b⁻¹ • F.D b⁻¹ (F.K τ x x) := by
    rw [← hK, map_smul, hDD b⁻¹ b hbi hb, inv_mul_cancel₀ hb.ne', F.D_one,
      ContinuousLinearMap.id_apply, inv_smul_smul₀ hb.ne']
  rw [hz, map_smul, hDD a b⁻¹ ha hbi]

theorem scaledFlowOfMild : ScaledFlowOfMild := by
  intro X _ _ _ κ F w u s₀ s hs hmild hu
  have hcov : ExpChangeOfVariables := expChangeOfVariables_holds
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
    rw [ScaledMildFramework.Ks, huσ, hsplit, scaledKernelDilate F _ _ _ (w σ) ha0 hb0 hτ, hratio,
      smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
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
