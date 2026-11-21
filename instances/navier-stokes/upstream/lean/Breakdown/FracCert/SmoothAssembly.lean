import Breakdown.FracCert.StatementsSmooth

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem lintegral_enorm_sq_eq (x : X) :
    ∫⁻ ξ, ‖(x : L2C) ξ‖ₑ ^ 2 = ENNReal.ofReal ‖x‖ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := ((x : L2C) : Space → CSpace))
    (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [← h, show ‖x‖ = ‖(x : L2C)‖ from rfl, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

private theorem weight_sq_le (ξ : Space) (v : CSpace) :
    ‖ξ‖ ^ (2 * 1) * (|(2 * π * ‖ξ‖)⁻¹| * ‖v‖) ^ 2 ≤ (2 * π)⁻¹ ^ 2 * ‖v‖ ^ 2 := by
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · simp [h]
    positivity
  · have hp : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    have e : ‖ξ‖ ^ (2 * 1) * |(2 * π * ‖ξ‖)⁻¹| ^ 2 = (2 * π)⁻¹ ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      field_simp
    rw [mul_pow, ← mul_assoc, e]

private theorem homNormSq_one_le (x : X) :
    homNormSq 1 (symbolX x) ≤ ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ENNReal.ofReal ‖x‖ ^ 2 := by
  unfold homNormSq symbolX
  rw [← lintegral_enorm_sq_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  simp only [← ofReal_norm, norm_smul, Real.norm_eq_abs]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (weight_sq_le ξ _)

theorem mildSmoothing_of (h1 : MildFirstGainStatement) (h2 : SupFromGainStatement)
    (h3 : MildMomentStepStatement) : MildSmoothingStatement := by
  intro α hα1 hα2 F hF u t ht hu σ hσ
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  set A : ℝ≥0∞ := ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ENNReal.ofReal B ^ 2 with hA
  have hAt : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hH1 : ∀ s ∈ Icc 0 t, homNormSq 1 (symbolX (u s)) ≤ A := by
    intro s hs
    refine (homNormSq_one_le _).trans ?_
    rw [hA]
    gcongr
    exact hB s hs
  obtain ⟨C2, hC2⟩ := h2 (α + 1 / 2) (by linarith)
  have hW : ∀ σ ∈ Ioc 0 t, ∃ C : ℝ, ∀ s ∈ Icc σ t,
      freqL1Norm (symbolX (u s)) ≤ ENNReal.ofReal C := by
    intro σ' hσ'
    obtain ⟨C1, hC1⟩ := h1 α hα1 hα2 F hF u t ht hu σ' hσ'
    set E : ℝ≥0∞ := ENNReal.ofReal C2 * (A ^ (1 / 2 : ℝ) + ENNReal.ofReal C1 ^ (1 / 2 : ℝ)) with hEd
    have hE : E ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAt,
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top⟩)
    refine ⟨E.toReal, fun s hs => ?_⟩
    rw [ENNReal.ofReal_toReal hE]
    have hs0 : s ∈ Icc 0 t := ⟨hσ'.1.le.trans hs.1, hs.2⟩
    refine (hC2 (u s) ((hC1 s hs).trans_lt ENNReal.ofReal_lt_top)).trans ?_
    rw [hEd]
    gcongr
    · exact hH1 s hs0
    · exact hC1 s hs
  have key : ∀ k : ℕ, 1 ≤ k → ∀ σ ∈ Ioc 0 t, ∃ C : ℝ, ∀ s ∈ Icc σ t,
      homNormSq k (symbolX (u s)) ≤ ENNReal.ofReal C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro σ' hσ'
      refine ⟨A.toReal, fun s hs => ?_⟩
      rw [ENNReal.ofReal_toReal hAt]
      exact hH1 s ⟨hσ'.1.le.trans hs.1, hs.2⟩
    | succ k hk ih =>
      refine h3 α hα1 hα2 F hF u t ht hu k hk ?_
      intro σ' hσ'
      obtain ⟨Cw, hw⟩ := hW σ' hσ'
      obtain ⟨Ck, hCk⟩ := ih σ' hσ'
      refine ⟨(ENNReal.ofReal Cw + ENNReal.ofReal Ck).toReal, fun s hs => ?_⟩
      rw [ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)]
      exact add_le_add (hw s hs) (hCk s hs)
  intro k hk
  obtain ⟨C, hC⟩ := key k hk σ hσ
  exact (hC σ ⟨le_rfl, hσ.2⟩).trans_lt ENNReal.ofReal_lt_top

end Breakdown.FracCert
