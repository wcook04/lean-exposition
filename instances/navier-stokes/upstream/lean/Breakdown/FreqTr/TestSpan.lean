import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

private theorem diffAt_test {φ : Space → Space} (hφ : IsTestField φ) (y : Space) :
    DifferentiableAt ℝ φ y :=
  (hφ.1.differentiable (by simp)).differentiableAt

private theorem test_add {φ ψ : Space → Space} (hφ : IsTestField φ) (hψ : IsTestField ψ) :
    IsTestField (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, fun y => ?_⟩
  have hd : fderiv ℝ (φ + ψ) y = fderiv ℝ φ y + fderiv ℝ ψ y :=
    fderiv_add (diffAt_test hφ y) (diffAt_test hψ y)
  have a := hφ.2.2 y
  have b := hψ.2.2 y
  unfold divergenceAt at a b ⊢
  simp only [hd, add_apply, PiLp.add_apply, Finset.sum_add_distrib, a, b,
    add_zero]

private theorem test_smul (c : ℝ) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (c • φ) := by
  refine ⟨hφ.1.const_smul c, hφ.2.1.smul_left (f := fun _ : Space => c), fun y => ?_⟩
  have hd : fderiv ℝ (c • φ) y = c • fderiv ℝ φ y := fderiv_const_smul (diffAt_test hφ y) c
  have a := hφ.2.2 y
  unfold divergenceAt at a ⊢
  simp only [hd, smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    a, mul_zero]

private theorem test_zero : IsTestField (0 : Space → Space) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, fun y => ?_⟩
  unfold divergenceAt
  simp

private theorem decay_of_test {φ : Space → Space} (hφ : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  refine ⟨hs, hdiv, ?_⟩
  obtain ⟨A, hA⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set M := max (max A B) 0
  set S := max R 0
  have hM : 0 ≤ M := le_max_right _ _
  have hS : 0 ≤ S := le_max_right _ _
  refine ⟨M * (1 + S) ^ 2, fun y => ?_⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  by_cases hy : y ∈ tsupport φ
  · have hyS : ‖y‖ ≤ S := by
      have := hR hy
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have h1 : 1 + ‖y‖ ≤ 1 + S := by linarith
    have hAy : ‖φ y‖ ≤ M := (hA y).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hBy : ‖fderiv ℝ φ y‖ ≤ M := (hB y).trans ((le_max_right _ _).trans (le_max_left _ _))
    constructor
    · rw [le_div_iff₀ hpos]
      calc ‖φ y‖ * (1 + ‖y‖) ≤ M * (1 + S) := mul_le_mul hAy h1 hpos.le hM
        _ ≤ M * (1 + S) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hM
          nlinarith
    · rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul hBy (pow_le_pow_left₀ hpos.le h1 2) (by positivity) hM
  · have h0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h0' : fderiv ℝ φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
    rw [h0, h0', norm_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩

theorem testSpanSpec (h1 : EmbedLinear) :
    TestSpanSpec := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, test_zero, ?_⟩
    have h := h1.2.1 0 0 (decay_of_test test_zero) (decay_of_test test_zero)
    rw [sub_zero, sub_self] at h
    exact h
  | add a b _ _ ha hb =>
    obtain ⟨φ, hφ, rfl⟩ := ha
    obtain ⟨ψ, hψ, rfl⟩ := hb
    exact ⟨φ + ψ, test_add hφ hψ, h1.1 φ ψ (decay_of_test hφ) (decay_of_test hψ)⟩
  | smul c a _ ha =>
    obtain ⟨φ, hφ, rfl⟩ := ha
    exact ⟨c • φ, test_smul c hφ, h1.2.2 c φ (decay_of_test hφ)⟩

end Breakdown.Freq
