import Breakdown.Weak.StatementsTime

open MeasureTheory Set Real Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem contDiff_similarityScale (s₀ : ℝ) : ContDiff ℝ ∞ (similarityScale s₀) := by
  unfold similarityScale
  fun_prop

private theorem similarityScale_pos (s₀ σ : ℝ) : 0 < similarityScale s₀ σ := Real.exp_pos _

private theorem divergenceAt_scaled {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (c b : ℝ)
    (y : Space) :
    divergenceAt (fun y => c • ψ (b • y)) y = c * b * divergenceAt ψ (b • y) := by
  have hd : HasFDerivAt ψ (fderiv ℝ ψ (b • y)) (b • y) :=
    ((hψ.differentiable (by simp)) (b • y)).hasFDerivAt
  have hl : HasFDerivAt (fun y : Space => b • y) (b • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul b
  have h : HasFDerivAt (fun y => c • ψ (b • y))
      (c • ((fderiv ℝ ψ (b • y)).comp (b • ContinuousLinearMap.id ℝ Space))) y :=
    (hd.comp y hl).const_smul c
  unfold divergenceAt
  rw [h.fderiv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

theorem scaledTestField_holds : ScaledTestField := by
  intro α s₀ φ hα hαc hφ
  have hψ := isTestField_negSsp hφ
  refine ⟨?_, ?_, ?_⟩
  · have hβ := contDiff_similarityScale s₀
    exact ((hα.comp contDiff_fst).mul ((hβ.comp contDiff_fst).pow 2)).smul
      (hψ.1.comp ((hβ.comp contDiff_fst).smul contDiff_snd))
  · obtain ⟨r, hr⟩ := hαc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨R, hR⟩ := hψ.2.1.isCompact.isBounded.subset_closedBall 0
    have hm0 : 0 < Real.exp (-(r - s₀) / 2) := Real.exp_pos _
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) r).prod
      (isCompact_closedBall (0 : Space) (R / Real.exp (-(r - s₀) / 2)))) ?_
    rintro ⟨σ, y⟩ hz
    simp only [scaledTest]
    by_cases hσ : σ ∈ closedBall (0 : ℝ) r
    · have hy : y ∉ closedBall (0 : Space) (R / Real.exp (-(r - s₀) / 2)) :=
        fun hy => hz ⟨hσ, hy⟩
      have hσr : σ ≤ r := by
        have h1 := mem_closedBall_zero_iff.mp hσ
        rw [Real.norm_eq_abs] at h1
        exact (abs_le.mp h1).2
      have hβm : Real.exp (-(r - s₀) / 2) ≤ similarityScale s₀ σ := by
        unfold similarityScale
        exact Real.exp_le_exp.mpr (by linarith)
      have h0 : negSsp φ (similarityScale s₀ σ • y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        have h1 := mem_closedBall_zero_iff.mp (hR h)
        rw [norm_smul, Real.norm_of_nonneg (similarityScale_pos s₀ σ).le] at h1
        have h2 : R / Real.exp (-(r - s₀) / 2) < ‖y‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hy
          exact hy
        have h3 : R < Real.exp (-(r - s₀) / 2) * ‖y‖ := by
          rw [div_lt_iff₀ hm0] at h2
          linarith
        nlinarith [norm_nonneg y]
      rw [h0, smul_zero]
    · have h0 : α σ = 0 := image_eq_zero_of_notMem_tsupport (fun h => hσ (hr h))
      rw [h0, zero_mul, zero_smul]
  · intro σ y
    exact (divergenceAt_scaled hψ.1 _ _ y).trans (by rw [hψ.2.2, mul_zero])
