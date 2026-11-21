import Breakdown.Profile.StatementsFlow

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem dilateJointContinuous_holds : DilateJointContinuous := by
  intro X _ _ _ F
  rintro ⟨μ₀, x₀⟩ ⟨hμ₀, -⟩
  have hμ₀' : 0 < μ₀ := hμ₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hc : ContinuousAt (fun μ => F.D μ x₀) μ₀ :=
    (F.D_cont x₀).continuousAt (Ioi_mem_nhds hμ₀')
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  have hM0 : 0 ≤ (2 * μ₀) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hM1 : 0 < (2 * μ₀) ^ (1 / 4 : ℝ) + 1 := by linarith
  refine ⟨min (min δ₁ μ₀) (ε / (2 * ((2 * μ₀) ^ (1 / 4 : ℝ) + 1))),
    lt_min (lt_min hδ₁ hμ₀') (div_pos hε (by linarith)), ?_⟩
  rintro ⟨μ, x⟩ hd
  rw [Prod.dist_eq] at hd
  have hd1 : dist μ μ₀ < min (min δ₁ μ₀) (ε / (2 * ((2 * μ₀) ^ (1 / 4 : ℝ) + 1))) :=
    lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist x x₀ < min (min δ₁ μ₀) (ε / (2 * ((2 * μ₀) ^ (1 / 4 : ℝ) + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) hd
  have hμδ : dist μ μ₀ < δ₁ :=
    lt_of_lt_of_le hd1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hμμ : dist μ μ₀ < μ₀ :=
    lt_of_lt_of_le hd1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hxε : dist x x₀ < ε / (2 * ((2 * μ₀) ^ (1 / 4 : ℝ) + 1)) :=
    lt_of_lt_of_le hd2 (min_le_right _ _)
  rw [Real.dist_eq, abs_lt] at hμμ
  have hμpos : 0 < μ := by linarith [hμμ.1]
  have hμlt : μ ≤ 2 * μ₀ := by linarith [hμμ.2]
  have hpow : μ ^ (1 / 4 : ℝ) ≤ (2 * μ₀) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hμpos.le hμlt (by norm_num)
  rw [dist_eq_norm] at hxε
  have hA : ‖F.D μ (x - x₀)‖ < ε / 2 := by
    rw [F.D_norm μ hμpos]
    calc μ ^ (1 / 4 : ℝ) * ‖x - x₀‖ ≤ ((2 * μ₀) ^ (1 / 4 : ℝ) + 1) * ‖x - x₀‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < ((2 * μ₀) ^ (1 / 4 : ℝ) + 1) * (ε / (2 * ((2 * μ₀) ^ (1 / 4 : ℝ) + 1))) :=
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

theorem kernelDilate_holds : KernelDilate := by
  intro X _ _ _ F a b τ x ha hb hτ
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

end Breakdown
