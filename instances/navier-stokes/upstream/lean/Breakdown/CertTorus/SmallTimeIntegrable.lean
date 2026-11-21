import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace SmallTimeWeight.Internal

theorem inv_sqrt_eq_rpow {τ : ℝ} (hτ : 0 < τ) : (Real.sqrt τ)⁻¹ = τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]

theorem inv_mul_inv_sqrt_eq_rpow {τ : ℝ} (hτ : 0 < τ) :
    τ⁻¹ * (Real.sqrt τ)⁻¹ = τ ^ (-(3 / 2 : ℝ)) := by
  rw [inv_sqrt_eq_rpow hτ, ← Real.rpow_neg_one, ← Real.rpow_add hτ]
  norm_num

theorem weight_le_one {τ β : ℝ} (hτ : 0 ≤ τ) (hβ : 0 ≤ β) : (1 + τ) ^ (-β) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

theorem weight_le_inv {τ β : ℝ} (hτ : 1 ≤ τ) (hβ : 1 ≤ β) : (1 + τ) ^ (-β) ≤ τ⁻¹ := by
  have h0 : 0 < τ := by linarith
  rw [Real.rpow_neg (by linarith)]
  apply inv_anti₀ h0
  calc τ = τ ^ (1 : ℝ) := (Real.rpow_one τ).symm
    _ ≤ τ ^ β := Real.rpow_le_rpow_of_exponent_le hτ hβ
    _ ≤ (1 + τ) ^ β := Real.rpow_le_rpow h0.le (by linarith) (by linarith)

end SmallTimeWeight.Internal

open SmallTimeWeight.Internal in
theorem smallTimeIntegrable_holds : SmallTimeIntegrable := by
  intro n
  set β : ℝ := 1 + (n : ℝ) / 2 with hβdef
  have hβ : 1 ≤ β := by
    have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    linarith
  have hcont : ContinuousOn (fun τ : ℝ => (1 + τ) ^ (-β) * (Real.sqrt τ)⁻¹) (Ioi 0) := by
    intro τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · exact (continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by show (1 : ℝ) + τ ≠ 0; linarith))
    · exact Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr hτ').ne'
  rw [(Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by norm_num)
    refine hg.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun τ hτ => ?_
    have h0 : 0 < τ := hτ.1
    have hs : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
    have hw : 0 ≤ (1 + τ) ^ (-β) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg (mul_nonneg hw hs), ← inv_sqrt_eq_rpow h0]
    calc (1 + τ) ^ (-β) * (Real.sqrt τ)⁻¹ ≤ 1 * (Real.sqrt τ)⁻¹ :=
          mul_le_mul_of_nonneg_right (weight_le_one h0.le (by linarith)) hs
      _ = (Real.sqrt τ)⁻¹ := one_mul _
  · have hg : IntegrableOn (fun τ : ℝ => τ ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine hg.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => ?_
    have h1 : 1 < τ := hτ
    have h0 : 0 < τ := by linarith
    have hs : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
    have hw : 0 ≤ (1 + τ) ^ (-β) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg (mul_nonneg hw hs), ← inv_mul_inv_sqrt_eq_rpow h0]
    exact mul_le_mul_of_nonneg_right (weight_le_inv h1.le hβ) hs

end Breakdown.FarField
