import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace KernelScalingInternal

theorem heatKernel_dilate {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) (x : Space) :
    heatKernel (s ^ 2 * τ) (s • x) = (s ^ 3)⁻¹ * heatKernel τ x := by
  unfold heatKernel
  have h1 : 4 * π * (s ^ 2 * τ) = s ^ 2 * (4 * π * τ) := by ring
  have h2 : (s ^ 2) ^ (-(3 / 2 : ℝ)) = (s ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have h3 : -(‖s • x‖ ^ 2) / (4 * (s ^ 2 * τ)) = -(‖x‖ ^ 2) / (4 * τ) := by
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), h2, h3]
  ring

theorem heatKernelThird_dilate {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (i j k : Fin 3) (x : Space) :
    heatKernelThird i j k (s ^ 2 * ρ) (s • x) = (s ^ 6)⁻¹ * heatKernelThird i j k ρ x := by
  unfold heatKernelThird
  rw [heatKernel_dilate hs hρ]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hs' := hs.ne'
  have hρ' := hρ.ne'
  split_ifs <;> field_simp <;> ring

theorem integral_heatKernelThird_dilate {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) (i j k : Fin 3)
    (x : Space) :
    ∫ ρ in Ioi (s ^ 2 * τ), heatKernelThird i j k ρ (s • x) =
      (s ^ 4)⁻¹ * ∫ ρ in Ioi τ, heatKernelThird i j k ρ x := by
  rw [← integral_comp_mul_left_Ioi' (fun ρ => heatKernelThird i j k ρ (s • x)) τ
    (by positivity : (0 : ℝ) < s ^ 2)]
  have h : ∫ ρ in Ioi τ, heatKernelThird i j k (s ^ 2 * ρ) (s • x) =
      ∫ ρ in Ioi τ, (s ^ 6)⁻¹ * heatKernelThird i j k ρ x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    exact heatKernelThird_dilate hs (lt_trans hτ hρ) i j k x
  rw [h, integral_const_mul, smul_eq_mul]
  have hs' := hs.ne'
  field_simp

end KernelScalingInternal

open KernelScalingInternal in
theorem kernelScaling_holds : KernelScaling := by
  intro μ hμ τ hτ x
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ μ = s ^ 2 := ⟨Real.sqrt μ, Real.sqrt_pos.2 hμ, (Real.sq_sqrt hμ.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  refine ⟨?_, fun i j k => ?_⟩
  · rw [heatKernel_dilate hs hτ]
    ring
  · unfold lerayKernel
    rw [heatKernel_dilate hs hτ, integral_heatKernelThird_dilate hs hτ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    have hs' := hs.ne'
    have hτ' := hτ.ne'
    split_ifs <;> field_simp
    ring

end Breakdown.FarField
