import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

private theorem finrank_space_eq : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

private theorem heat_scalar_identity {μ : ℝ} (hμ : 0 < μ) :
    μ * Real.sqrt μ * |(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| = 1 := by
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have h := Real.sq_sqrt hμ.le
  rw [finrank_space_eq, abs_of_pos (inv_pos.2 (pow_pos hr 3))]
  calc μ * Real.sqrt μ * (Real.sqrt μ ^ 3)⁻¹
      = Real.sqrt μ ^ 2 * Real.sqrt μ * (Real.sqrt μ ^ 3)⁻¹ := by rw [h]
    _ = 1 := by field_simp

private theorem kernel_scalar_identity {μ : ℝ} (hμ : 0 < μ) :
    μ ^ 2 * |(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| = Real.sqrt μ := by
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have h := Real.sq_sqrt hμ.le
  rw [finrank_space_eq, abs_of_pos (inv_pos.2 (pow_pos hr 3))]
  calc μ ^ 2 * (Real.sqrt μ ^ 3)⁻¹
      = (Real.sqrt μ ^ 2) ^ 2 * (Real.sqrt μ ^ 3)⁻¹ := by rw [h]
    _ = Real.sqrt μ := by field_simp

private theorem heatConv_dilate (hS : KernelScaling) {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (f : Space → Space) (y : Space) :
    heatConv (μ * τ) f (Real.sqrt μ • y) = heatConv τ (fun z => f (Real.sqrt μ • z)) y := by
  unfold heatConv
  set g : Space → Space := fun w => heatKernel (μ * τ) (Real.sqrt μ • y - w) • f w with hg
  have hne : μ * Real.sqrt μ ≠ 0 := by positivity
  have hpt : ∀ z : Space, heatKernel τ (y - z) • f (Real.sqrt μ • z) =
      (μ * Real.sqrt μ) • g (Real.sqrt μ • z) := by
    intro z
    have h1 := (hS μ hμ τ hτ (y - z)).1
    rw [hg]
    dsimp only
    rw [← smul_sub, h1, smul_smul, mul_inv_cancel_left₀ hne]
  have hcomp := Measure.integral_comp_smul (volume : Measure Space) g (Real.sqrt μ)
  symm
  calc ∫ z, heatKernel τ (y - z) • f (Real.sqrt μ • z)
      = ∫ z, (μ * Real.sqrt μ) • g (Real.sqrt μ • z) := integral_congr_ae (Eventually.of_forall hpt)
    _ = (μ * Real.sqrt μ) • ∫ z, g (Real.sqrt μ • z) := integral_smul _ _
    _ = (μ * Real.sqrt μ) • (|(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| • ∫ z, g z) := by rw [hcomp]
    _ = ∫ z, g z := by rw [smul_smul, heat_scalar_identity hμ, one_smul]

private theorem kernelConv_dilate (hS : KernelScaling) {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (F : Space → Fin 3 → Fin 3 → ℝ) (y : Space) :
    Real.sqrt μ • kernelConv (μ * τ) F (Real.sqrt μ • y) =
      kernelConv τ (fun z => F (Real.sqrt μ • z)) y := by
  unfold kernelConv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  set g : Space → ℝ := fun w => ∑ j : Fin 3, ∑ k : Fin 3,
    lerayKernel i j k (μ * τ) (Real.sqrt μ • y - w) * F w j k with hg
  have hpt : ∀ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k τ (y - z) * F (Real.sqrt μ • z) j k = μ ^ 2 * g (Real.sqrt μ • z) := by
    intro z
    rw [hg]
    dsimp only
    rw [← smul_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := (hS μ hμ τ hτ (y - z)).2 i j k
    have hne : μ ^ 2 ≠ 0 := by positivity
    rw [h1, ← mul_assoc, mul_inv_cancel_left₀ hne]
  have hcomp := Measure.integral_comp_smul (volume : Measure Space) g (Real.sqrt μ)
  symm
  calc ∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F (Real.sqrt μ • z) j k
      = ∫ z, μ ^ 2 * g (Real.sqrt μ • z) := integral_congr_ae (Eventually.of_forall hpt)
    _ = μ ^ 2 * ∫ z, g (Real.sqrt μ • z) := integral_const_mul _ _
    _ = μ ^ 2 * (|(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| • ∫ z, g z) := by rw [hcomp]
    _ = Real.sqrt μ * ∫ z, g z := by rw [smul_eq_mul, ← mul_assoc, kernel_scalar_identity hμ]

theorem duhamelChangeOfVariables_of_kernel (hS : KernelScaling) (_hSup : KernelConvSup)
    (_hB : LerayKernelBound) (_hM : LerayKernelMeasurable) : DuhamelChangeOfVariables := by
  intro W _hW C _hC s T hT y
  have h1T : 0 < 1 + T := by linarith
  have h1T' : 1 + T ≠ 0 := h1T.ne'
  have hμ : 0 < (1 + T)⁻¹ := inv_pos.2 h1T
  have hlogpos : 0 < Real.log (1 + T) := Real.log_pos (by linarith)
  unfold duhamelVelocityForm similarityHeatPart profileBilinTrunc
  congr 1
  · have htime : 1 - (1 + T)⁻¹ = (1 + T)⁻¹ * T := by field_simp; ring
    rw [sub_sub_cancel, Real.exp_neg, Real.exp_log h1T, htime]
    unfold dilateField
    rw [heatConv_dilate hS hμ hT, Real.sqrt_inv]
    rfl
  · have himg : (fun τ : ℝ => s - Real.log (1 + τ)) '' Ioc 0 T = Ico (s - Real.log (1 + T)) s := by
      ext σ
      simp only [mem_image, mem_Ioc, mem_Ico]
      constructor
      · rintro ⟨τ, ⟨h0, hTτ⟩, rfl⟩
        constructor
        · have : Real.log (1 + τ) ≤ Real.log (1 + T) := Real.log_le_log (by linarith) (by linarith)
          linarith
        · have : 0 < Real.log (1 + τ) := Real.log_pos (by linarith)
          linarith
      · rintro ⟨h1, h2⟩
        refine ⟨Real.exp (s - σ) - 1, ⟨?_, ?_⟩, ?_⟩
        · have := Real.add_one_lt_exp (show s - σ ≠ 0 by intro h; linarith)
          linarith
        · have h3 : Real.exp (s - σ) ≤ Real.exp (Real.log (1 + T)) := Real.exp_le_exp.2 (by linarith)
          rw [Real.exp_log h1T] at h3
          linarith
        · have h4 : 1 + (Real.exp (s - σ) - 1) = Real.exp (s - σ) := by ring
          rw [h4, Real.log_exp]
          ring
    have hderiv : ∀ τ ∈ Ioc (0 : ℝ) T, HasDerivWithinAt (fun τ : ℝ => s - Real.log (1 + τ))
        (-(1 / (1 + τ))) (Ioc 0 T) τ := by
      intro τ hτ
      have h1 : 0 < 1 + τ := by linarith [hτ.1]
      exact ((((hasDerivAt_id' τ).const_add 1).log h1.ne').const_sub s).hasDerivWithinAt
    have hinj : InjOn (fun τ : ℝ => s - Real.log (1 + τ)) (Ioc 0 T) := by
      intro a ha b hb hab
      have hab' : Real.log (1 + a) = Real.log (1 + b) := by
        simp only at hab
        linarith
      have := Real.log_injOn_pos (mem_Ioi.2 (by linarith [ha.1] : (0 : ℝ) < 1 + a))
        (mem_Ioi.2 (by linarith [hb.1] : (0 : ℝ) < 1 + b)) hab'
      linarith
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ← integral_Ico_eq_integral_Ioo, ← himg,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hderiv hinj, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    have h1 : 0 < 1 + τ := by linarith [hτ.1]
    have h1' : 1 + τ ≠ 0 := h1.ne'
    have hμ' : 0 < (1 + τ)⁻¹ := inv_pos.2 h1
    have htime' : 1 - (1 + τ)⁻¹ = (1 + τ)⁻¹ * τ := by field_simp; ring
    rw [sub_sub_cancel, Real.exp_neg, Real.exp_log h1, htime']
    unfold dilateField
    rw [smul_neg, kernelConv_dilate hS hμ' hτ.1, abs_neg, abs_of_pos (one_div_pos.2 h1), one_div,
      smul_neg, Real.sqrt_inv]
    rfl

end Breakdown.FarField
