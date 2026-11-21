import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField.Internal.LerayOdd

open Breakdown Breakdown.FarField

theorem heatKernel_neg (τ : ℝ) (x : Space) : heatKernel τ (-x) = heatKernel τ x := by
  unfold heatKernel
  rw [norm_neg]

theorem heatKernelThird_neg (i j k : Fin 3) (ρ : ℝ) (x : Space) :
    heatKernelThird i j k ρ (-x) = -heatKernelThird i j k ρ x := by
  unfold heatKernelThird
  rw [heatKernel_neg]
  simp only [PiLp.neg_apply]
  split_ifs <;> ring

end Breakdown.FarField.Internal.LerayOdd

namespace Breakdown.FarField

open Breakdown.FarField.Internal.LerayOdd

theorem lerayKernelOdd_holds : LerayKernelOdd := by
  intro i j k τ x
  unfold lerayKernel
  have hI : (∫ ρ in Ioi τ, heatKernelThird i j k ρ (-x)) = -∫ ρ in Ioi τ, heatKernelThird i j k ρ x := by
    simp_rw [heatKernelThird_neg]
    exact integral_neg _
  rw [hI, heatKernel_neg]
  simp only [PiLp.neg_apply]
  split_ifs <;> ring

end Breakdown.FarField
