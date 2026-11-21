import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

theorem kernelConvSup_of_l1 : KernelL1Bound → LerayKernelMeasurable → KernelConvSup := by
  intro hL1 _
  obtain ⟨C, hC⟩ := hL1
  refine ⟨27 * C, ?_⟩
  intro τ hτ F _ A hA y
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  have hFjk : ∀ z j k, |F z j k| ≤ A := fun z j k =>
    le_trans (le_trans (norm_le_pi_norm (F z j) k) (norm_le_pi_norm (F z) j)) (hA z)
  have hcoord : ∀ i : Fin 3,
      ‖∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k‖ ≤
        9 * (C * τ ^ (-(1 / 2 : ℝ))) * A := by
    intro i
    have hint : ∀ j k : Fin 3, Integrable (fun z => |lerayKernel i j k τ (y - z)| * A) := by
      intro j k
      exact (((hC i j k τ hτ).1.comp_sub_left y).abs).mul_const A
    have hbound : ∀ z, ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k‖ ≤
        ∑ j : Fin 3, ∑ k : Fin 3, |lerayKernel i j k τ (y - z)| * A := by
      intro z
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hFjk z j k) (abs_nonneg _)
    have hgi : Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, |lerayKernel i j k τ (y - z)| * A) :=
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k
    refine le_trans (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)) ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
    have hterm : ∀ j k : Fin 3, ∫ z, |lerayKernel i j k τ (y - z)| * A ≤
        C * τ ^ (-(1 / 2 : ℝ)) * A := by
      intro j k
      rw [integral_mul_const]
      have he : ∫ z, |lerayKernel i j k τ (y - z)| = ∫ x, |lerayKernel i j k τ x| :=
        integral_sub_left_eq_self (fun x => |lerayKernel i j k τ x|) volume y
      rw [he]
      exact mul_le_mul_of_nonneg_right (hC i j k τ hτ).2 hA0
    calc ∑ j : Fin 3, ∫ z, ∑ k : Fin 3, |lerayKernel i j k τ (y - z)| * A
        = ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, |lerayKernel i j k τ (y - z)| * A := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact integral_finsetSum _ fun k _ => hint j k
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, C * τ ^ (-(1 / 2 : ℝ)) * A :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
      _ = 9 * (C * τ ^ (-(1 / 2 : ℝ))) * A := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  unfold kernelConv
  calc ‖∑ i : Fin 3, (∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) •
        unitVector i‖
      ≤ ∑ i : Fin 3, ‖(∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) •
        unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 9 * (C * τ ^ (-(1 / 2 : ℝ))) * A := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        have hu : ‖unitVector i‖ = 1 := by
          simp [unitVector]
        rw [hu, mul_one]
        exact hcoord i
    _ = 27 * C * τ ^ (-(1 / 2 : ℝ)) * A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Breakdown.FarField
