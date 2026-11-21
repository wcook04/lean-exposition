import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace TensorWeightInternal

theorem norm_tensorField_le (u v : Space) :
    ‖tensorField (fun _ => u) (fun _ => v) 0‖ ≤ ‖u‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  simp only [tensorField, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (PiLp.norm_apply_le u j) (PiLp.norm_apply_le v k) (abs_nonneg _)
    (norm_nonneg _)

end TensorWeightInternal

open TensorWeightInternal in
theorem tensorWeight_holds : TensorWeight := by
  intro a b γ γ' A B _ _ hA hB s y
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 := hA s y
  have h2 := hB s y
  have hX : 0 ≤ (1 + ‖y‖) ^ γ * ‖a s y‖ := mul_nonneg (rpow_nonneg hpos.le _) (norm_nonneg _)
  have hY : 0 ≤ (1 + ‖y‖) ^ γ' * ‖b s y‖ := mul_nonneg (rpow_nonneg hpos.le _) (norm_nonneg _)
  have hT : ‖pairTensor a b s y‖ ≤ ‖a s y‖ * ‖b s y‖ := norm_tensorField_le (a s y) (b s y)
  calc (1 + ‖y‖) ^ (γ + γ') * ‖pairTensor a b s y‖
      ≤ (1 + ‖y‖) ^ (γ + γ') * (‖a s y‖ * ‖b s y‖) :=
        mul_le_mul_of_nonneg_left hT (rpow_nonneg hpos.le _)
    _ = ((1 + ‖y‖) ^ γ * ‖a s y‖) * ((1 + ‖y‖) ^ γ' * ‖b s y‖) := by
        rw [rpow_add hpos]; ring
    _ ≤ A * B := mul_le_mul h1 h2 hY (hX.trans h1)

end Breakdown.FarField
