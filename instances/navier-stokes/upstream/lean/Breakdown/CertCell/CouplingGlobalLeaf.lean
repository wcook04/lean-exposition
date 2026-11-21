import Breakdown.CertCell.CouplingStatements

namespace Breakdown

namespace CertCell

namespace Coupling

private theorem twice_product_sub_square_div_le {t a b : ℝ} (ht : 0 < t) :
    2 * a * b - a ^ 2 / t ≤ t * b ^ 2 := by
  have hid : t * b ^ 2 - (2 * a * b - a ^ 2 / t) = (t * b - a) ^ 2 / t := by
    field_simp
    ring
  have hnn : 0 ≤ (t * b - a) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  linarith

theorem globalLeaf : GlobalLeafHolds := by
  intro k tw cw ℓ h κ ζ htw
  have hs : ∑ i, (2 * ζ i * h i - ζ i ^ 2 / tw) ≤ ∑ i, tw * h i ^ 2 :=
    Finset.sum_le_sum fun i _ => twice_product_sub_square_div_le htw
  rw [Finset.sum_sub_distrib] at hs
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum] at hs
  linarith

end Coupling

end CertCell

end Breakdown
