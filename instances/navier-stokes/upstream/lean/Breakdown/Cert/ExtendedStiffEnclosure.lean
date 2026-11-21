import Breakdown.Cert.ExtendedNodes

open MeasureTheory

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedStiffEnclosure

theorem energyW_nonneg_of_weight {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) :
    0 ≤ energyW w u := by
  unfold energyW sliceWeightedGrad
  refine add_nonneg (sq_nonneg _) (integral_nonneg fun t => integral_nonneg fun y => ?_)
  exact mul_nonneg (hw y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem sqrt_sum_sq_le_sizeZ {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX)
    (κ : Fin k → ℝ) : Real.sqrt (∑ i, κ i ^ 2) ≤ sizeZ w u κ := by
  unfold sizeZ
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (energyW_nonneg_of_weight hw u))

end Internal.ExtendedStiffEnclosure

open Internal.ExtendedStiffEnclosure in
theorem extendedStiffEnclosureHolds : ExtendedStiffEnclosureHolds := by
  intro k d hd q _ f κ hs
  have hE := hd.certificate
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => le_trans hE.weight_pos.le (hE.weightFn_lower y)
  have hκ : Real.sqrt (∑ i, κ i ^ 2) ≤ 2 * d.sizeBound :=
    le_trans (sqrt_sum_sq_le_sizeZ hw _ κ) hs.size
  have h1 : Real.sqrt (∑ j ∈ d.adjointSetᶜ, (∑ i, d.frame i j * κ i) ^ 2) ≤
      Real.sqrt (d.stiffNorm ^ 2 * ∑ i, κ i ^ 2) :=
    Real.sqrt_le_sqrt (hE.stiff_norm κ)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hE.stiffNorm_nonneg] at h1
  rw [hd.unit_weight, div_one]
  calc Real.sqrt (∑ j ∈ d.adjointSetᶜ, (∑ i, d.frame i j * κ i) ^ 2)
      ≤ d.stiffNorm * Real.sqrt (∑ i, κ i ^ 2) := h1
    _ ≤ d.stiffNorm * (2 * d.sizeBound) := mul_le_mul_of_nonneg_left hκ hE.stiffNorm_nonneg
    _ = 2 * d.sizeBound * d.stiffNorm := by ring

end Breakdown.Cert
