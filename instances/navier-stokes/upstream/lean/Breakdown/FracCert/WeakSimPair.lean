import Breakdown.FracCert.StWeak
import Breakdown.Frac.RExports
import Breakdown.Frac.PAxial
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

theorem simAdjPairing : SimAdjPairingStatement := by
  intro α a μ hα hμ x φ _
  set g : ℝ := 1 / (2 * α) with hg
  set R : Space ≃ₗᵢ[ℝ] Space := axialRotation (a * Real.log μ) with hR
  set v : Space → Space := (velocity x : Space → Space) with hv
  set w : Space → Space := (velocity (rotX R x) : Space → Space) with hw
  have hsim : simOp α a μ x = fracDilX α μ⁻¹ (rotX R x) := rfl
  have h1 := fracVelocityDilate_holds α hα μ⁻¹ (inv_pos.2 hμ) (rotX R x)
  have h2 : w =ᵐ[volume] pushForward R v := velocityCov_holds.1 R x
  have hc : (μ⁻¹) ^ g * μ ^ g = 1 := by
    rw [Real.inv_rpow hμ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hμ g).ne']
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hpow : |((μ ^ g) ^ Module.finrank ℝ Space)⁻¹|⁻¹ * (μ⁻¹) ^ (1 - g) = μ ^ (4 * g - 1) := by
    rw [hfin, abs_inv, inv_inv, abs_of_pos (pow_pos (Real.rpow_pos_of_pos hμ g) 3),
      Real.inv_rpow hμ.le, ← Real.rpow_neg hμ.le, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le,
      ← Real.rpow_add hμ]
    congr 1
    push_cast
    ring
  have hRsymm : (axialRotation (-(a * Real.log μ))) = R.symm := by
    rw [hR, axialRotationSpec.2.2.2.1]
  calc ∫ y, inner ℝ ((velocity (simOp α a μ x) : Space → Space) y) (φ y)
      = ∫ y, inner ℝ (scaleField α μ⁻¹ w y) (φ y) := by
        rw [hsim]
        refine integral_congr_ae ?_
        filter_upwards [h1] with y hy
        rw [hy]
    _ = |((μ ^ g) ^ Module.finrank ℝ Space)⁻¹|⁻¹ *
          ∫ z, inner ℝ (scaleField α μ⁻¹ w ((μ ^ g) • z)) (φ ((μ ^ g) • z)) := by
        rw [Measure.integral_comp_smul volume (fun y => inner ℝ (scaleField α μ⁻¹ w y) (φ y)) (μ ^ g),
          smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
        rw [hfin]
        simp only [ne_eq, abs_eq_zero, inv_eq_zero, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
          not_false_eq_true]
        exact (Real.rpow_pos_of_pos hμ g).ne'
    _ = |((μ ^ g) ^ Module.finrank ℝ Space)⁻¹|⁻¹ * (μ⁻¹) ^ (1 - g) *
          ∫ z, inner ℝ (w z) (φ ((μ ^ g) • z)) := by
        rw [mul_assoc, ← integral_const_mul ((μ⁻¹) ^ (1 - g)) (fun z : Space => inner ℝ (w z) (φ ((μ ^ g) • z)))]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [scaleField, smul_smul, ← hg, hc, one_smul, real_inner_smul_left]
    _ = μ ^ (4 * g - 1) * ∫ z, inner ℝ (pushForward R v z) (φ ((μ ^ g) • z)) := by
        rw [hpow]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [h2] with z hz
        rw [hz]
    _ = μ ^ (4 * g - 1) * ∫ z, inner ℝ (R (v z)) (φ ((μ ^ g) • R z)) := by
        congr 1
        rw [← (LinearIsometryEquiv.measurePreserving R).integral_comp
          R.toHomeomorph.measurableEmbedding]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp [pushForward]
    _ = ∫ y, inner ℝ ((velocity x : Space → Space) y) (simAdj α a μ φ y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [simAdj, pushForward, ← hg, hRsymm, ← hv, LinearIsometryEquiv.symm_symm]
        rw [LinearIsometryEquiv.inner_map_eq_flip, map_smul, real_inner_smul_right]

end Breakdown.FracCert
