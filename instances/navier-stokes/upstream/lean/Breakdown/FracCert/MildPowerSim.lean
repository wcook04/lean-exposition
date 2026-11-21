import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.NNicePairing

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace MildPowerSimInternal

theorem contDiff_two_of_nice {φ : Space → Space} (hφ : IsNiceField φ) : ContDiff ℝ 2 φ := by
  obtain ⟨S, hS⟩ := Internal.NicePairing.rapid_of_nice hφ
  rw [← hS]
  exact S.smooth 2

end MildPowerSimInternal

open MildPowerSimInternal in
theorem powerSimAdj : PowerSimAdjStatement := by
  intro α a μ hα hμ φ hφ
  have hc2 := contDiff_two_of_nice hφ
  set R : Space ≃ₗᵢ[ℝ] Space := axialRotation (-(a * Real.log μ)) with hR
  set l : ℝ := μ ^ (1 / (2 * α)) with hl
  set c : ℝ := μ ^ (4 * (1 / (2 * α)) - 1) with hc
  have hl0 : 0 < l := Real.rpow_pos_of_pos hμ _
  have hlμ : l ^ (2 * α) = μ := by
    rw [hl, ← Real.rpow_mul hμ.le]
    have : 1 / (2 * α) * (2 * α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hw : ContDiff ℝ 2 (fun x => φ (l • x)) := hc2.comp (contDiff_const_smul l)
  have hv : ContDiff ℝ 2 (fun x => c • φ (l • x)) := hw.const_smul c
  funext y
  have e1 : simAdj α a μ φ = fun x => R ((fun x => c • φ (l • x)) (R.symm x)) := rfl
  have e2 : simAdj α a μ (fractionalPowerAt α φ) =
      fun x => R (c • fractionalPowerAt α φ (l • R.symm x)) := rfl
  rw [e1, (covariance α _ hv).2.2.1 R y, (covariance α _ hw).2.1 c (R.symm y),
    (covariance α φ hc2).1 l hl0 (R.symm y), e2]
  simp only [Pi.smul_apply, hlμ, map_smul, smul_comm μ c]

end Breakdown.FracCert
