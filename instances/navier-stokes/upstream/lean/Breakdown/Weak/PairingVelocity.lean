import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.PairingVelocity

open Freq.Internal.VelocityInjective

theorem pairing_eq_lp (φ : Space → Space) (hG : MemLp (negSsp φ) (6 / 5) volume) (x : X) :
    ∫ y, inner ℝ ((velocity x : Space → Space) y) (negSsp φ y) =
      (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
        (velocity x) (hG.toLp _) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp] with z hz
  rw [hz]
  rfl

end Internal.PairingVelocity

open Internal.PairingVelocity Freq.Internal.VelocityInjective in
theorem pairingVelocity_holds : PairingVelocity := by
  intro x φ hφ
  have hG : MemLp (negSsp φ) (6 / 5) volume :=
    (negSsp_continuous φ hφ).memLp_of_hasCompactSupport (negSsp_hasCompactSupport φ hφ)
  have hspec : VelocitySpec velocity := Freq.Internal.MildOfWeak.velocity_spec velocity_holds
  let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
  have heq : (fun y : X => inner ℝ y (embedX φ)) = fun y => P (velocity y) (hG.toLp _) := by
    apply Continuous.ext_on testDense_holds.2 (by fun_prop)
      ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds y hy
    show inner ℝ (embedX ψ) (embedX φ) = P (velocity (embedX ψ)) (hG.toLp _)
    rw [pairing_test embedMem_holds fieldOpRealized_holds gradCompatible ψ φ hψ hφ,
      ← pairing_eq_lp φ hG]
    apply integral_congr_ae
    filter_upwards [(hspec ψ hψ) ▸ toLp6_test ψ hψ] with z hz
    rw [hz]
  rw [congrFun heq x, pairing_eq_lp φ hG]

end Breakdown.WeakProfile
