import Breakdown.Cert.CoerciveSmoothEnergyIdentityBounds
import Breakdown.Cert.CoerciveSmoothEnergyIdentityTransport
import Breakdown.Cert.CoerciveSmoothEnergyIdentitySumSecondPartials
import Breakdown.Cert.CoerciveSmoothEnergyIdentityStretch
import Breakdown.Cert.CoerciveSmoothEnergyIdentitySliceIntegrable
import Breakdown.Cert.CoerciveSmoothEnergyIdentityTime
import Breakdown.Cert.CoerciveSmoothEnergyIdentityRest

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

theorem slice_identity (P : ℝ) (W v : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWd : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ) :
    ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      (1 / P) * (∫ y, timePair v σ y)
      + ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchForm W v (gradField v) σ y) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := slice_integrable P W v hW hWdec hv σ hs
  simp_rw [smoothRight_split]
  rw [integral_add _ i3, integral_add i1 i2, integral_add _ i7, integral_add i5 i6,
    transport_slice P v hv σ hs, sumSecondPartials_slice P v hv σ hs, stretch_slice P W v hW hWd hWdec hv σ hs]
  all_goals first | exact i5.add i6 | exact i1.add i2 | ring

theorem slice_identity_ae (P : ℝ) (W v : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWd : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    (fun σ => ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun σ => (1 / P) * (∫ y, timePair v σ y)
        + ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
          + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchForm W v (gradField v) σ y) := by
  filter_upwards [slice_bounds_ae P v hv] with σ hs
  exact slice_identity P W v hW hWd hWdec hv σ hs

end SmoothEnergyIdentityInternal

open SmoothEnergyIdentityInternal in
theorem energyIdentitySmoothHolds_proof : EnergyIdentitySmoothHolds := by
  intro P W v _ hW _ hWd hWdec hv
  rw [integral_congr_ae (slice_identity_ae P W v hW hWd hWdec hv),
    integral_add ((time_integrable P v hv).const_mul _) (rest_integrable P W v hW hWdec hv),
    integral_const_mul, time_term_zero P v hv, mul_zero, zero_add]

end Coercive

end Breakdown
