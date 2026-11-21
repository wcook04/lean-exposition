import Breakdown.Cert.ExtendedCoerciveEnergyIdentityWeak
import Breakdown.Cert.ExtendedCoerciveEnergyIdentityPoint
import Breakdown.Cert.CoerciveSmoothEnergyIdentityStretch

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal Coercive.SmoothEnergyIdentityInternal

structure WeakSliceData (u W₀ : Space → Space) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) :
    Prop where
  hu : ContDiff ℝ ∞ u
  hd : ∀ y, divergenceAt u y = 0
  i0 : Integrable (fun y => ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)
  i1 : Integrable (fun y => ‖fderiv ℝ u y‖ ^ 2)
  i2 : Integrable (fun y => ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ ^ 2)
  hW : ContDiff ℝ 1 W₀
  hWd : ∀ y, divergenceAt W₀ y = 0
  D0 : 0 ≤ D
  W0 : ∀ y, ‖W₀ y‖ ≤ D
  W1 : ∀ y, ‖fderiv ℝ W₀ y‖ ≤ D / (1 + ‖y‖)
  W2 : ∀ y, ‖H y‖ ≤ D / (1 + ‖y‖)
  hHm : AEStronglyMeasurable H
  hweak : ∀ a : Fin 3,
    IsWeakGradient (fun y => fderiv ℝ W₀ y (unitVector a)) (fun y => (H y).flip (unitVector a))
  hsym : ∀ᵐ y, ∀ a b, H y a b = H y b a

end EnergyIdentityWeakInternal

end CoerciveWeak

end Breakdown
