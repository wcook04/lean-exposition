import Breakdown.FracCert.HeldExists
import Breakdown.FracCert.HeldUnique

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

open HeldUniqueInternal in
theorem weakPowerSub : WeakPowerSubStatement := by
  intro α h1 h2 v P v' P' hv hv' hP hP'
  refine ⟨hP.1.sub hP'.1, fun φ hφ => ?_⟩
  have e1 := hP.2 φ hφ
  have e2 := hP'.2 φ hφ
  simp only [inner_sub_left]
  rw [integral_sub (l2_test_int hP.1 hφ) (l2_test_int hP'.1 hφ),
    integral_sub (six_power_int h1 (by linarith) hv hφ) (six_power_int h1 (by linarith) hv' hφ),
    e1, e2]

end SteadyCert

end Breakdown
