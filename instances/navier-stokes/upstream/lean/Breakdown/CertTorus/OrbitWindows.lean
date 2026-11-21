import Breakdown.CertTorus.RegularStatements
import Breakdown.Transfer.Exports

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

open Freq

theorem orbitWindows_holds : OrbitWindows := by
  intro w P R hw s₀ T _ hT1
  obtain ⟨hc, hd⟩ := orbitPhysical X realization.F w hw.cont hw.flow s₀
  exact ⟨hc.mono (Icc_subset_Ico_right hT1), fun t ht => hd t ⟨ht.1, ht.2.trans_lt hT1⟩⟩

end Breakdown.FarField
