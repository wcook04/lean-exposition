import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

theorem newtonFar_of_identity : NewtonFarIdentity → NewtonFarEstimate → NewtonFar := by
  intro hI hE
  obtain ⟨C, hC⟩ := hE
  refine ⟨C, fun f A hf hb i y => ?_⟩
  have hcont : Continuous f := hf.continuous
  have hb0 : ∀ z, ‖f z‖ ≤ A / (1 + ‖z‖) ^ 2 := by
    intro z
    have h := hb 0 (by norm_num) z
    simpa [norm_iteratedFDeriv_zero] using h
  have heq : (fun z => FundSol.kernelGrad (y - z) i * ((1 - nearCutoff y z) * divDivSource f z)) =
      fun z => farWeight i y z * divDivSource f z := by
    funext z
    unfold farWeight
    ring
  obtain ⟨hint, hid⟩ := hI f A hf hb i y
  rw [heq]
  refine ⟨hint, ?_⟩
  rw [hid]
  exact hC f A hcont hb0 i y

end Breakdown.FarField
