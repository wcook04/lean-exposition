import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.SupBound

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

set_option maxHeartbeats 4000000 in
open Internal.SupBound in
theorem extendedSupBoundHolds_of (h1 : FreeEnergyLocalHolds) (h2 : ExtendedFrozenBridgeHolds)
    (_h3 : ExtendedInvarianceHolds) (h4 : ExtendedDataHolds) (_h5 : ReadingEnergyHolds)
    (h6 : ExtendedConvectionHolds) (h7 : FreeEquivariantHolds) :
    ExtendedSupBoundHolds := by
  intro k d hd q hq f hf κ
  have hP : 0 < d.period q := hd.period_pos q hq
  obtain ⟨y, hyc, hyper, hyae, hid⟩ := h1 (d.period q) hP f
  have hN : d.twist = 1 ∨ d.twist = 2 := hd.twist_mem.imp id fun h => h.1
  have hhalf : d.twist = 2 → ∀ σ, y (σ + 1 / 2) = y σ := by
    intro htw
    rcases hd.twist_mem with h | ⟨_, Q, hQ⟩
    · omega
    · exact half_periodic _ d.symmetries Q hQ (h7 d.symmetries (d.period q) hP f hf) y hyc hyae
  have hfb : 0 ≤ d.formBound :=
    (add_nonneg hd.modelFormBound_nonneg hd.formShift_nonneg).trans hd.formBound_ge
  have hex := (h6 d hd q hq).1
  have hconv : ConvectionSpec d.toCertificateData q (convection d.toCertificateData q) := by
    unfold convection
    rw [dif_pos hex]
    exact hex.choose_spec
  have hB : (bordered d.toCertificateData q (f, κ)).1 =
      f + convection d.toCertificateData q (freeInv (d.period q) f)
        + actuatorH d.toCertificateData κ := by
    simp [bordered]
    rfl
  have hb := core_bound hN hP hd.weight_pos hd.weightFn_measurable hd.weightFn_lower
    hd.weightFn_upper hfb (freeInv (d.period q) f) f (bordered d.toCertificateData q (f, κ)).1
    (actuatorH d.toCertificateData κ) (convection d.toCertificateData q (freeInv (d.period q) f))
    (fun t => solField (sliceConvection (d.profile q (circleRep t))
      (gradPart (sliceOf (freeInv (d.period q) f) t))))
    y hyc hyper hyae hid hhalf (h2 d hd q hq f hf) (hconv _) hB ((h4 d hd q hq).2.2.2.2.1 κ)
  exact supGrad_bound _ y _ hyae hb

end Breakdown.Cert
