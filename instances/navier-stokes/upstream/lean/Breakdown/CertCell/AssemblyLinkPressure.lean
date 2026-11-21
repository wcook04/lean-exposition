import Breakdown.CertCell.AssemblyStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCalculus

theorem pressureRecoveryHolds_of_pressureParts (hA : AnnihilatorGradientHolds)
    (hH : HarmonicAnnihilatorHolds) (hF : FlipAverageRightSideHolds) (hS : RemainderAnnihilatesHolds)
    (hR : RemainderRegularHolds) : PressureRecoveryHolds := by
  intro k C nE nM D hD q hq x
  obtain ⟨hFm, hFp, hF2, hFr⟩ := hF D hD q hq x
  obtain ⟨hRm, hRp, hRl⟩ :=
    hR D hD q hq x.v x.G x.H x.g x.perturbation x.κ (flipAverage x.F) hFm hFp hF2
  have hSa := hS D hD q hq x.v x.G x.H x.g x.perturbation x.κ (flipAverage x.F) hFm hFp hF2 hFr
  have hHa := hH _ hRm hRp hRl hSa
  refine ⟨hRm, hRp, hRl, fun ν => ?_⟩
  obtain ⟨hcm, hsm, hcl, hsl, hco, hso⟩ := hHa ν
  exact ⟨hA _ hcm hcl hco, hA _ hsm hsl hso⟩

end Assembly

end CertCell

end Breakdown
