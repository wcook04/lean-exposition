import Breakdown.CellReduction.InstanceStatements
import Breakdown.CellReduction.InstParamsBounded
import Breakdown.CellReduction.InstProfileSplit

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

theorem adjointStructure_holds_of (hA : AdjointFieldHolds)
    (hP : ProfilePiecesFlowHolds) : AdjointStructureHolds := by
  intro k C nE nM D R Pr Z O r hscale hcert hperiod hlinks j hj
  obtain ⟨hR, _, hZ⟩ := hcert
  have hfield : ∀ q, D.cert.adjoint j q = (r j).field := fun q => by
    rw [hZ.adjoint_eq j hj q, hlinks.field_eq j hj]
  have hfacts := hA D Z hZ
  obtain ⟨A, Cf, hclass, hpot⟩ := hfacts.field j hj
  obtain ⟨M, hM⟩ := paramsBounded_holds D.cert hscale
  obtain ⟨B, hB⟩ := hP D R M hR
  have hempty := hlinks.fitted_empty j hj
  refine
    { adjoint_eq := fun q _ => hfield q
      coupling_eq := fun q hq l => hlinks.coupling_eq j hj q hq l
      field_class := ⟨Cf, 3, by simpa [hfield 0] using hclass 0⟩
      field_potential := ⟨A, Cf, 2, by simpa [hfield 0] using hpot 0⟩
      pieces := ⟨B, ?_, ?_, ?_⟩
      profile_split := ?_
      period_split := ?_ }
  · intro q hq
    rw [hlinks.centre_eq j hj]
    exact (hB q (hM q hq)).1
  · intro i hi
    rw [hempty] at hi
    exact absurd hi (Finset.notMem_empty i)
  · intro q hq i _
    rw [hlinks.free_eq j hj q i]
    exact (hB q (hM q hq)).2 i
  · intro q _ σ y
    rw [hempty, Finset.sum_empty, Finset.compl_empty, add_zero, hlinks.centre_eq j hj,
      profileSplit_holds D R hR q σ y]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [hlinks.free_eq j hj q i]
  · intro q hq
    rw [hperiod q hq, hlinks.centrePeriod_eq j hj, hlinks.periodRate_eq j hj]

end Instantiation

end CellReduction

end Breakdown
