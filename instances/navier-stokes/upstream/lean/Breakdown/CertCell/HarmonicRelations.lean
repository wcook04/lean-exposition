import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.LocalRelations

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem harmonicRelations_holds (h1 : HarmonicLiftStatement) : HarmonicRelationsStatement := by
  intro m K B modes L hL v G H Pg hP hPg ν ρ
  obtain ⟨c, S, _, _, hcl⟩ := hL
  obtain ⟨hc, hs, _⟩ := h1 m v G H hP ν
  have hac : IsLocalAdmissible (cosTuple ν v G H Pg) := ⟨hc, (hPg.harmonic_gradient ν).1⟩
  have has : IsLocalAdmissible (sinTuple ν v G H Pg) := ⟨hs, (hPg.harmonic_gradient ν).2⟩
  have e1 := localRelationsHold c K S B L hcl _ hac ρ
  have e2 := localRelationsHold c K S B L hcl _ has ρ
  unfold harmonicData
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ Complex.I, ← Finset.mul_sum, e1, e2, mul_zero,
    add_zero]

end Breakdown.CertCell.CellCalculus
