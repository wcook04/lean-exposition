import Breakdown.FracCell.GivenProfileCentre

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

namespace GivenProfileCentreTraceInternal

theorem diag_entry (H : Space →L[ℝ] Space →L[ℝ] Space) (i : Fin 3) :
    entry (curlGradMatrix H) i i =
      ∑ b : Fin 3, ∑ q : Fin 3, permSign i b q * H (unitVector i) (unitVector b) q := by
  simp only [entry, curlGradMatrix, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  simp [unitVector, EuclideanSpace.inner_single_left, Fin.sum_univ_three]
  fin_cases i <;> simp

theorem trace_zero_of_symm (H : Space →L[ℝ] Space →L[ℝ] Space) (hs : ∀ u w, H u w = H w u) :
    ∑ i : Fin 3, entry (curlGradMatrix H) i i = 0 := by
  simp only [diag_entry]
  simp [Fin.sum_univ_three, permSign]
  rw [hs (unitVector 1) (unitVector 0), hs (unitVector 2) (unitVector 0),
    hs (unitVector 2) (unitVector 1)]
  ring

end GivenProfileCentreTraceInternal

open GivenProfileCentreTraceInternal

theorem centreTraceFree_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) :
    ∀ y, ∑ i : Fin 3, entry (c.centreCurlGrad y) i i = 0 := by
  intro y
  exact trace_zero_of_symm (c.centreSecond y) (centreSecond_symm_of D c hD hc y)

end GivenFields

end CellCert

end Breakdown
