import Breakdown.FracCell.StClauses

noncomputable section

namespace Breakdown

namespace CellCert

namespace CrossIdentityInternal

theorem vec_eq (u : Space) : u = u 0 • unitVector 0 + u 1 • unitVector 1 + u 2 • unitVector 2 := by
  ext i
  fin_cases i <;> simp [unitVector]

theorem apply_coord (A : Space →L[ℝ] Space) (u : Space) (l : Fin 3) :
    A u l = u 0 * entry A l 0 + u 1 * entry A l 1 + u 2 * entry A l 2 := by
  conv_lhs => rw [vec_eq u]
  simp [entry]

theorem adjoint_coord (A : Space →L[ℝ] Space) (w : Space) (k : Fin 3) :
    ContinuousLinearMap.adjoint A w k = entry A 0 k * w 0 + entry A 1 k * w 1 + entry A 2 k * w 2 := by
  have h : ContinuousLinearMap.adjoint A w k = inner ℝ (unitVector k) (ContinuousLinearMap.adjoint A w) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  rw [h, ContinuousLinearMap.adjoint_inner_right]
  simp [entry, PiLp.inner_apply, Fin.sum_univ_three]
  ring

end CrossIdentityInternal

open CrossIdentityInternal in
theorem crossIdentity : CrossIdentityStatement := by
  intro u w Du Dw
  ext i
  simp only [PiLp.add_apply, adjoint_coord]
  simp only [apply_coord]
  fin_cases i <;> simp [crossVec, curlOf, permSign, Fin.sum_univ_three, unitVector] <;> ring

end CellCert

end Breakdown
