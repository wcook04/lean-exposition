import Breakdown.FracCell.StFormulaProof

open Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace FormulaPolar

theorem quad_transpose {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (w : ι → ℝ) :
    w ⬝ᵥ (Mᵀ *ᵥ w) = w ⬝ᵥ (M *ᵥ w) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem polarized_eq {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ w, f w = w ⬝ᵥ (M *ᵥ w)) : polarized f = (1 / 2 : ℝ) • (M + Mᵀ) := by
  ext e e'
  simp only [polarized, hM, mulVec_add, dotProduct_add, add_dotProduct, mulVec_single,
    single_dotProduct, Matrix.smul_apply, Matrix.add_apply, transpose_apply, smul_eq_mul,
    Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one, one_mul]
  ring

end FormulaPolar

open FormulaPolar

theorem polarization : PolarizationStatement := by
  intro ι _ _ f hf w
  obtain ⟨M, hM⟩ := hf
  rw [polarized_eq f M hM, hM]
  simp only [Finite.quadValue, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add,
    quad_transpose, smul_eq_mul]
  ring

end CellFormula

end CellCert

end Breakdown
