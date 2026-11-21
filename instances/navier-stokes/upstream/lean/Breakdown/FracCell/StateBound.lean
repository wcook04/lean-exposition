import Breakdown.FracCell.StAssembly

open Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

private lemma quadValue_add_matrix {ι : Type*} [Fintype ι] (M M' : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadValue (M + M') v = quadValue M v + quadValue M' v := by
  unfold quadValue
  rw [Matrix.add_mulVec, dotProduct_add]

private lemma quadValue_sum_matrix {ι κ : Type*} [Fintype ι] [Fintype κ] (M : κ → Matrix ι ι ℝ)
    (v : ι → ℝ) : quadValue (∑ K, M K) v = ∑ K, quadValue (M K) v := by
  unfold quadValue
  rw [Matrix.sum_mulVec, dotProduct_sum]

theorem stateBound_of_cells_of (hsplit : QuadFormSplitStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (S : CellSplit k N) (hS : S.IsCellSplit c α) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue ((∑ K, S.cellMatrix K) + S.globalMatrix c) (S.stateOf x ζ)
        ≤ c.quadForm α x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  intro x hx ζ
  have h := hsplit α hα₁ hα₂ c hc S hS x hx ζ
  have hext := hS.exterior_bound x hx
  have hcells : ∑ K, quadValue (S.cellMatrix K) (S.stateOf x ζ) ≤ ∑ K, S.cellPart c α K x ζ :=
    Finset.sum_le_sum fun K _ => hS.cell_bound K x hx ζ
  rw [quadValue_add_matrix, quadValue_sum_matrix]
  linarith

end Assembly

end CellCert

end Breakdown
