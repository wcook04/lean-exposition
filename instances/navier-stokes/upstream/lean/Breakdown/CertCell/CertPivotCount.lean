import Mathlib
import Breakdown.CertCell.CertificateStatements

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

private theorem quadValue_add_matrix {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M + N) x = quadValue M x + quadValue N x := by
  simp [quadValue, add_mulVec, dotProduct_add]

private theorem quadValue_sub_matrix {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M - N) x = quadValue M x - quadValue N x := by
  simp [quadValue, sub_mulVec, dotProduct_sub]

private theorem quadValue_sum_matrix {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (M : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (∑ k ∈ s, M k) x = ∑ k ∈ s, quadValue (M k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadValue]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quadValue_add_matrix, ih]

private theorem quadValue_diagonal_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (d x : ι → ℝ) :
    quadValue (diagonal d) x = ∑ j, d j * x j ^ 2 := by
  simp only [quadValue, dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl (fun j _ => by ring)

private theorem quadValue_vecMulVec_self {ι : Type*} [Fintype ι] (c x : ι → ℝ) :
    quadValue (vecMulVec c c) x = (c ⬝ᵥ x) ^ 2 := by
  simp only [quadValue, vecMulVec_mulVec]
  simp [dotProduct_smul, dotProduct_comm x c, sq]

theorem pivotCountPositive : PivotCountPositive := by
  intro A B _ _ T hT
  classical
  let _ : Fintype T.Node := T.nodeFintype
  let _ : Fintype T.Column := T.columnFintype
  let f : (A ⊕ B → ℝ) →ₗ[ℝ] (T.Column → ℝ) :=
    { toFun := fun x c => T.column c ⬝ᵥ x
      map_add' := by
        intro x y
        funext c
        simp [dotProduct_add]
      map_smul' := by
        intro r x
        funext c
        simp [dotProduct_smul] }
  refine ⟨LinearMap.ker f, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank ℝ (LinearMap.range f) ≤ Fintype.card T.Column := by
      simpa using Submodule.finrank_le (LinearMap.range f)
    have h3 : Module.finrank ℝ (A ⊕ B → ℝ) = Fintype.card A + Fintype.card B := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    have h4 : Fintype.card T.Column ≤ Fintype.card B := hT.column_count
    omega
  · intro y hy hy0
    have hcol : ∀ c, T.column c ⬝ᵥ y = 0 := fun c => congrFun (LinearMap.mem_ker.mp hy) c
    unfold SignedTree.rootForm
    rw [quadValue_sub_matrix, quadValue_add_matrix, quadValue_sum_matrix, quadValue_sum_matrix]
    simp only [quadValue_diagonal_matrix, quadValue_vecMulVec_self, hcol]
    have hzero : ∑ c : T.Column, (0 : ℝ) ^ 2 = 0 := by simp
    rw [hzero, sub_zero]
    refine add_pos_of_nonneg_of_pos (hT.root_front_nonneg y) ?_
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      exact hy0 (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    obtain ⟨ν, hν⟩ := hT.every_variable_pivoted j
    refine Finset.sum_pos' (fun μ _ => Finset.sum_nonneg (fun i _ => ?_))
      ⟨ν, Finset.mem_univ _, Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩⟩
    · split_ifs with h
      · exact mul_nonneg (hT.slack_positive _ _ h).le (sq_nonneg _)
      · simp
    · split_ifs with h
      · exact mul_nonneg (hT.slack_positive _ _ h).le (sq_nonneg _)
      · simp
    · rw [if_pos hν]
      exact mul_pos (hT.slack_positive _ _ hν) (by positivity)

end Breakdown.CertCell.Certificate
