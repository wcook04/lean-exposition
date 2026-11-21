import Breakdown.FracCell.StFormulaProof

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open CellAnalysis CellAnalysis.CellScalars

namespace FormulaFarInternal

open Classical

variable {k N slots : ℕ} (S : CellScalars) (R : CellRows N slots k)

theorem farMatrix_eq (e e' : Aug S k) :
    farMatrix S R e e' =
      if augToFar S e ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) ∧ augToFar S e' ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) then
        R.farKernel (augToFar S e) (augToFar S e') else 0 := by
  have key : ∀ e : Aug S k, (∀ i, e = Sum.inl i → i.1 ∈ R.farSupport) ↔
      augToFar S e ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) := by
    rintro (i | j)
    · simp [augToFar, Finset.inl_mem_disjSum]
    · simp [augToFar, Finset.inr_mem_disjSum]
  unfold farMatrix
  by_cases h : augToFar S e ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) ∧ augToFar S e' ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k))
  · rw [if_pos ((and_congr (key e) (key e')).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((and_congr (key e) (key e')).mp h')), if_neg h]

theorem sum_aug (hsub : R.farSupport ⊆ lowSupport S) (h : LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ) :
    ∑ e : Aug S k, (if augToFar S e ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) then h (augToFar S e) else 0) =
      ∑ i ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)), h i := by
  rw [Fintype.sum_sum_type, Finset.sum_disjSum]
  congr 1
  · have h1 : ∀ i : LowSupp S,
        (if augToFar S (Sum.inl i : Aug S k) ∈ R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) then h (augToFar S (Sum.inl i : Aug S k)) else 0) =
          (fun j : LowIndex => if j ∈ R.farSupport then h (Sum.inl j) else 0) i.1 := by
      intro i
      simp [augToFar, Finset.inl_mem_disjSum]
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_coe_sort (lowSupport S) (fun j : LowIndex => if j ∈ R.farSupport then h (Sum.inl j) else 0),
      ← Finset.sum_subset hsub (f := fun j : LowIndex => if j ∈ R.farSupport then h (Sum.inl j) else 0)
        (fun j _ hj => if_neg hj)]
    exact Finset.sum_congr rfl (fun j hj => if_pos hj)
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [augToFar, Finset.inr_mem_disjSum]

end FormulaFarInternal

open Classical FormulaFarInternal in
theorem farIdentity : FarIdentityStatement := by
  intro k N slots c K S B R hsub x ζ
  set T := R.farSupport.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) with hT
  set fv := farVector c K S B x ζ with hfv
  have hu : augVector c K S B x ζ = fun e => fv (augToFar S e) := by
    funext e
    rcases e with i | i | i <;> rfl
  have step : ∀ e : Aug S k,
      star (fv (augToFar S e)) * ∑ e' : Aug S k, farMatrix S R e e' * fv (augToFar S e') =
        if augToFar S e ∈ T then
          ∑ i' ∈ T, star (fv (augToFar S e)) * R.farKernel (augToFar S e) i' * fv i' else 0 := by
    intro e
    by_cases he : augToFar S e ∈ T
    · rw [if_pos he, ← sum_aug S R hsub (fun i' => star (fv (augToFar S e)) * R.farKernel (augToFar S e) i' * fv i'),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e' _ => ?_)
      rw [farMatrix_eq]
      by_cases he' : augToFar S e' ∈ T
      · rw [if_pos ⟨he, he'⟩, if_pos he']
        ring
      · rw [if_neg (fun h => he' h.2), if_neg he']
        ring
    · rw [if_neg he]
      have : ∀ e' : Aug S k, farMatrix S R e e' * fv (augToFar S e') = 0 := by
        intro e'
        rw [farMatrix_eq, if_neg (fun h => he h.1), zero_mul]
      simp [this]
  unfold farFormValue quadFormValue
  rw [hu]
  simp only [dotProduct, mulVec, Pi.star_apply]
  rw [Finset.sum_congr rfl (fun e _ => step e),
    sum_aug S R hsub (fun i => ∑ i' ∈ T, star (fv i) * R.farKernel i i' * fv i')]
  rfl

end Breakdown.CellCert.CellFormula
