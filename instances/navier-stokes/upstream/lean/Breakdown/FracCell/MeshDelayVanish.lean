import Breakdown.FracCell.MeshDefs

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula Matrix

namespace MeshDelayVanishInternal

theorem sum_rowEntries_mul {n : ℕ} (L : List (Fin n × ℝ)) (f : Fin n → ℝ) :
    ∑ i, rowEntries L i * f i = (L.map (fun p => p.2 * f p.1)).sum := by
  induction L with
  | nil => simp [rowEntries]
  | cons a L ih =>
    have h : ∀ i, rowEntries (a :: L) i = (if a.1 = i then a.2 else 0) + rowEntries L i := by
      intro i
      simp [rowEntries]
    simp only [h, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

end MeshDelayVanishInternal

open MeshDelayVanishInternal in
open Classical in
theorem delayVanish_of (α : ℝ) {k N : ℕ} (c : FracCellData k N) (Sp : CellSplit k N) (M : MeshData k N Sp)
    (hM : IsMeshData α c Sp M) (hmom : ∀ x, Sp.moment x = M.canonicalMoment c x) :
    ∀ j x, IsAdmissible c x → ∀ ζ : Fin k → ℝ, Finite.quadValue (Sp.delayForm j) (Sp.stateOf x ζ) = 0 := by
  intro j x _ ζ
  set m := M.canonicalMoment c x with hm
  set F := Sp.freeMap *ᵥ ζ with hFdef
  set g : Fin Sp.slots → ℝ := fun l => if M.IsDelaySlot l then 0 else M.baseMoment c x l with hg
  set E : Fin Sp.slots → Fin Sp.slots → ℝ := fun i l =>
    if M.IsDelaySlot i then rowEntries (M.delayExpansion i) l else if i = l then 1 else 0 with hE
  have hzero : ∀ i l, M.IsDelaySlot l → rowEntries (M.delayExpansion i) l = 0 := by
    intro i l hl
    unfold rowEntries
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    rw [if_neg]
    rintro rfl
    exact hM.expansion_base i p hp hl
  have hmE : ∀ i, m i = ∑ l, E i l * g l := by
    intro i
    by_cases hi : M.IsDelaySlot i
    · have h1 : m i = ((M.delayExpansion i).map (fun p => p.2 * M.baseMoment c x p.1)).sum := by
        rw [hm]
        unfold MeshData.canonicalMoment
        rw [if_pos hi]
      rw [h1]
      simp only [hE, if_pos hi]
      rw [sum_rowEntries_mul]
      congr 1
      apply List.map_congr_left
      intro p hp
      simp only [hg, if_neg (hM.expansion_base i p hp)]
    · have h1 : m i = M.baseMoment c x i := by
        rw [hm]
        unfold MeshData.canonicalMoment
        rw [if_neg hi]
      rw [h1]
      simp only [hE, if_neg hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hg]
  have hmomrow : m (M.delaySlot j) = ((M.delayRow j).map (fun p => p.2 * m p.1)).sum := by
    have hds : M.IsDelaySlot (M.delaySlot j) := ⟨j, rfl⟩
    rw [hmE (M.delaySlot j)]
    have hstep : ∀ l, E (M.delaySlot j) l * g l = (∑ i, rowEntries (M.delayRow j) i * E i l) * g l := by
      intro l
      by_cases hl : M.IsDelaySlot l
      · simp only [hg, if_pos hl, mul_zero]
      · congr 1
        rw [sum_rowEntries_mul]
        simp only [hE, if_pos hds]
        rw [hM.expansion_consistent j l hl]
    rw [Finset.sum_congr rfl (fun l _ => hstep l), ← sum_rowEntries_mul]
    simp only [hmE, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfreerow : F (M.delaySlot j) = ((M.delayRow j).map (fun p => p.2 * F p.1)).sum := by
    rw [← sum_rowEntries_mul]
    simp only [hFdef, Matrix.mulVec, dotProduct]
    have : ∀ i, Sp.freeMap (M.delaySlot j) i = ∑ l, rowEntries (M.delayRow j) l * Sp.freeMap l i := by
      intro i
      rw [hM.delay_free j i, sum_rowEntries_mul]
    simp only [this, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot : M.delayVector j ⬝ᵥ Sp.stateOf x ζ = 0 := by
    have hs : Sp.stateOf x ζ = Sum.elim (m + F) ζ := by
      unfold CellSplit.stateOf
      rw [hmom x]
    rw [hs]
    unfold MeshData.delayVector
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [sum_rowEntries_mul, sum_rowEntries_mul, hmomrow, hfreerow]
    ring
  unfold Finite.quadValue
  rw [hM.delay_form j, Matrix.vecMulVec_mulVec, hdot]
  simp

end CellCoordinates

end CellCert

end Breakdown
