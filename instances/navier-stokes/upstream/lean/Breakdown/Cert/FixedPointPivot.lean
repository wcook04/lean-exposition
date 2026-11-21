import Breakdown.Cert.FixedPointDefs

namespace Breakdown
namespace GridSimplex

theorem card_doorSet_mod_two {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (hL : ∀ x : Fin (k + 1) → ℕ, (∀ i, x i ≤ p) → L x ≤ k + 1) :
    (doorSet (p := p) L).card % 2 = (fullSet (p := p) L).card % 2 := by
  classical
  have hd : (doorSet (p := p) L).card =
      ∑ s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)),
        (Finset.univ.filter fun j => IsDoor L s.1 s.2 j).card := by
    simp only [doorSet, Finset.card_filter, Fintype.sum_prod_type]
  have hf : (fullSet (p := p) L).card =
      ∑ s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)),
        (if IsFull L s.1 s.2 then 1 else 0) := by
    simp only [fullSet, Finset.card_filter]
  rw [hd, hf, Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have key : IsFull L s.1 s.2 ↔
      Covers (fun t : Fin (k + 2) => L (vertex s.1 s.2 (t : ℕ))) (k + 1) := Iff.rfl
  have hc := card_coversFrom_mod_two (fun t : Fin (k + 2) => L (vertex s.1 s.2 (t : ℕ)))
    (fun t => hL _ (vertex_le _ _ _))
  have hc' : (Finset.univ.filter fun j => IsDoor L s.1 s.2 j).card % 2 =
      if Covers (fun t : Fin (k + 2) => L (vertex s.1 s.2 (t : ℕ))) (k + 1) then 1 else 0 := by
    rw [← hc]
    rfl
  rw [hc']
  by_cases h : Covers (fun t : Fin (k + 2) => L (vertex s.1 s.2 (t : ℕ))) (k + 1)
  · rw [if_pos h, if_pos (key.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (key.1 h'))]

namespace PivotInternal

def up {n p : ℕ} (v : Fin n → Fin p) (i0 : Fin n) : Fin n → Fin p := fun i =>
  if i = i0 then ⟨min ((v i : ℕ) + 1) (p - 1), by have := (v i).isLt; omega⟩ else v i

def down {n p : ℕ} (v : Fin n → Fin p) (i1 : Fin n) : Fin n → Fin p := fun i =>
  if i = i1 then ⟨(v i : ℕ) - 1, by have := (v i).isLt; omega⟩ else v i

theorem coe_up {n p : ℕ} (v : Fin n → Fin p) (i0 i : Fin n) :
    (up v i0 i : ℕ) = if i = i0 then min ((v i : ℕ) + 1) (p - 1) else v i := by
  unfold up
  split_ifs <;> rfl

theorem coe_down {n p : ℕ} (v : Fin n → Fin p) (i1 i : Fin n) :
    (down v i1 i : ℕ) = if i = i1 then (v i : ℕ) - 1 else v i := by
  unfold down
  split_ifs <;> rfl

def lo {k : ℕ} (j : Fin (k + 2)) : Fin (k + 1) := ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩

def hi {k : ℕ} (j : Fin (k + 2)) : Fin (k + 1) := ⟨min (j : ℕ) k, by omega⟩

def pivot {k p : ℕ} (s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2)) :
    (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2) :=
  if s.2.2 = 0 then
    (up s.1 (s.2.1.symm 0), s.2.1.trans (finRotate (k + 1)).symm, Fin.last (k + 1))
  else if s.2.2 = Fin.last (k + 1) then
    (down s.1 (s.2.1.symm (Fin.last k)), s.2.1.trans (finRotate (k + 1)), 0)
  else (s.1, s.2.1.trans (Equiv.swap (lo s.2.2) (hi s.2.2)), s.2.2)

theorem last_ne_zero' (k : ℕ) : (Fin.last (k + 1) : Fin (k + 2)) ≠ 0 := by
  simp [Fin.ext_iff]

theorem pivot_zero {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1))) :
    pivot (v, τ, 0) =
      (up v (τ.symm 0), τ.trans (finRotate (k + 1)).symm, Fin.last (k + 1)) := by
  simp [pivot]

theorem pivot_last {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1))) :
    pivot (v, τ, Fin.last (k + 1)) =
      (down v (τ.symm (Fin.last k)), τ.trans (finRotate (k + 1)), 0) := by
  simp [pivot, last_ne_zero' k]

theorem pivot_mid {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) (h0 : j ≠ 0) (hl : j ≠ Fin.last (k + 1)) :
    pivot (v, τ, j) = (v, τ.trans (Equiv.swap (lo j) (hi j)), j) := by
  simp [pivot, h0, hl]

theorem coe_rot_symm {k : ℕ} (m : Fin (k + 1)) :
    ((finRotate (k + 1)).symm m : ℕ) = if (m : ℕ) = 0 then k else (m : ℕ) - 1 := by
  by_cases hm : m = 0
  · have h : (finRotate (k + 1)).symm 0 = Fin.last k := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    subst hm
    simp [h]
  · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
    rw [coe_finRotate_symm_of_ne_zero hm, if_neg hm']

theorem coe_rot {k : ℕ} (m : Fin (k + 1)) :
    (finRotate (k + 1) m : ℕ) = if (m : ℕ) = k then 0 else (m : ℕ) + 1 := by
  rw [coe_finRotate]
  by_cases hm : (m : ℕ) = k
  · rw [if_pos hm, if_pos (Fin.ext (by simp [hm]))]
  · rw [if_neg hm, if_neg (fun h => hm (by simp [h]))]

theorem vertex_up {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (hv : (v (τ.symm 0) : ℕ) + 1 < p) (t : ℕ) (ht : t ≤ k) :
    vertex (up v (τ.symm 0)) (τ.trans (finRotate (k + 1)).symm) t = vertex v τ (t + 1) := by
  funext i
  simp only [vertex, coe_up, Equiv.trans_apply, coe_rot_symm]
  have hτ := (τ i).isLt
  by_cases hi : i = τ.symm 0
  · have h0 : τ i = 0 := by rw [hi]; simp
    rw [← hi] at hv
    rw [if_pos hi, h0, Fin.val_zero]
    split_ifs <;> omega
  · have h' : (τ i : ℕ) ≠ 0 := fun h => hi (by rw [← Fin.ext (a := τ i) (b := 0) h]; simp)
    rw [if_neg hi]
    split_ifs <;> omega

theorem vertex_down {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (hv : (v (τ.symm (Fin.last k)) : ℕ) ≠ 0) (t : ℕ) (ht : t ≤ k) :
    vertex (down v (τ.symm (Fin.last k))) (τ.trans (finRotate (k + 1))) (t + 1) =
      vertex v τ t := by
  funext i
  simp only [vertex, coe_down, Equiv.trans_apply, coe_rot]
  have hτ := (τ i).isLt
  by_cases hi : i = τ.symm (Fin.last k)
  · have h0 : τ i = Fin.last k := by rw [hi]; simp
    rw [← hi] at hv
    rw [if_pos hi, h0, Fin.val_last]
    split_ifs <;> omega
  · have h' : (τ i : ℕ) ≠ k := fun h => hi (by
      rw [← Fin.ext (a := τ i) (b := Fin.last k) (by simp [h])]; simp)
    rw [if_neg hi]
    split_ifs <;> omega

theorem vertex_swap {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) (h0 : j ≠ 0) (hl : j ≠ Fin.last (k + 1)) (t : ℕ) (ht : t ≠ j) :
    vertex v (τ.trans (Equiv.swap (lo j) (hi j))) t = vertex v τ t := by
  have hj0 : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have hjl : (j : ℕ) ≠ k + 1 := fun h => hl (Fin.ext (by simp [h]))
  have hj := j.isLt
  funext i
  simp only [vertex, Equiv.trans_apply]
  have hτ := (τ i).isLt
  simp only [Equiv.swap_apply_def]
  split_ifs <;>
    simp only [Fin.ext_iff, lo, hi] at * <;> omega

theorem not_boundary_zero {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (h : ¬ OnBoundary v τ 0) : (v (τ.symm 0) : ℕ) + 1 < p := by
  have := (v (τ.symm 0)).isLt
  have h' : (v (τ.symm 0) : ℕ) + 1 ≠ p := fun e => h (Or.inl ⟨rfl, e⟩)
  omega

theorem not_boundary_last {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (h : ¬ OnBoundary v τ (Fin.last (k + 1))) : (v (τ.symm (Fin.last k)) : ℕ) ≠ 0 :=
  fun e => h (Or.inr ⟨rfl, e⟩)

theorem symm_rot_symm {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) :
    (τ.trans (finRotate (k + 1)).symm).symm (Fin.last k) = τ.symm 0 := by
  simp

theorem symm_rot {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) :
    (τ.trans (finRotate (k + 1))).symm 0 = τ.symm (Fin.last k) := by
  have h : (finRotate (k + 1)).symm 0 = Fin.last k := by
    rw [Equiv.symm_apply_eq, finRotate_last]
  simp [h]

theorem pivot_pivot {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) (hnb : ¬ OnBoundary v τ j) : pivot (pivot (v, τ, j)) = (v, τ, j) := by
  by_cases h0 : j = 0
  · subst h0
    have hv := not_boundary_zero v τ hnb
    rw [pivot_zero, pivot_last, symm_rot_symm]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext i
      apply Fin.ext
      simp only [coe_down, coe_up]
      split_ifs with h
      · subst h
        omega
      · rfl
    · ext i
      simp
  by_cases hl : j = Fin.last (k + 1)
  · subst hl
    have hv := not_boundary_last v τ hnb
    have hlt := (v (τ.symm (Fin.last k))).isLt
    rw [pivot_last, pivot_zero, symm_rot]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext i
      apply Fin.ext
      simp only [coe_down, coe_up]
      split_ifs with h
      · subst h
        omega
      · rfl
    · ext i
      simp
  · rw [pivot_mid v τ j h0 hl, pivot_mid _ _ j h0 hl]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    ext i
    simp

theorem pivot_ne {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) : pivot (v, τ, j) ≠ (v, τ, j) := by
  intro h
  by_cases h0 : j = 0
  · subst h0
    rw [pivot_zero] at h
    exact last_ne_zero' k (congrArg (fun s => s.2.2) h)
  by_cases hl : j = Fin.last (k + 1)
  · subst hl
    rw [pivot_last] at h
    exact last_ne_zero' k (congrArg (fun s => s.2.2) h).symm
  · rw [pivot_mid v τ j h0 hl] at h
    have e := congrArg (fun s => s.2.1 (τ.symm (lo j))) h
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at e
    have hj0 : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    have hjl : (j : ℕ) ≠ k + 1 := fun h => hl (Fin.ext (by simp [h]))
    have hj := j.isLt
    simp only [Fin.ext_iff, lo, hi] at e
    omega

theorem pivot_not_boundary {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) (hnb : ¬ OnBoundary v τ j) :
    ¬ OnBoundary (pivot (v, τ, j)).1 (pivot (v, τ, j)).2.1 (pivot (v, τ, j)).2.2 := by
  by_cases h0 : j = 0
  · subst h0
    have hv := not_boundary_zero v τ hnb
    rw [pivot_zero]
    unfold OnBoundary
    dsimp only
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact last_ne_zero' k h
    · rw [symm_rot_symm, coe_up, if_pos rfl] at h
      omega
  by_cases hl : j = Fin.last (k + 1)
  · subst hl
    have hv := not_boundary_last v τ hnb
    have hlt := (v (τ.symm (Fin.last k))).isLt
    rw [pivot_last]
    unfold OnBoundary
    dsimp only
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rw [symm_rot, coe_down, if_pos rfl] at h
      omega
    · exact last_ne_zero' k h.symm
  · rw [pivot_mid v τ j h0 hl]
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h0 h
    · exact hl h

theorem pivot_door {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ) (v : Fin (k + 1) → Fin p)
    (τ : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 2)) (hd : IsDoor L v τ j)
    (hnb : ¬ OnBoundary v τ j) :
    IsDoor L (pivot (v, τ, j)).1 (pivot (v, τ, j)).2.1 (pivot (v, τ, j)).2.2 := by
  by_cases h0 : j = 0
  · subst h0
    have hv := not_boundary_zero v τ hnb
    rw [pivot_zero]
    intro l h1 h2
    obtain ⟨t, ht, hl⟩ := hd l h1 h2
    have htv : (t : ℕ) ≠ 0 := fun h => ht (Fin.ext h)
    have htl := t.isLt
    refine ⟨⟨(t : ℕ) - 1, by omega⟩, fun h => ?_, ?_⟩
    · rw [Fin.ext_iff, Fin.val_last] at h
      simp only at h
      omega
    · show L (vertex _ _ ((t : ℕ) - 1)) = l
      rw [vertex_up v τ hv _ (by omega), show (t : ℕ) - 1 + 1 = t by omega]
      exact hl
  by_cases hl' : j = Fin.last (k + 1)
  · subst hl'
    have hv := not_boundary_last v τ hnb
    rw [pivot_last]
    intro l h1 h2
    obtain ⟨t, ht, hl⟩ := hd l h1 h2
    have htv : (t : ℕ) ≠ k + 1 := fun h => ht (Fin.ext (by simp [h]))
    have htl := t.isLt
    refine ⟨⟨(t : ℕ) + 1, by omega⟩, fun h => ?_, ?_⟩
    · rw [Fin.ext_iff] at h
      simp at h
    · show L (vertex _ _ ((t : ℕ) + 1)) = l
      rw [vertex_down v τ hv _ (by omega)]
      exact hl
  · rw [pivot_mid v τ j h0 hl']
    intro l h1 h2
    obtain ⟨t, ht, hl⟩ := hd l h1 h2
    refine ⟨t, ht, ?_⟩
    show L (vertex _ _ (t : ℕ)) = l
    rw [vertex_swap v τ j h0 hl' _ (fun h => ht (Fin.ext h))]
    exact hl

end PivotInternal

open Classical in
theorem even_card_interior_doors {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ) :
    Even ((doorSet (p := p) L).filter fun s => ¬ OnBoundary s.1 s.2.1 s.2.2).card := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have hmem : ∀ a ∈ (doorSet (p := p) L).filter (fun s => ¬ OnBoundary s.1 s.2.1 s.2.2),
      IsDoor L a.1 a.2.1 a.2.2 ∧ ¬ OnBoundary a.1 a.2.1 a.2.2 := by
    intro a ha
    rw [Finset.mem_filter, mem_doorSet] at ha
    exact ha
  have key := Finset.sum_involution
    (s := (doorSet (p := p) L).filter fun s => ¬ OnBoundary s.1 s.2.1 s.2.2)
    (f := fun _ => (1 : ZMod 2)) (fun a _ => PivotInternal.pivot a) (fun _ _ => by decide)
    (fun a _ _ => PivotInternal.pivot_ne a.1 a.2.1 a.2.2)
    (fun a ha => by
      obtain ⟨hd, hnb⟩ := hmem a ha
      rw [Finset.mem_filter, mem_doorSet]
      exact ⟨PivotInternal.pivot_door L a.1 a.2.1 a.2.2 hd hnb,
        PivotInternal.pivot_not_boundary a.1 a.2.1 a.2.2 hnb⟩)
    (fun a ha => PivotInternal.pivot_pivot a.1 a.2.1 a.2.2 (hmem a ha).2)
  simpa using key

theorem card_fullSet_mod_two_eq {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (hL : ∀ x : Fin (k + 1) → ℕ, (∀ i, x i ≤ p) → L x ≤ k + 1) :
    (fullSet (p := p) L).card % 2 = (boundaryDoorSet (p := p) L).card % 2 := by
  classical
  have h1 := card_doorSet_mod_two (p := p) L hL
  have h2 := even_card_interior_doors (p := p) L
  have h3 := Finset.card_filter_add_card_filter_not
    (s := doorSet (p := p) L) (fun s => OnBoundary s.1 s.2.1 s.2.2)
  have h4 : boundaryDoorSet (p := p) L =
      (doorSet (p := p) L).filter fun s => OnBoundary s.1 s.2.1 s.2.2 := by
    ext s
    simp [boundaryDoorSet]
  rw [h4]
  obtain ⟨r, hr⟩ := h2
  omega

end GridSimplex
end Breakdown
