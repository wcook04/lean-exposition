import Breakdown.Cert.FixedPointDefs

namespace Breakdown
namespace GridSimplex
namespace FaceInternal

theorem vertex_cons_succ {k p : ℕ} (c : Fin p) (w : Fin k → Fin p) (σ : Equiv.Perm (Fin k))
    (hc : (c : ℕ) + 1 = p) (t : ℕ) :
    vertex (Fin.cons c w : Fin (k + 1) → Fin p) (Equiv.Perm.decomposeFin.symm (0, σ)) (t + 1) =
      (Fin.cons p (vertex w σ t) : Fin (k + 1) → ℕ) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [vertex, Equiv.Perm.decomposeFin_symm_apply_zero, hc]
  · simp [vertex, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.val_succ]

theorem label_pos {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (hhigh : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → (i : ℕ) + 1 ≤ L x)
    (y : Fin k → ℕ) (hy : ∀ j, y j ≤ p) : 1 ≤ L (Fin.cons p y) := by
  have h := hhigh (Fin.cons p y) (fun j => Fin.cases (by simp) (fun j => by simpa using hy j) j) 0
    (by simp)
  simpa using h

theorem isDoor_cons_iff {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (hhigh : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → (i : ℕ) + 1 ≤ L x)
    (c : Fin p) (w : Fin k → Fin p) (σ : Equiv.Perm (Fin k)) (hc : (c : ℕ) + 1 = p) :
    IsDoor L (Fin.cons c w : Fin (k + 1) → Fin p) (Equiv.Perm.decomposeFin.symm (0, σ)) 0 ↔
      IsFull (fun y : Fin k → ℕ => L (Fin.cons p y) - 1) w σ := by
  unfold IsDoor IsFull CoversFrom Covers
  have hv : ∀ s : Fin (k + 1),
      vertex (Fin.cons c w : Fin (k + 1) → Fin p) (Equiv.Perm.decomposeFin.symm (0, σ))
        ((s.succ : Fin (k + 2)) : ℕ) = Fin.cons p (vertex w σ s) := fun s => by
    rw [Fin.val_succ]
    exact vertex_cons_succ c w σ hc s
  have hpos : ∀ s : Fin (k + 1), 1 ≤ L (Fin.cons p (vertex w σ (s : ℕ))) :=
    fun s => label_pos L hhigh _ (vertex_le w σ s)
  constructor
  · intro h l hl
    obtain ⟨t, ht0, ht⟩ := h (l + 1) (by omega) (by omega)
    obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.mpr ht0
    refine ⟨s, ?_⟩
    beta_reduce at ht ⊢
    rw [hv] at ht
    omega
  · intro h l hl1 hl2
    obtain ⟨s, hs⟩ := h (l - 1) (by omega)
    refine ⟨s.succ, Fin.succ_ne_zero s, ?_⟩
    beta_reduce at hs ⊢
    rw [hv]
    have := hpos s
    omega

theorem boundary_shape {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (hhigh : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → (i : ℕ) + 1 ≤ L x)
    (hne : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = 0 → L x ≠ (i : ℕ) + 1)
    (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 2))
    (hd : IsDoor L v τ j) (hb : OnBoundary v τ j) :
    j = 0 ∧ τ 0 = 0 ∧ (v 0 : ℕ) + 1 = p := by
  unfold IsDoor CoversFrom at hd
  rcases hb with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
  · have hτ : τ.symm 0 = 0 := by
      obtain ⟨t, ht0, ht⟩ := hd 1 le_rfl (by omega)
      have ht0' : (t : ℕ) ≠ 0 := fun h => ht0 (Fin.ext (by rw [Fin.val_zero]; exact h))
      have hc : vertex v τ t (τ.symm 0) = p := by
        simp only [vertex, Equiv.apply_symm_apply, Fin.val_zero]
        rw [if_pos (Nat.pos_of_ne_zero ht0')]
        exact h0
      have h2 := hhigh _ (vertex_le v τ t) _ hc
      beta_reduce at ht
      rw [ht] at h2
      exact Fin.ext (by rw [Fin.val_zero]; omega)
    refine ⟨rfl, ?_, ?_⟩
    · have h4 := hτ
      rw [Equiv.symm_apply_eq] at h4
      exact h4.symm
    · rw [hτ] at h0
      exact h0
  · exfalso
    have hlt := (τ.symm (Fin.last k)).isLt
    obtain ⟨t, ht0, ht⟩ := hd ((τ.symm (Fin.last k) : ℕ) + 1) (by omega) (by omega)
    have ht1 : (t : ℕ) ≠ k + 1 := fun h => ht0 (Fin.ext (by rw [Fin.val_last]; exact h))
    have ht2 := t.isLt
    have hc : vertex v τ t (τ.symm (Fin.last k)) = 0 := by
      simp only [vertex, Equiv.apply_symm_apply, Fin.val_last]
      rw [if_neg (by omega)]
      simpa using h1
    exact hne _ (vertex_le v τ t) _ hc ht

end FaceInternal

open FaceInternal in
theorem card_boundaryDoorSet {k p : ℕ} (hp : 0 < p) (L : (Fin (k + 1) → ℕ) → ℕ)
    (hhigh : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → (i : ℕ) + 1 ≤ L x)
    (hne : ∀ x : Fin (k + 1) → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = 0 → L x ≠ (i : ℕ) + 1) :
    (boundaryDoorSet (p := p) L).card =
      (fullSet (p := p) fun y : Fin k → ℕ => L (Fin.cons p y) - 1).card := by
  classical
  have hp1 : p - 1 < p := by omega
  have key : ∀ s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2),
      s ∈ boundaryDoorSet (p := p) L →
        s = (Fin.cons ⟨p - 1, hp1⟩ (Fin.tail s.1),
          Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin s.2.1).2), 0) := by
    rintro ⟨v, τ, j⟩ hs
    rw [mem_boundaryDoorSet] at hs
    obtain ⟨rfl, hτ, hv⟩ := boundary_shape L hhigh hne v τ j hs.1 hs.2
    have h1 : (Equiv.Perm.decomposeFin τ).1 = 0 := by
      have h3 := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin τ).1
        (Equiv.Perm.decomposeFin τ).2
      rw [Prod.mk.eta, Equiv.symm_apply_apply] at h3
      rw [← h3, hτ]
    have h2 : v 0 = ⟨p - 1, hp1⟩ := Fin.ext (by simp only; omega)
    simp only [Prod.mk.injEq, and_true]
    refine ⟨?_, ?_⟩
    · rw [← h2, Fin.cons_self_tail]
    · rw [← h1, Prod.mk.eta, Equiv.symm_apply_apply]
  refine Finset.card_nbij' (fun s => (Fin.tail s.1, (Equiv.Perm.decomposeFin s.2.1).2))
    (fun s => (Fin.cons ⟨p - 1, hp1⟩ s.1, Equiv.Perm.decomposeFin.symm (0, s.2), 0))
    ?_ ?_ ?_ ?_
  · intro s hs
    have hs' : s ∈ boundaryDoorSet (p := p) L := hs
    have he := key s hs'
    rw [Finset.mem_coe, mem_fullSet]
    rw [he, mem_boundaryDoorSet] at hs'
    exact (isDoor_cons_iff L hhigh ⟨p - 1, hp1⟩ _ _ (by simp only; omega)).mp hs'.1
  · intro s hs
    have hs' : s ∈ fullSet (p := p) fun y : Fin k → ℕ => L (Fin.cons p y) - 1 := hs
    rw [mem_fullSet] at hs'
    rw [Finset.mem_coe, mem_boundaryDoorSet]
    refine ⟨(isDoor_cons_iff L hhigh ⟨p - 1, hp1⟩ _ _ (by simp only; omega)).mpr hs', ?_⟩
    left
    refine ⟨rfl, ?_⟩
    have h0 : (Equiv.Perm.decomposeFin.symm (0, s.2)).symm (0 : Fin (k + 1)) = 0 := by
      rw [Equiv.symm_apply_eq, Equiv.Perm.decomposeFin_symm_apply_zero]
    simp only
    rw [h0, Fin.cons_zero]
    simp only
    omega
  · intro s hs
    exact (key s hs).symm
  · intro s _
    simp only [Fin.tail_cons, Equiv.apply_symm_apply]

end GridSimplex
end Breakdown
