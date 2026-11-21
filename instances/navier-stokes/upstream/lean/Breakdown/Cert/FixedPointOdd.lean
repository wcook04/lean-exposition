import Breakdown.Cert.FixedPointPivot
import Breakdown.Cert.FixedPointFace

namespace Breakdown
namespace GridSimplex

theorem odd_card_fullSet {k p : ℕ} (hp : 0 < p) (L : (Fin k → ℕ) → ℕ)
    (hL : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → L x ≤ k)
    (hhigh : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → (i : ℕ) + 1 ≤ L x)
    (hne : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = 0 → L x ≠ (i : ℕ) + 1) :
    Odd (fullSet (p := p) L).card := by
  induction k with
  | zero =>
    have h : fullSet (p := p) L = Finset.univ := by
      ext s
      simp only [Finset.mem_univ, iff_true, mem_fullSet]
      intro l hl
      refine ⟨0, ?_⟩
      show L (vertex s.1 s.2 ((0 : Fin 1) : ℕ)) = l
      have := hL (vertex s.1 s.2 ((0 : Fin 1) : ℕ)) (vertex_le s.1 s.2 _)
      omega
    rw [h, Finset.card_univ]
    simp
  | succ k ih =>
    have hface := card_boundaryDoorSet (p := p) hp L hhigh hne
    have hmod := card_fullSet_mod_two_eq (p := p) L hL
    have hcons : ∀ y : Fin k → ℕ, (∀ j, y j ≤ p) → ∀ j, (Fin.cons p y : Fin (k + 1) → ℕ) j ≤ p := by
      intro y hy j
      cases j using Fin.cases with
      | zero => simp
      | succ i => simpa using hy i
    have hpos : ∀ y : Fin k → ℕ, (∀ j, y j ≤ p) → 1 ≤ L (Fin.cons p y) := by
      intro y hy
      have := hhigh (Fin.cons p y) (hcons y hy) 0 (by simp)
      simpa using this
    have hodd := ih (fun y : Fin k → ℕ => L (Fin.cons p y) - 1) ?_ ?_ ?_
    · rw [Nat.odd_iff] at hodd ⊢
      rw [hmod, hface]
      exact hodd
    · intro y hy
      have := hL (Fin.cons p y) (hcons y hy)
      omega
    · intro y hy i hi
      have := hhigh (Fin.cons p y) (hcons y hy) i.succ (by simpa using hi)
      simp only [Fin.val_succ] at this
      omega
    · intro y hy i hi
      have := hne (Fin.cons p y) (hcons y hy) i.succ (by simpa using hi)
      have h1 := hpos y hy
      simp only [Fin.val_succ] at this
      omega

theorem exists_complete_simplex {k p : ℕ} (hp : 0 < p) (lab : (Fin k → ℕ) → Fin k → Prop)
    (h0 : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = 0 → ¬ lab x i)
    (h1 : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → lab x i) :
    ∃ (v : Fin k → Fin p) (τ : Equiv.Perm (Fin k)), ∀ i,
      (∃ j : Fin (k + 1), ¬ lab (vertex v τ (j : ℕ)) i) ∧
        (∃ j : Fin (k + 1), lab (vertex v τ (j : ℕ)) i) := by
  classical
  set L : (Fin k → ℕ) → ℕ := fun x => (Finset.univ.filter (lab x)).sup fun i => (i : ℕ) + 1 with hLdef
  have hle : ∀ x i, lab x i → (i : ℕ) + 1 ≤ L x := by
    intro x i hi
    exact Finset.le_sup (f := fun i : Fin k => (i : ℕ) + 1) (by simpa using hi)
  have key : ∀ x (n : ℕ), L x = n + 1 → ∃ i, lab x i ∧ (i : ℕ) = n := by
    intro x n h
    rcases (Finset.univ.filter (lab x)).eq_empty_or_nonempty with hs | hs
    · simp [hLdef, hs] at h
    · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup _ hs (fun i : Fin k => (i : ℕ) + 1)
      refine ⟨i, (Finset.mem_filter.1 hi).2, ?_⟩
      have : L x = (i : ℕ) + 1 := he
      omega
  have hLk : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → L x ≤ k := by
    intro x _
    refine Finset.sup_le ?_
    intro i _
    exact i.isLt
  have hodd := odd_card_fullSet hp L hLk
    (fun x hx i hi => hle x i (h1 x hx i hi))
    (fun x hx i hi he => by
      obtain ⟨i', hl, hi'⟩ := key x i he
      have : i' = i := Fin.ext hi'
      subst this
      exact h0 x hx i' hi hl)
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hodd.pos
  have hfull := (mem_fullSet L s).1 hs
  refine ⟨s.1, s.2, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := hfull 0 (Nat.zero_le _)
    refine ⟨t, fun hl => ?_⟩
    have := hle _ _ hl
    simp only at ht
    omega
  · obtain ⟨t, ht⟩ := hfull ((i : ℕ) + 1) i.isLt
    obtain ⟨i', hl, hi'⟩ := key _ _ ht
    have : i' = i := Fin.ext hi'
    subst this
    exact ⟨t, hl⟩

end GridSimplex
end Breakdown
