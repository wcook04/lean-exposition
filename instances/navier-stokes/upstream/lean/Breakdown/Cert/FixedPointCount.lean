import Mathlib

namespace Breakdown
namespace GridSimplex

def Covers {n : ℕ} (g : Fin n → ℕ) (m : ℕ) : Prop :=
  ∀ l, l ≤ m → ∃ t, g t = l

def CoversFrom {n : ℕ} (g : Fin n → ℕ) (j : Fin n) (m : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ m → ∃ t, t ≠ j ∧ g t = l

namespace CountInternal

theorem injective_of_covers {k : ℕ} (g : Fin (k + 2) → ℕ) (hg : ∀ t, g t ≤ k + 1)
    (hc : Covers g (k + 1)) : Function.Injective g := by
  let G : Fin (k + 2) → Fin (k + 2) := fun t => ⟨g t, by have := hg t; omega⟩
  have hs : Function.Surjective G := by
    intro y
    obtain ⟨t, ht⟩ := hc y.val (by have := y.isLt; omega)
    exact ⟨t, Fin.ext ht⟩
  have hi : Function.Injective G := Finite.injective_iff_surjective.mpr hs
  intro a b hab
  apply hi
  exact Fin.ext hab

open Classical in
theorem card_doors_eq_two {k : ℕ} (g : Fin (k + 2) → ℕ) (hg : ∀ t, g t ≤ k + 1)
    (hc : ¬ Covers g (k + 1)) (j1 : Fin (k + 2)) (hj1 : CoversFrom g j1 (k + 1)) :
    (Finset.univ.filter fun j => CoversFrom g j (k + 1)).card = 2 := by
  have hsurj : ∀ l, 1 ≤ l → l ≤ k + 1 → ∃ u, g u = l := by
    intro l h1 h2
    obtain ⟨u, -, hu⟩ := hj1 l h1 h2
    exact ⟨u, hu⟩
  have hpos : ∀ t, 1 ≤ g t := by
    intro t
    by_contra h0
    apply hc
    intro l hl
    rcases Nat.eq_zero_or_pos l with h | h
    · exact ⟨t, by omega⟩
    · exact hsurj l h hl
  have hmaps : Set.MapsTo g (Finset.univ : Finset (Fin (k + 2)))
      (Finset.Icc 1 (k + 1)) := by
    intro t _
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨hpos t, hg t⟩
  have hlt : (Finset.Icc 1 (k + 1)).card < (Finset.univ : Finset (Fin (k + 2))).card := by
    simp
  obtain ⟨t1, -, t2, -, h12, hg12⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have key : ∀ a b, a ≠ b → g a = g b → CoversFrom g a (k + 1) := by
    intro a b hab hgab l h1 h2
    obtain ⟨u, hu⟩ := hsurj l h1 h2
    by_cases hua : u = a
    · subst hua
      exact ⟨b, fun h => hab h.symm, hgab.symm.trans hu⟩
    · exact ⟨u, hua, hu⟩
  have hset : (Finset.univ.filter fun j => CoversFrom g j (k + 1)) = {t1, t2} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      push Not at hne
      obtain ⟨hj1', hj2'⟩ := hne
      obtain ⟨t, htj, ht⟩ := hj (g j) (hpos j) (hg j)
      obtain ⟨s, hsj, hs2, hsg⟩ : ∃ s, s ≠ j ∧ s ≠ t2 ∧ g s = g j := by
        by_cases hj2 : g j = g t2
        · exact ⟨t1, fun h => hj1' h.symm, h12, hg12.trans hj2.symm⟩
        · refine ⟨t, htj, ?_, ht⟩
          rintro rfl
          exact hj2 ht.symm
      have hsub : Finset.Icc 1 (k + 1) ⊆
          (((Finset.univ : Finset (Fin (k + 2))).erase t2).erase j).image g := by
        intro l hl
        rw [Finset.mem_Icc] at hl
        obtain ⟨u, hu⟩ := hsurj l hl.1 hl.2
        rw [Finset.mem_image]
        by_cases hu2 : u = t2
        · subst hu2
          refine ⟨t1, ?_, hg12.trans hu⟩
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨fun h => hj1' h.symm, h12⟩
        · by_cases huj : u = j
          · subst huj
            refine ⟨s, ?_, hsg.trans hu⟩
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨hsj, hs2⟩
          · refine ⟨u, ?_, hu⟩
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨huj, hu2⟩
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.card_image_le (s := ((Finset.univ : Finset (Fin (k + 2))).erase t2).erase j) (f := g)
      have hj2mem : j ∈ (Finset.univ : Finset (Fin (k + 2))).erase t2 := by
        simp [hj2']
      rw [Finset.card_erase_of_mem hj2mem, Finset.card_erase_of_mem (Finset.mem_univ _)] at hc2
      simp at hc1 hc2
      omega
    · rintro (rfl | rfl)
      · exact key j t2 h12 hg12
      · exact key j t1 (fun h => h12 h.symm) hg12.symm
  rw [hset, Finset.card_pair h12]

end CountInternal

open Classical in
theorem card_coversFrom_mod_two {k : ℕ} (g : Fin (k + 2) → ℕ) (hg : ∀ t, g t ≤ k + 1) :
    (Finset.univ.filter fun j => CoversFrom g j (k + 1)).card % 2 =
      if Covers g (k + 1) then 1 else 0 := by
  by_cases hc : Covers g (k + 1)
  · rw [if_pos hc]
    obtain ⟨j0, hj0⟩ := hc 0 (Nat.zero_le _)
    have hinj : Function.Injective g := CountInternal.injective_of_covers g hg hc
    have hset : (Finset.univ.filter fun j => CoversFrom g j (k + 1)) = {j0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        by_contra hne
        have hpos : 1 ≤ g j := by
          rcases Nat.eq_zero_or_pos (g j) with h | h
          · exact absurd (hinj (h.trans hj0.symm)) hne
          · exact h
        obtain ⟨t, htj, ht⟩ := hj (g j) hpos (hg j)
        exact htj (hinj ht)
      · rintro rfl l hl1 hl2
        obtain ⟨t, ht⟩ := hc l hl2
        refine ⟨t, ?_, ht⟩
        rintro rfl
        omega
    rw [hset, Finset.card_singleton]
  · rw [if_neg hc]
    by_cases hd : ∃ j, CoversFrom g j (k + 1)
    · obtain ⟨j1, hj1⟩ := hd
      rw [CountInternal.card_doors_eq_two g hg hc j1 hj1]
    · push Not at hd
      have : (Finset.univ.filter fun j => CoversFrom g j (k + 1)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun x _ => hd x
      rw [this, Finset.card_empty]

end GridSimplex
end Breakdown
