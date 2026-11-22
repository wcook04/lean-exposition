/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Relative Hamming distance

The distance and agreement fractions from §2 of Amireddy–Behera–Srinivasan–Sudan–
Willumsgaard, *A Simple Algebraic Proof of the PCP Theorem*. Fractions take values in
`ℚ`. Both fractions are zero on an empty domain; their sum is one on a nonempty domain.
The counting and triangle inequality reuse mathlib's `hammingDist`.
-/

namespace PCP.Algebraic

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- The fraction of coordinates at which two words disagree. -/
def relativeDistance (f g : ι → α) : ℚ :=
  (hammingDist f g : ℚ) / Fintype.card ι

/-- The fraction of coordinates at which two words agree. -/
def relativeAgreement (f g : ι → α) : ℚ :=
  ((univ.filter fun i => f i = g i).card : ℚ) / Fintype.card ι

@[simp] theorem relativeDistance_self (f : ι → α) : relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_comm (f g : ι → α) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, hammingDist_comm]

theorem relativeDistance_nonneg (f g : ι → α) : 0 ≤ relativeDistance f g := by
  unfold relativeDistance
  positivity

theorem relativeDistance_le_one (f g : ι → α) : relativeDistance f g ≤ 1 := by
  calc
    relativeDistance f g ≤ (Fintype.card ι : ℚ) / Fintype.card ι := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (hammingDist_le_card_fintype (x := f) (y := g))
    _ ≤ 1 := div_self_le_one _

theorem relativeDistance_triangle (f g h : ι → α) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  unfold relativeDistance
  rw [← add_div, ← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hammingDist_triangle f g h)
    (Nat.cast_nonneg _)

/-- Errors in a difference can only occur where one of its two inputs is wrong. -/
theorem relativeDistance_sub_le [AddGroup α] (f g h k : ι → α) :
    relativeDistance (fun i => f i - g i) (fun i => h i - k i) ≤
      relativeDistance f h + relativeDistance g k := by
  have ht := relativeDistance_triangle (fun i => f i - g i)
    (fun i => h i - g i) (fun i => h i - k i)
  simpa only [relativeDistance, hammingDist, ne_eq, sub_left_inj, sub_right_inj] using ht

/-- An injective relabeling of the alphabet preserves relative distance. -/
theorem relativeDistance_map {β : Type*} [DecidableEq β] (k : α → β)
    (hk : Function.Injective k) (f g : ι → α) :
    relativeDistance (fun i => k (f i)) (fun i => k (g i)) = relativeDistance f g := by
  simp only [relativeDistance, hammingDist_comp (fun _ => k) (fun _ => hk)]

/-- Distance on a product domain is the average of the distances of its rows. -/
theorem relativeDistance_prod {κ : Type*} [Fintype κ] (f g : ι × κ → α) :
    relativeDistance f g =
      (∑ i, relativeDistance (fun j => f (i, j)) (fun j => g (i, j))) / Fintype.card ι := by
  have hc : hammingDist f g = ∑ i, hammingDist (fun j => f (i, j)) (fun j => g (i, j)) := by
    simp only [hammingDist, card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [relativeDistance, hc, Nat.cast_sum, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div, div_div, mul_comm (Fintype.card κ : ℚ)]

/-- Reindexing a finite word by a bijection preserves relative distance. -/
theorem relativeDistance_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (f g : ι → α) :
    relativeDistance (fun i => f (e i)) (fun i => g (e i)) = relativeDistance f g := by
  unfold relativeDistance hammingDist
  rw [Fintype.card_congr e]
  congr 1
  apply congrArg Nat.cast
  exact card_equiv e (by simp)

/-- A code with constant pairwise distance scales the distance of concatenated words. -/
theorem relativeDistance_concatenate {κ β : Type*} [Fintype κ] [DecidableEq β]
    (E : α → κ → β) (δ : ℚ)
    (hE : ∀ a b, relativeDistance (E a) (E b) = if a = b then 0 else δ)
    (f g : ι → α) :
    relativeDistance (fun p : ι × κ => E (f p.1) p.2) (fun p => E (g p.1) p.2) =
      δ * relativeDistance f g := by
  rw [relativeDistance_prod]
  simp_rw [hE]
  rw [relativeDistance, hammingDist, Finset.natCast_card_filter, ← mul_div_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases h : f i = g i <;> simp [h]

@[simp] theorem relativeDistance_eq_zero_iff {f g : ι → α} :
    relativeDistance f g = 0 ↔ f = g := by
  constructor
  · intro h
    have hz : hammingDist f g = 0 := by
      rcases div_eq_zero_iff.mp h with hnum | hden
      · exact_mod_cast hnum
      · have hc : Fintype.card ι = 0 := by exact_mod_cast hden
        exact Nat.eq_zero_of_le_zero (hc ▸ hammingDist_le_card_fintype)
    exact hammingDist_eq_zero.mp hz
  · rintro rfl
    exact relativeDistance_self _

theorem relativeAgreement_comm (f g : ι → α) :
    relativeAgreement f g = relativeAgreement g f := by
  simp only [relativeAgreement, eq_comm]

/-- Applying a map to both words can only increase their agreement. -/
theorem relativeAgreement_le_map {β : Type*} [DecidableEq β] (k : α → β)
    (f g : ι → α) :
    relativeAgreement f g ≤ relativeAgreement (fun i => k (f i)) (fun i => k (g i)) := by
  unfold relativeAgreement
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ i, congrArg k (mem_filter.mp hi).2⟩

theorem relativeAgreement_nonneg (f g : ι → α) : 0 ≤ relativeAgreement f g := by
  unfold relativeAgreement
  positivity

theorem relativeAgreement_le_one (f g : ι → α) : relativeAgreement f g ≤ 1 := by
  calc
    relativeAgreement f g ≤ (Fintype.card ι : ℚ) / Fintype.card ι := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (card_le_univ (univ.filter fun i => f i = g i))
    _ ≤ 1 := div_self_le_one _

theorem relativeAgreement_add_relativeDistance [Nonempty ι] (f g : ι → α) :
    relativeAgreement f g + relativeDistance f g = 1 := by
  unfold relativeAgreement relativeDistance hammingDist
  rw [← add_div, ← Nat.cast_add, card_filter_add_card_filter_not]
  simp

theorem relativeAgreement_eq_one_sub_relativeDistance [Nonempty ι] (f g : ι → α) :
    relativeAgreement f g = 1 - relativeDistance f g := by
  have := relativeAgreement_add_relativeDistance f g
  linarith

@[simp] theorem relativeAgreement_self [Nonempty ι] (f : ι → α) :
    relativeAgreement f f = 1 := by
  simp [relativeAgreement_eq_one_sub_relativeDistance]

/-- Balls of radius less than half the minimum distance contain at most one codeword. -/
theorem eq_of_relativeDistance_le_of_separated {C : Set (ι → α)} {δ ε : ℚ}
    (hsep : ∀ f ∈ C, ∀ g ∈ C, f ≠ g → δ ≤ relativeDistance f g)
    (hradius : 2 * ε < δ) {f g w : ι → α} (hf : f ∈ C) (hg : g ∈ C)
    (hwf : relativeDistance w f ≤ ε) (hwg : relativeDistance w g ≤ ε) : f = g := by
  by_contra hne
  have hlow := hsep f hf g hg hne
  have htriangle := relativeDistance_triangle f w g
  rw [relativeDistance_comm f w] at htriangle
  linarith

end PCP.Algebraic
