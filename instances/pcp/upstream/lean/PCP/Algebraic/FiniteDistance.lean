/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Distance

/-!
# Finite sampling bounds for relative distance

Error containment, a two-input union bound, and averaging over an independent
finite seed. These are normalized rational statements, including empty word
domains where possible. Nonempty seed hypotheses are explicit.
-/

namespace PCP.Algebraic

open Finset

variable {ι κ α β γ : Type*} [Fintype ι] [DecidableEq α]

/-- Containment of disagreement events implies the corresponding probability bound. -/
theorem relativeDistance_le_of_disagreement [DecidableEq β]
    (f g : ι → α) (u v : ι → β) (h : ∀ i, f i ≠ g i → u i ≠ v i) :
    relativeDistance f g ≤ relativeDistance u v := by
  unfold relativeDistance hammingDist
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ i, h i (mem_filter.mp hi).2⟩

/-- Combining two answers can fail only if at least one answer is wrong. -/
theorem relativeDistance_zipWith_le [DecidableEq β] [DecidableEq γ]
    (op : α → β → γ) (f g : ι → α) (u v : ι → β) :
    relativeDistance (fun i => op (f i) (u i)) (fun i => op (g i) (v i)) ≤
      relativeDistance f g + relativeDistance u v := by
  have h₁ := relativeDistance_le_of_disagreement
    (fun i => op (f i) (u i)) (fun i => op (g i) (u i)) f g
    (fun i hfg h => hfg (by rw [h]))
  have h₂ := relativeDistance_le_of_disagreement
    (fun i => op (g i) (u i)) (fun i => op (g i) (v i)) u v
    (fun i huv h => huv (by rw [h]))
  exact (relativeDistance_triangle _ _ _).trans (add_le_add h₁ h₂)

/-- Distinct constant words disagree everywhere on a nonempty domain. -/
theorem relativeDistance_const [Nonempty ι] (a b : α) :
    relativeDistance (fun _ : ι => a) (fun _ => b) = if a = b then 0 else 1 := by
  by_cases h : a = b
  · simp [h]
  · simp [relativeDistance, hammingDist, h, Fintype.card_ne_zero]

/-- An unused independent nonempty seed does not change the error fraction. -/
theorem relativeDistance_comp_fst [Fintype κ] [Nonempty κ] (f g : ι → α) :
    relativeDistance (fun p : ι × κ => f p.1) (fun p => g p.1) = relativeDistance f g := by
  simpa only [one_mul] using
    (relativeDistance_concatenate (fun a : α => fun _ : κ => a) 1
      (relativeDistance_const (ι := κ)) f g)

/-- Uniform row bounds survive averaging over a nonempty finite collection of rows. -/
theorem relativeDistance_prod_le [Fintype κ] [Nonempty ι]
    (f g : ι × κ → α) {ε : ℚ}
    (h : ∀ i, relativeDistance (fun j => f (i, j)) (fun j => g (i, j)) ≤ ε) :
    relativeDistance f g ≤ ε := by
  rw [relativeDistance_prod]
  have hc : (0 : ℚ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => h i)
  simpa [mul_comm] using hs

end PCP.Algebraic
