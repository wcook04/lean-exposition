/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteDistance

/-!
# Accepting unused seeds in a larger finite sample space

An injective seed embedding preserves the number of rejecting samples when the
new test agrees on the image and accepts outside it. Normalizing by the actual
cardinalities gives the exact rejection loss. This permits whole-field sampling
in place of nonzero-field sampling while preserving perfect completeness.
-/

namespace PCP.Algebraic.FiniteSeedPadding

open Finset

variable {A B : Type*}

/-- Extend a test to a larger seed space, accepting seeds outside the embedding. -/
noncomputable def test (e : A ↪ B) (T : A → Bool) (b : B) : Bool := by
  classical
  exact if h : ∃ a, e a = b then T h.choose else true

@[simp] theorem test_embed (e : A ↪ B) (T : A → Bool) (a : A) :
    test e T (e a) = T a := by
  classical
  have h : ∃ a', e a' = e a := ⟨a, rfl⟩
  simp only [test, dite_eq_left h]
  exact congrArg T (e.injective h.choose_spec)

theorem test_of_not_range (e : A ↪ B) (T : A → Bool) (b : B)
    (h : b ∉ Set.range e) : test e T b = true := by
  classical
  exact dite_eq_right h

theorem test_complete (e : A ↪ B) (T : A → Bool) (hT : ∀ a, T a = true) (b : B) :
    test e T b = true := by
  classical
  unfold test
  split <;> simp only [hT]

variable [Fintype A] [Fintype B]

/-- The number of rejections is unchanged, including empty seed spaces. -/
theorem hammingDist_of_embedding (e : A ↪ B) (T : A → Bool) (U : B → Bool)
    (himage : ∀ a, U (e a) = T a) (houtside : ∀ b, b ∉ Set.range e → U b = true) :
    hammingDist U (fun _ => true) = hammingDist T (fun _ => true) := by
  classical
  have he : (univ.filter fun b => U b ≠ true) = (univ.filter fun a => T a ≠ true).map e := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hb
      by_cases h : b ∈ Set.range e
      · obtain ⟨a, rfl⟩ := h
        exact ⟨a, by simpa only [← himage] using hb, rfl⟩
      · exact False.elim (hb (houtside b h))
    · rintro ⟨a, ha, rfl⟩
      simpa only [himage] using ha
  simp only [hammingDist, he, card_map]

variable [Nonempty A]

/-- Exact normalized rejection, with the actual ratio of finite seed cardinalities. -/
theorem rejectionRate_of_embedding (e : A ↪ B) (T : A → Bool) (U : B → Bool)
    (himage : ∀ a, U (e a) = T a) (houtside : ∀ b, b ∉ Set.range e → U b = true) :
    relativeDistance U (fun _ => true) =
      ((Fintype.card A : ℚ) / Fintype.card B) * relativeDistance T (fun _ => true) := by
  classical
  let _ : Nonempty B := ⟨e (Classical.choice inferInstance)⟩
  unfold relativeDistance
  rw [hammingDist_of_embedding e T U himage houtside]
  have ha : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The canonical padding test has exactly the same rejection scaling. -/
theorem rejectionRate_test (e : A ↪ B) (T : A → Bool) :
    relativeDistance (test e T) (fun _ => true) =
      ((Fintype.card A : ℚ) / Fintype.card B) * relativeDistance T (fun _ => true) :=
  rejectionRate_of_embedding e T (test e T) (test_embed e T) (test_of_not_range e T)

end PCP.Algebraic.FiniteSeedPadding
