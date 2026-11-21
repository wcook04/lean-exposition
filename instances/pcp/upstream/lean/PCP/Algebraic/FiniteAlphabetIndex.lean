/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card

/-!
# Initial alphabets under an explicit finite indexing

The first `n` codes of an indexed finite type give an actual finite alphabet,
with a computable equivalence to `Fin n`. The construction uses a finite-map
embedding, without choosing an enumeration or requiring decidable equality on
the alphabet type. No running-time bound is asserted.
-/

namespace PCP.Algebraic.FiniteAlphabetIndex

variable {A : Type*} {q n : ℕ}

/-- Decode the first `n` codes using the given ambient indexing. -/
def prefixEmbedding (e : A ≃ Fin q) (h : n ≤ q) : Fin n ↪ A :=
  (Fin.castLEEmb h).trans e.symm.toEmbedding

@[simp] theorem code_prefixEmbedding (e : A ≃ Fin q) (h : n ≤ q) (i : Fin n) :
    e (prefixEmbedding e h i) = Fin.castLE h i := e.apply_symm_apply _

/-- The alphabet consists exactly of the first `n` ambient codes. -/
def alphabet (e : A ≃ Fin q) (h : n ≤ q) : Finset A :=
  Finset.univ.map (prefixEmbedding e h)

/-- Membership is the explicit integer comparison on the ambient code. -/
@[simp] theorem mem_alphabet (e : A ≃ Fin q) (h : n ≤ q) (x : A) :
    x ∈ alphabet e h ↔ (e x).val < n := by
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
    rw [← hi, code_prefixEmbedding]
    exact i.isLt
  · intro hx
    refine Finset.mem_map.mpr ⟨⟨(e x).val, hx⟩, Finset.mem_univ _, ?_⟩
    apply e.injective
    rw [code_prefixEmbedding]
    rfl

/-- The prefix alphabet has precisely the requested cardinality. -/
@[simp] theorem card_alphabet (e : A ≃ Fin q) (h : n ≤ q) :
    (alphabet e h).card = n := by simp [alphabet]

/-- The explicit index of an alphabet element is its original ambient integer code. -/
def code (e : A ≃ Fin q) (h : n ≤ q) : alphabet e h ≃ Fin n where
  toFun x := ⟨(e x.1).val, (mem_alphabet e h x.1).mp x.2⟩
  invFun i := ⟨prefixEmbedding e h i,
    Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [code_prefixEmbedding]
    rfl
  right_inv i := by
    apply Fin.ext
    exact congrArg (fun j : Fin q => j.val) (code_prefixEmbedding e h i)

@[simp] theorem code_apply_val (e : A ≃ Fin q) (h : n ≤ q) (x : alphabet e h) :
    (code e h x).val = (e x.1).val := rfl

@[simp] theorem code_symm_coe (e : A ≃ Fin q) (h : n ≤ q) (i : Fin n) :
    ((code e h).symm i).val = e.symm (Fin.castLE h i) := rfl

/-- A positive prefix length gives a nonempty actual alphabet. -/
theorem alphabet_nonempty (e : A ≃ Fin q) (h : n ≤ q) (hn : 0 < n) :
    (alphabet e h).Nonempty := by
  rw [← Finset.card_pos, card_alphabet]
  exact hn

end PCP.Algebraic.FiniteAlphabetIndex
