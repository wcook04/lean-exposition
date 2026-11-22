/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Variable-length witnesses in a fixed number of optional cells

The local condition `none → next none` says precisely that the occupied cells
form one initial segment. Decoding that segment gives an actual witness of
length at most the space budget. The result is generic in the cell alphabet.
-/

namespace PCP.Machine.OptionalBitPrefix

variable {α : Type*} {W : ℕ}

/-- A blank cell cannot be followed immediately by an occupied one. -/
def NoHoles (s : Fin W → Option α) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < W), s ⟨i, by omega⟩ = none → s ⟨i + 1, hi⟩ = none

/-- Decode exactly the populated initial segment, stopping at the first blank. -/
def decode : {W : ℕ} → (Fin W → Option α) → List α
  | 0, _ => []
  | _ + 1, s => match s 0 with
    | none => []
    | some a => a :: decode (fun i => s i.succ)

theorem decode_length_le (s : Fin W → Option α) : (decode s).length ≤ W := by
  induction W with
  | zero => simp [decode]
  | succ W ih =>
    cases h : s 0 <;> simp only [decode, h, List.length_nil, List.length_cons]
    · omega
    · exact Nat.succ_le_succ (ih _)

theorem NoHoles.tail {s : Fin (W + 1) → Option α} (h : NoHoles s) :
    NoHoles (fun i => s i.succ) := by
  intro i hi
  exact h (i + 1) (by omega)

theorem NoHoles.none_of_le {s : Fin W → Option α} (h : NoHoles s)
    (i j : Fin W) (hij : i.val ≤ j.val) (hi : s i = none) : s j = none := by
  have aux : ∀ k, ∀ hk : k < W, i.val ≤ k → s ⟨k, hk⟩ = none := by
    intro k
    induction k with
    | zero =>
      intro hk hle
      have he : (⟨0, hk⟩ : Fin W) = i := Fin.ext (show 0 = i.val by omega)
      simpa only [he] using hi
    | succ k ih =>
      intro hk hle
      by_cases he : i.val = k + 1
      · have he' : (⟨k + 1, hk⟩ : Fin W) = i := Fin.ext he.symm
        simpa only [he'] using hi
      · exact h k hk (ih (by omega) (by omega))
  exact aux j.val j.isLt hij

/-- Every padded position of the decoded witness is exactly its original cell. -/
theorem getElem?_decode (s : Fin W → Option α) (h : NoHoles s) (j : Fin W) :
    (decode s)[j.val]? = s j := by
  induction W with
  | zero => exact Fin.elim0 j
  | succ W ih =>
    cases hs : s 0 with
    | none =>
      simp only [decode, hs, List.getElem?_nil]
      exact (h.none_of_le 0 j (Nat.zero_le _) hs).symm
    | some a =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [decode, hs]
      · simpa only [decode, hs, Fin.val_succ, List.getElem?_cons_succ] using
          ih (fun i => s i.succ) h.tail k

/-- Pad an ordinary witness by blanks to the prescribed width. -/
def encode (w : List α) (_hw : w.length ≤ W) : Fin W → Option α := fun j => w[j.val]?

theorem encode_noHoles (w : List α) (hw : w.length ≤ W) : NoHoles (encode w hw) := by
  intro i hi h
  have hlen : w.length ≤ i := List.getElem?_eq_none_iff.mp h
  change w[i + 1]? = none
  exact List.getElem?_eq_none (by omega)

/-- Local no-hole constraints are equivalent to one actual bounded-length witness. -/
theorem exists_list_iff (s : Fin W → Option α) :
    NoHoles s ↔ ∃ w : List α, w.length ≤ W ∧ ∀ j : Fin W, w[j.val]? = s j := by
  constructor
  · intro h
    exact ⟨decode s, decode_length_le s, getElem?_decode s h⟩
  · rintro ⟨w, hw, he⟩
    have hs : encode w hw = s := funext he
    exact hs ▸ encode_noHoles w hw

theorem decode_encode (w : List α) (hw : w.length ≤ W) : decode (encode w hw) = w := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < W
  · exact getElem?_decode _ (encode_noHoles w hw) ⟨i, hi⟩
  · rw [List.getElem?_eq_none ((decode_length_le _).trans (by omega)),
      List.getElem?_eq_none (by omega)]

end PCP.Machine.OptionalBitPrefix
