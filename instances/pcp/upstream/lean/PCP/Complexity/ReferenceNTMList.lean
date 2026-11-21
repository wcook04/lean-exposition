import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Finite storage for the reference Turing-machine tapes

Cells outside a stored list contain the designated blank symbol. Updating a cell
extends storage only as far as that cell, so every bounded trace has finite
executable storage. This module is independent of the reference library.
-/

namespace PCP.ReferenceNTM

variable {α : Type*}

/-- Default-blank reading of a finite cell list. -/
def cell (blank : α) (xs : List α) (i : ℕ) : α := xs[i]?.getD blank

/-- Store a cell, filling any intervening absent cells with blanks. -/
def setCell (blank : α) (xs : List α) : ℕ → α → List α
  | 0, a => a :: xs.tail
  | i + 1, a => xs.headD blank :: setCell blank xs.tail i a

@[simp] theorem cell_nil (blank : α) (i : ℕ) : cell blank [] i = blank := by
  simp [cell]

@[simp] theorem cell_cons_zero (blank a : α) (xs : List α) :
    cell blank (a :: xs) 0 = a := rfl

@[simp] theorem cell_cons_succ (blank a : α) (xs : List α) (i : ℕ) :
    cell blank (a :: xs) (i + 1) = cell blank xs i := rfl

theorem cell_setCell (blank : α) (xs : List α) (i j : ℕ) (a : α) :
    cell blank (setCell blank xs i a) j = if j = i then a else cell blank xs j := by
  induction i generalizing xs j with
  | zero =>
      cases j <;> cases xs <;> simp [setCell]
  | succ i ih =>
      cases j with
      | zero => cases xs <;> simp [setCell]
      | succ j =>
          cases xs with
          | nil => simpa [setCell] using ih [] j
          | cons b bs => simpa [setCell] using ih bs j

theorem length_setCell (blank : α) (xs : List α) (i : ℕ) (a : α) :
    (setCell blank xs i a).length = max xs.length (i + 1) := by
  induction i generalizing xs with
  | zero => cases xs <;> simp [setCell]
  | succ i ih =>
      cases xs <;> simp only [setCell, List.length_cons, List.tail_nil,
        List.tail_cons, List.length_nil, ih] <;> omega

theorem cell_of_length_le (blank : α) (xs : List α) (i : ℕ)
    (h : xs.length ≤ i) : cell blank xs i = blank := by
  simp [cell, List.getElem?_eq_none h]

end PCP.ReferenceNTM
