/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.Encoding
import PCP.Complexity.OptionalBitPrefix

/-!
# Local constraints for a bounded existential witness on the input stack

The public input and separator are fixed. The following positions contain bits
or blanks, with adjacent checks forcing blanks to be a suffix. These unary and
binary constraints characterize exactly the encoded pairs with a bounded witness.
-/

namespace PCP.Machine.WitnessInputCells

/-- Interpret a possible witness bit, rejecting separators through the separate local predicate. -/
def bitValue : Option Sym → Option Bool
  | some (.bit b) => some b
  | _ => none

/-- Optional bits are exactly the fixed points of bit decoding followed by embedding. -/
def IsBit (v : Option Sym) : Prop := v = (bitValue v).map Sym.bit

instance isBitDecidable (v : Option Sym) : Decidable (IsBit v) :=
  inferInstanceAs (Decidable (_ = _))

theorem isBit_none_iff {v : Option Sym} (h : IsBit v) : bitValue v = none ↔ v = none := by
  rw [h]
  cases bitValue v <;> simp [bitValue]

/-- One unary cell check, using its public arithmetic position. -/
def Cell (x : List Bool) (W j : ℕ) (v : Option Sym) : Prop :=
  if hj : j < x.length then v = some (.bit x[j]) else
  if j = x.length then v = some .sep else
  if j < x.length + 1 + W then IsBit v else v = none

instance cellDecidable (x : List Bool) (W j : ℕ) (v : Option Sym) :
    Decidable (Cell x W j v) := by
  unfold Cell
  split <;> infer_instance

/-- Outside a finite vector, its cell is the fixed blank value. -/
def read {B : ℕ} (s : Fin B → Option Sym) (j : ℕ) : Option Sym :=
  if h : j < B then s ⟨j, h⟩ else none

@[simp] theorem read_fin {B : ℕ} (s : Fin B → Option Sym) (j : Fin B) :
    read s j.val = s j := by simp [read]

/-- Each cell is valid, and a blank witness position forces the next position to be blank. -/
def Holds {B : ℕ} (x : List Bool) (W : ℕ) (s : Fin B → Option Sym) : Prop :=
  (∀ j : Fin B, Cell x W j.val (s j)) ∧
    ∀ j : Fin W, read s (x.length + 1 + j.val) = none →
      read s (x.length + 1 + (j.val + 1)) = none

theorem cell_all {B : ℕ} {x : List Bool} {W : ℕ} {s : Fin B → Option Sym}
    (h : Holds x W s) (hb : x.length + 1 + W ≤ B) (j : ℕ) :
    Cell x W j (read s j) := by
  by_cases hj : j < B
  · simpa [read, hj] using h.1 ⟨j, hj⟩
  · have hxl : ¬j < x.length := by omega
    have hxe : j ≠ x.length := by omega
    have hxw : ¬j < x.length + 1 + W := by omega
    simp [Cell, read, hj, hxl, hxe, hxw]

theorem witness_isBit {B : ℕ} {x : List Bool} {W : ℕ} {s : Fin B → Option Sym}
    (h : Holds x W s) (hb : x.length + 1 + W ≤ B) (j : Fin W) :
    IsBit (read s (x.length + 1 + j.val)) := by
  have hc := cell_all h hb (x.length + 1 + j.val)
  simpa only [Cell, dite_eq_right (show ¬x.length + 1 + j.val < x.length by omega),
    ite_eq_right (show x.length + 1 + j.val ≠ x.length by omega),
    ite_eq_left (show x.length + 1 + j.val < x.length + 1 + W by have := j.isLt; omega)] using hc

def witnessCells {B : ℕ} (x : List Bool) (W : ℕ) (s : Fin B → Option Sym) :
    Fin W → Option Bool := fun j => bitValue (read s (x.length + 1 + j.val))

theorem witness_noHoles {B : ℕ} {x : List Bool} {W : ℕ} {s : Fin B → Option Sym}
    (h : Holds x W s) (hb : x.length + 1 + W ≤ B) :
    OptionalBitPrefix.NoHoles (witnessCells x W s) := by
  intro j hj hz
  have h₀ := witness_isBit h hb (⟨j, by omega⟩ : Fin W)
  have h₁ := witness_isBit h hb (⟨j + 1, hj⟩ : Fin W)
  apply (isBit_none_iff h₁).mpr
  exact h.2 ⟨j, by omega⟩ ((isBit_none_iff h₀).mp hz)


/-- The separator position and witness offsets in the repository's actual pair encoding. -/
theorem get_encodePair (x w : List Bool) (j : ℕ) :
    (encodePair (x, w))[j]? = if hj : j < x.length then some (.bit x[j]) else
      if j = x.length then some .sep else (w[j - (x.length + 1)]?).map Sym.bit := by
  simp only [encodePair, List.getElem?_append, length_ofBits]
  by_cases hj : j < x.length
  · simp [hj, ofBits]
  · rw [ite_eq_right hj, dite_eq_right hj]
    by_cases he : j = x.length
    · simp [he]
    · rw [ite_eq_right he]
      have hj' : j - x.length = (j - (x.length + 1)) + 1 := by omega
      rw [hj']
      simp [ofBits]

@[simp] theorem get_encodePair_witness (x w : List Bool) (j : ℕ) :
    (encodePair (x, w))[x.length + 1 + j]? = (w[j]?).map Sym.bit := by
  rw [get_encodePair]
  simp [show ¬x.length + 1 + j < x.length by omega,
    show x.length + 1 + j ≠ x.length by omega]

/-- Unary and adjacent checks recover a single bounded witness, shared by the whole tableau. -/
theorem exists_encoded {B : ℕ} {x : List Bool} {W : ℕ} {s : Fin B → Option Sym}
    (h : Holds x W s) (hb : x.length + 1 + W ≤ B) :
    ∃ w : List Bool, w.length ≤ W ∧ ∀ j, read s j = (encodePair (x, w))[j]? := by
  obtain ⟨w, hw, hget⟩ := (OptionalBitPrefix.exists_list_iff _).mp (witness_noHoles h hb)
  refine ⟨w, hw, fun j => ?_⟩
  have hc := cell_all h hb j
  rw [get_encodePair]
  by_cases hj : j < x.length
  · simpa only [Cell, dite_eq_left hj] using hc
  · rw [dite_eq_right hj]
    by_cases he : j = x.length
    · simpa only [Cell, dite_eq_right hj, ite_eq_left he] using hc
    · rw [ite_eq_right he]
      by_cases hjw : j < x.length + 1 + W
      · have hn : j - (x.length + 1) < W := by omega
        have heq : x.length + 1 + (j - (x.length + 1)) = j := by omega
        have hg := hget ⟨j - (x.length + 1), hn⟩
        change w[j - (x.length + 1)]? =
          bitValue (read s (x.length + 1 + (j - (x.length + 1)))) at hg
        rw [heq] at hg
        rw [hg]
        exact (by simpa only [Cell, dite_eq_right hj, ite_eq_right he, ite_eq_left hjw] using hc :
          IsBit (read s j))
      · rw [List.getElem?_eq_none (by omega)]
        simpa only [Cell, dite_eq_right hj, ite_eq_right he, ite_eq_right hjw, Option.map_none] using hc

@[simp] theorem isBit_map (u : Option Bool) : IsBit (u.map Sym.bit) := by
  cases u <;> rfl

/-- Every bounded witness supplies the local cell and adjacent-blank checks. -/
theorem holds_of_encoded {B : ℕ} {x w : List Bool} {W : ℕ} {s : Fin B → Option Sym}
    (hw : w.length ≤ W) (hget : ∀ j, read s j = (encodePair (x, w))[j]?) : Holds x W s := by
  constructor
  · intro j
    have hg := hget j.val
    rw [read_fin] at hg
    rw [hg]
    unfold Cell
    split
    · next hj => simp only [get_encodePair, dite_eq_left hj]
    · next hj =>
      rw [get_encodePair, dite_eq_right hj]
      split
      · next he => rfl
      · next he =>
        split
        · exact isBit_map _
        · next hjw => simp [List.getElem?_eq_none (by omega : w.length ≤ j.val - (x.length + 1))]
  · intro j hz
    rw [hget, get_encodePair_witness] at hz ⊢
    have hn : w[j.val]? = none := by
      cases hv : w[j.val]? with
      | none => rfl
      | some b => simp [hv] at hz
    have hl := List.getElem?_eq_none_iff.mp hn
    rw [List.getElem?_eq_none (by omega : w.length ≤ j.val + 1)]
    rfl

/-- Exact input-boundary characterization, with no quantified whole witness in the checks. -/
theorem holds_iff {B : ℕ} (x : List Bool) (W : ℕ) (s : Fin B → Option Sym)
    (hb : x.length + 1 + W ≤ B) :
    Holds x W s ↔ ∃ w : List Bool, w.length ≤ W ∧
      ∀ j, read s j = (encodePair (x, w))[j]? := by
  constructor
  · exact fun h => exists_encoded h hb
  · rintro ⟨w, hw, hget⟩
    exact holds_of_encoded hw hget

end PCP.Machine.WitnessInputCells
