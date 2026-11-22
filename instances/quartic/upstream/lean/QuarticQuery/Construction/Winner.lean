module

public import QuarticQuery.Statement

/-!
# Winners of the addressed function

The pointer bijection, uniqueness of the winner and its address (Section 2.2),
and the Boolean comparison facts of Section 3.3. Everything is stated for the
generic `addressedF f C ℓ r` and needs no property of the circuit.
-/

public section

namespace QuarticQuery

theorem mValue_eq (t : ℕ) : mValue t = 2 ^ (2 * t) := rfl

theorem mValue_eq_four_pow (t : ℕ) : mValue t = 4 ^ t := by
  simp [mValue, pow_mul]

theorem card_column (ℓ : ℕ) : Fintype.card (Column ℓ) = 2 ^ ℓ :=
  Fintype.card_fin _

/-- Ledger: def-column-layout. -/
theorem pointerEquiv_bijective (ℓ : ℕ) : Function.Bijective (pointerEquiv ℓ) :=
  (pointerEquiv ℓ).bijective

/-- Ledger: def-column-layout. Every column has exactly one `ℓ`-bit name, so no
pointer pattern is invalid. -/
theorem existsUnique_pointer (ℓ : ℕ) (j : Column ℓ) :
    ∃! w : Fin ℓ → Bool, pointerEquiv ℓ w = j :=
  (pointerEquiv_bijective ℓ).existsUnique j

section Winners

variable {κ : Type} {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}
  {x : BitInput (BitLoc ℓ r C.size κ)} {i i' : Column ℓ} {s s' : Address r}

/-- Ledger: def-F. A winner's pointer (8) puts a zero in any other winner's
all-one string. -/
theorem winsAt_column_unique (h : WinsAt f C ℓ r x i s) (h' : WinsAt f C ℓ r x i' s') :
    i = i' := by
  by_contra hne
  have hzero := h.2.2.2 ⟨i', fun e => hne e.symm⟩
  have hone := h'.1 (pointerEquiv ℓ (readPointerBit x i s ⟨i', fun e => hne e.symm⟩))
  exact Bool.noConfusion (hone.symm.trans hzero)

/-- Ledger: eq-7. The address of a column is forced by `f`. -/
theorem winsAt_address_unique (h : WinsAt f C ℓ r x i s) (h' : WinsAt f C ℓ r x i s') :
    s = s' :=
  funext fun a => Option.some.inj ((h.2.1 a).symm.trans (h'.2.1 a))

/-- Ledger: def-F. There is at most one winning pair. -/
theorem winsAt_unique (h : WinsAt f C ℓ r x i s) (h' : WinsAt f C ℓ r x i' s') :
    i = i' ∧ s = s' := by
  obtain rfl := winsAt_column_unique h h'
  exact ⟨rfl, winsAt_address_unique h h'⟩

/-- Ledger: claim-winner-dominates. Boolean half: a winner's string is all ones,
so no pointer, from any column at any address, finds a zero in it. -/
theorem winner_no_incoming_zero (h : WinsAt f C ℓ r x i s) (c : Column ℓ) (a : Address r)
    (hne : i ≠ c) :
    readX x i (pointerEquiv ℓ (readPointerBit x c a ⟨i, hne⟩)) = true :=
  h.1 _

/-- Ledger: claim-winner-dominates. Boolean half: the winner's correct cell finds
a zero in every other column. -/
theorem winner_finds_zero (h : WinsAt f C ℓ r x i s) (j : Column ℓ) (hne : j ≠ i) :
    readX x j (pointerEquiv ℓ (readPointerBit x i s ⟨j, hne⟩)) = false :=
  h.2.2.2 ⟨j, hne⟩

end Winners

end QuarticQuery
