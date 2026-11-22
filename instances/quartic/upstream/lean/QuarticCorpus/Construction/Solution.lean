module

public import QuarticQuery.Statement
import QuarticQuery.Construction.LocalTests

/-!
# Construction bundle

Section 2.2: there is at most one winner, a circuit transcript is unique, and the
outward pointers behave as the comparison argument needs.
-/

public section

namespace QuarticQuery.Checked

-- CHALLENGE-BEGIN
theorem winsAt_unique {κ : Type} {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}
    {x : BitInput (BitLoc ℓ r C.size κ)} {i i' : Column ℓ} {s s' : Address r}
    (h : WinsAt f C ℓ r x i s) (h' : WinsAt f C ℓ r x i' s') : i = i' ∧ s = s' := by
  -- proof
  exact QuarticQuery.winsAt_unique h h'

theorem existsUnique_gateConsistent {ι : Type} (C : Circuit ι) (x : BitInput ι) :
    ∃! tr, GateConsistent C x tr := by
  -- proof
  exact QuarticQuery.existsUnique_gateConsistent C x

theorem winner_no_incoming_zero {κ : Type} {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}
    {x : BitInput (BitLoc ℓ r C.size κ)} {i : Column ℓ} {s : Address r}
    (h : WinsAt f C ℓ r x i s) (c : Column ℓ) (a : Address r) (hne : i ≠ c) :
    readX x i (pointerEquiv ℓ (readPointerBit x c a ⟨i, hne⟩)) = true := by
  -- proof
  exact QuarticQuery.winner_no_incoming_zero h c a hne

theorem winner_finds_zero {κ : Type} {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}
    {x : BitInput (BitLoc ℓ r C.size κ)} {i : Column ℓ} {s : Address r}
    (h : WinsAt f C ℓ r x i s) (j : Column ℓ) (hne : j ≠ i) :
    readX x j (pointerEquiv ℓ (readPointerBit x i s ⟨j, hne⟩)) = false := by
  -- proof
  exact QuarticQuery.winner_finds_zero h j hne
-- CHALLENGE-END

end QuarticQuery.Checked
