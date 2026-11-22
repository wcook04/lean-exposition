import PCP.Complexity.Machine
import Mathlib.Logic.Equiv.Set

/-!
# Static work tapes and the untouched complement

An injective assignment of finitely many work slots into a fixed tape layout
extends to a bijection by adding exactly the unused tapes as a caller frame.
The forward map is an ordinary definition: work slots use their fixed assigned
index and frame slots use their underlying index. The inverse is used only in
layout proofs, not to inspect input-dependent data during execution.
-/

namespace PCP.Machine.StaticTapeLayout

variable {W K : Type} (work : W → K)

/-- Tapes outside the statically assigned working set. -/
def Unused := {k : K // ∀ w, work w ≠ k}

instance [Fintype W] [DecidableEq K] [Fintype K] : Fintype (Unused work) := inferInstanceAs
  (Fintype {k : K // ∀ w, work w ≠ k})

instance [DecidableEq K] : DecidableEq (Unused work) := inferInstanceAs
  (DecidableEq {k : K // ∀ w, work w ≠ k})

/-- Executable forward relocation of work slots and untouched caller slots. -/
def position : W ⊕ Unused work → K
  | .inl w => work w
  | .inr k => k.val

@[simp] theorem position_work (w : W) : position work (.inl w) = work w := rfl

@[simp] theorem position_unused (k : Unused work) : position work (.inr k) = k.val := rfl

/-- The caller complement makes every global tape represented exactly once. -/
theorem position_bijective (hinj : Function.Injective work) :
    Function.Bijective (position work) := by
  classical
  constructor
  · intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (hinj h)
        | inr y => exact False.elim (y.property x h)
    | inr x =>
        cases y with
        | inl y => exact False.elim (x.property y h.symm)
        | inr y => exact congrArg Sum.inr (Subtype.ext h)
  · intro k
    by_cases h : ∃ w, work w = k
    · obtain ⟨w, hw⟩ := h
      exact ⟨.inl w, hw⟩
    · exact ⟨.inr ⟨k, by simpa using h⟩, rfl⟩

/-- Static equivalence for trace transport; its forward map is `position`. -/
noncomputable def equiv (hinj : Function.Injective work) : W ⊕ Unused work ≃ K :=
  Equiv.ofBijective (position work) (position_bijective work hinj)

@[simp] theorem equiv_apply (hinj : Function.Injective work) (i : W ⊕ Unused work) :
    equiv work hinj i = position work i := rfl

end PCP.Machine.StaticTapeLayout
