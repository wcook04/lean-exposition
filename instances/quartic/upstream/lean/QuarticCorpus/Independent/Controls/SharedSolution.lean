module

public import Mathlib

/-! This deliberately shares the impossible premise in SharedChallenge.
Expected Comparator acceptance is a blind-spot result, not semantic success. -/

@[expose] public section
set_option autoImplicit false

namespace Round3.SharedBadSpec

structure IsComparison (a : Fin 2 → Fin 2 → ℝ) : Prop where
  complementary : ∀ i j, i ≠ j → a i j + a j i = 1
  self_zero : ∀ i, a i i = 0
  impossible : False

theorem vacuous_claim (a : Fin 2 → Fin 2 → ℝ) (ha : IsComparison a) : (1 : ℝ) = 0 :=
  ha.impossible.elim

end Round3.SharedBadSpec
