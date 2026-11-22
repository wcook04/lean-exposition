module

public import QuarticQuery.Forrelation.Promise

/-!
# The smallest instance

`k = 2`, `m = 4`. The 256 inputs split as 104 one-inputs, 48 zero-inputs and 104
outside the promise, checked in the kernel by `decide +kernel`, which adds no
axiom. `Φ = -1` occurs and lies outside the promise.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset

/-- Ledger: eq-4. The census of `k = 2`, `t = 1`: one-inputs. -/
theorem census_true :
    (univ.filter fun z : BitInput (ForrelationCoord 2 1) => P 2 1 z = some true).card = 104 := by
  decide +kernel

/-- Ledger: eq-4. The census of `k = 2`, `t = 1`: zero-inputs. -/
theorem census_false :
    (univ.filter fun z : BitInput (ForrelationCoord 2 1) => P 2 1 z = some false).card = 48 := by
  decide +kernel

/-- Ledger: eq-4. The census of `k = 2`, `t = 1`: outside the promise. -/
theorem census_none :
    (univ.filter fun z : BitInput (ForrelationCoord 2 1) => P 2 1 z = none).card = 104 := by
  decide +kernel

theorem exists_filter_of_card {α : Type} [Fintype α] {q : α → Prop} [DecidablePred q]
    {c : ℕ} (hc : 0 < c) (h : (univ.filter q).card = c) : ∃ a, q a := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (h ▸ hc)
  exact ⟨a, (Finset.mem_filter.1 ha).2⟩

/-- Ledger: eq-4. The promise is nonempty on both sides, in the real-valued form
of (4), and its complement is nonempty. -/
theorem promise_nonempty_two_one :
    (∃ z : BitInput (ForrelationCoord 2 1), delta 2 ≤ Phi 2 1 z) ∧
    (∃ z : BitInput (ForrelationCoord 2 1), |Phi 2 1 z| ≤ delta 2 / 2) ∧
    (∃ z : BitInput (ForrelationCoord 2 1),
      ¬ delta 2 ≤ Phi 2 1 z ∧ ¬ |Phi 2 1 z| ≤ delta 2 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := exists_filter_of_card (by norm_num) census_true
    exact ⟨z, (P_eq_some_true_iff _ _ _).1 hz⟩
  · obtain ⟨z, hz⟩ := exists_filter_of_card (by norm_num) census_false
    exact ⟨z, (P_eq_some_false_iff _ _ _).1 hz⟩
  · obtain ⟨z, hz⟩ := exists_filter_of_card (by norm_num) census_none
    exact ⟨z, (P_eq_none_iff _ _ _).1 hz⟩

/-- `z₁ = z₂ = (-1, 1, 1, 1)`. -/
def negativeWitness : BitInput (ForrelationCoord 2 1) := fun c => c.2.val == 0

/-- Ledger: eq-4. `Φ = -1` occurs. -/
theorem Phi_negativeWitness : Phi 2 1 negativeWitness = -1 := by
  have hN : forrelationNumerator 2 1 negativeWitness = -8 := by decide +kernel
  have hM : forrelationDenominator 2 1 = 8 := by decide +kernel
  rw [Phi, hN, hM]
  norm_num

/-- Ledger: eq-4. A large negative value is outside the promise. -/
theorem P_negativeWitness : P 2 1 negativeWitness = none := by decide +kernel

end QuarticQuery.Forrelation
