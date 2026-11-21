import Breakdown.CellReduction.InstFieldPotentialStreamKey
import Breakdown.CellReduction.InstFieldDecayOrder

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape


open Internal.FieldPot in
theorem fieldPotential_holds_of (hdec : FieldDecayOrderHolds) : FieldPotentialHolds := by
  intro P D hP hD hi
  have hk : ∀ k ∈ D.keys.image (fun κ => κ.label.1.natAbs), ∃ (A : ℝ → Space → Space) (C : ℝ),
      PotentialPack (shapeInfoField P (keysAt D k)) A C := by
    intro k _
    have hv := keysAt_valid hD k
    have hi' : ∀ κ ∈ (keysAt D k).keys, 3 ≤ ((keysAt D k).amp κ).highOrder := fun κ hκ => hi κ (mem_keysAt.1 hκ).1
    have hlab : ∀ κ ∈ (keysAt D k).keys, κ.label.1.natAbs = k := fun κ hκ => (mem_keysAt.1 hκ).2
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exact typeTwo_group hP hv (fun κ hκ => Int.natAbs_eq_zero.1 (hlab κ hκ)) hi'
    · obtain ⟨C, hC⟩ := typeOne_pack hdec hP hv hlab hpos hi'
      exact ⟨_, C, hC⟩
  choose! A C hAC using hk
  have hs := pack_sum (D.keys.image (fun κ => κ.label.1.natAbs)) _ A C hAC
  refine ⟨_, _, hs.smooth, hs.periodic, ?_, hs.bound⟩
  intro σ y
  rw [hs.curl σ y, shapeField_fiber P D σ y]

theorem fieldPotential_holds : FieldPotentialHolds :=
  fieldPotential_holds_of fieldDecayOrder_holds

end Instantiation

end CellReduction

end Breakdown
