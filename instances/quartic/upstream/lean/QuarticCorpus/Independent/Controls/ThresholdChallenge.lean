module

public import Mathlib

/-! Hand-authored challenge for one changed-definition Comparator control.
The challenge intentionally has an admitted proof; its statement is the input
to comparison, and is not a proof certificate. -/

@[expose] public section
set_option autoImplicit false

namespace Round3.ThresholdSpec

def Eligible (p : ℝ) : Prop := (2 / 3 : ℝ) ≤ p

theorem threshold_lower_bound (p : ℝ) (hp : Eligible p) : (2 / 3 : ℝ) ≤ p := by
  sorry

end Round3.ThresholdSpec
