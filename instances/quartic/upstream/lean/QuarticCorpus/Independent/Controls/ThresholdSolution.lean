module

public import Mathlib

/-! Deliberate mutant: the displayed theorem is unchanged but its premise has
been strengthened from >= 2/3 to > 2/3. Expected Comparator rejection; native outcomes: `research/adjudication/round3_formal.json`. -/

@[expose] public section
set_option autoImplicit false

namespace Round3.ThresholdSpec

def Eligible (p : ℝ) : Prop := (2 / 3 : ℝ) < p

theorem threshold_lower_bound (p : ℝ) (hp : Eligible p) : (2 / 3 : ℝ) ≤ p :=
  le_of_lt hp

end Round3.ThresholdSpec
