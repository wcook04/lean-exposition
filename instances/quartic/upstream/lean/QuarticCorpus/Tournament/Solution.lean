module

public import QuarticQuery.Statement
import QuarticQuery.Tournament.Drift

/-!
# Drift bundle

Identity (13) and the bound `E[W_new] ≤ W/2` from Proposition 3.2. Wrappers carry
distinct names, so that importing the proof module cannot collide with them.
-/

public section

namespace QuarticQuery.Checked

-- CHALLENGE-BEGIN
theorem expected_weight_eq {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p = (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) := by
  -- proof
  exact Tournament.expected_weight_eq w ha hW hpos

theorem expected_weight_le_half {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p ≤ W / 2 := by
  -- proof
  exact Tournament.expected_weight_le_half w ha hW hpos
-- CHALLENGE-END

end QuarticQuery.Checked
