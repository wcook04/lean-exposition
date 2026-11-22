module

public import QuarticQuery.Statement
import QuarticQuery.Tournament.Drift

public section

namespace QuarticQuery.Checked

/-! Must be rejected: the proof uses `sorry`. -/

theorem expected_weight_eq {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p = (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) :=
  Tournament.expected_weight_eq w ha hW hpos

theorem expected_weight_le_half {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p ≤ W / 2 :=
  sorry

end QuarticQuery.Checked
