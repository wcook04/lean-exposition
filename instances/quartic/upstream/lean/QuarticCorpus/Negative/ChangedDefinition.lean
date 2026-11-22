module

public import Mathlib

/-!
Must be rejected: `IsComparison` is redefined with an impossible field, which
makes both theorems vacuous while leaving their displayed text unchanged. This is
the attack a statement-only check would miss.
-/

public section

namespace QuarticQuery.Tournament

structure IsComparison {ι : Type} (a : ι → ι → ℝ) : Prop where
  complementary : ∀ i j, i ≠ j → a i j + a j i = 1
  self_zero : ∀ i, a i i = 0
  impossible : False

end QuarticQuery.Tournament

namespace QuarticQuery.Checked

theorem expected_weight_eq {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p = (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) :=
  ha.impossible.elim

theorem expected_weight_le_half {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    {a : ι → ι → ℝ} (ha : Tournament.IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p ≤ W / 2 :=
  ha.impossible.elim

end QuarticQuery.Checked
