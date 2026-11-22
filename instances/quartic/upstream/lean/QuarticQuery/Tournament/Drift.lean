module

public import QuarticQuery.Statement

/-!
# Weight drift in the probabilistic tournament

This is the classical identity (13) in Proposition 3.2 of the nearly quartic
separation preprint. A pivot `p` is chosen with probability `w p / W`, and each
weight `w i` is replaced by `w i * a i p`. Complementarity of the comparison
probabilities makes the expected new total at most half of the old one.

This file formalises the finite calculation only. It does not model the quantum
sampling procedure.
-/

@[expose] public section

open Finset

namespace QuarticQuery.Tournament

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The doubled sum pairs each ordered comparison with its reverse. -/
theorem two_mul_weighted_sum (w : ι → ℝ) {a : ι → ι → ℝ} (ha : IsComparison a) :
    2 * ∑ p, ∑ i, w p * w i * a i p = (∑ i, w i) ^ 2 - ∑ i, w i ^ 2 := by
  have hswap : ∑ p, ∑ i, w p * w i * a i p = ∑ p, ∑ i, w p * w i * a p i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by ring
  have hpair : ∀ p i, w p * w i * a i p + w p * w i * a p i
      = w p * w i - if i = p then w p * w i else 0 := by
    intro p i
    by_cases h : i = p
    · subst h
      simp [ha.self_zero]
    · have := ha.complementary i p h
      simp only [h, ↓reduceIte]
      rw [← mul_add, this]
      ring
  calc
    2 * ∑ p, ∑ i, w p * w i * a i p
        = ∑ p, ∑ i, (w p * w i * a i p + w p * w i * a p i) := by
          rw [two_mul]
          nth_rewrite 2 [hswap]
          simp only [Finset.sum_add_distrib]
    _ = ∑ p, ∑ i, (w p * w i - if i = p then w p * w i else 0) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => hpair p i
    _ = (∑ i, w i) ^ 2 - ∑ i, w i ^ 2 := by
          simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          rw [sq, Finset.sum_mul_sum]
          simp [sq]

/-- Identity (13): the expected new total weight, for positive total weight. -/
theorem expected_weight_eq (w : ι → ℝ) {a : ι → ι → ℝ} (ha : IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p = (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) := by
  have h := two_mul_weighted_sum w ha
  rw [← hW] at h
  have hrw : ∑ p, (w p / W) * ∑ i, w i * a i p
      = (∑ p, ∑ i, w p * w i * a i p) / W := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_mul_eq_mul_div, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, ← h]
  field_simp

/-- The expected new total weight is at most half of the old total. -/
theorem expected_weight_le_half (w : ι → ℝ) {a : ι → ι → ℝ} (ha : IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    ∑ p, (w p / W) * ∑ i, w i * a i p ≤ W / 2 := by
  rw [expected_weight_eq w ha hW hpos]
  have hsq : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

end QuarticQuery.Tournament
