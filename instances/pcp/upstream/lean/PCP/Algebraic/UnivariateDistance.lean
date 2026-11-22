/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Distance
import Mathlib.Algebra.Polynomial.Roots

/-!
# Univariate polynomial disagreement on a uniformly sampled field element

The root bound in rational normalization, used by the point-line decoder and
the bivariate agreement argument. The estimates remain true, but may be
uninformative, above the field size.
-/

namespace PCP.Algebraic.UnivariateDistance

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A nonzero polynomial has at most its degree many zeros in the field. -/
theorem card_eval_zero_le (p : Polynomial F) (hp : p ≠ 0) :
    #{x : F | p.eval x = 0} ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hx).2

/-- The zero fraction is bounded by the degree divided by the field size. -/
theorem eval_zero_agreement_le (p : Polynomial F) (hp : p ≠ 0) :
    relativeAgreement p.eval 0 ≤ (p.natDegree : ℚ) / Fintype.card F := by
  unfold relativeAgreement
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_eval_zero_le p hp

/-- Sampling one parameter detects a nonzero degree-`d` residual with probability
at least `1 - d / |F|`. -/
theorem eval_distance_zero_ge (p : Polynomial F) {d : ℕ}
    (hp : p.natDegree ≤ d) (hne : p ≠ 0) :
    1 - (d : ℚ) / Fintype.card F ≤ relativeDistance p.eval 0 := by
  have h := eval_zero_agreement_le p hne
  have hd : (p.natDegree : ℚ) / Fintype.card F ≤ (d : ℚ) / Fintype.card F := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hp
  rw [relativeAgreement_eq_one_sub_relativeDistance] at h
  linarith

end PCP.Algebraic.UnivariateDistance
