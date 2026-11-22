/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardAffineQueries

/-!
# Restricting received-word distance to homogeneous labels

Degree-one Hadamard queries include affine forms. Homogeneous forms constitute
half of that query space, so restriction can at most double the error fraction.
This applies to arbitrary received words, without any linearity assumption.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {I : Type*} [Fintype I] {t : ℕ}

/-- Restricting every received row to homogeneous labels costs at most a factor two. -/
theorem relativeDistance_homogeneous_le_twice_full
    (H G : I → Coefficients t 1 → ZMod 2) :
    relativeDistance
      (fun p : I × (Fin t → ZMod 2) => H p.1 (homogeneousIndex (le_refl 1) p.2))
      (fun p => G p.1 (homogeneousIndex (le_refl 1) p.2)) ≤
      2 * relativeDistance (fun p : I × Coefficients t 1 => H p.1 p.2)
        (fun p => G p.1 p.2) := by
  classical
  rw [relativeDistance_prod, relativeDistance_prod, ← mul_div_assoc, mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro i _
  simpa only [Function.comp_def, embed_refl] using
    homogeneousDistance_le_twice_affine (le_refl 1) (H i) (G i)

end PCP.Algebraic.Hadamard
