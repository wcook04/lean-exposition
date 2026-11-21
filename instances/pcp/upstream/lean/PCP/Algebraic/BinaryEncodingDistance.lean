/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryConstraintRobust

/-!
# Distances between binary field encodings

Homogeneous Hadamard labels halve the distance between field-valued functions.
The restricted binary distance also satisfies the triangle inequality.
-/

namespace PCP.Algebraic.BinaryLagrangeConstraint

open BinaryPolynomialSpace Hadamard

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F]
variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]
variable {c t r : ℕ}

/-- The homogeneous-label distance of two field encodings is exactly half the
distance between the field functions. -/
theorem homogeneousDistance_encode (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (f g : (σ → F) → F) :
    homogeneousDistance hr (fun x => encode r (ρ (f x)))
        (fun x => encode r (ρ (g x))) = (1 : ℚ) / 2 * relativeDistance f g := by
  have h := relativeDistance_homogeneous_queries hr (fun x => ρ (f x)) (fun x => ρ (g x))
  rw [relativeDistance_map ρ ρ.injective] at h
  exact h

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
/-- Restricting to homogeneous labels preserves the triangle inequality. -/
theorem homogeneousDistance_triangle (hr : 1 ≤ r)
    (H G K : (σ → F) → Coefficients t r → ZMod 2) :
    homogeneousDistance hr H K ≤ homogeneousDistance hr H G +
      homogeneousDistance hr G K :=
  relativeDistance_triangle _ _ _

end PCP.Algebraic.BinaryLagrangeConstraint
