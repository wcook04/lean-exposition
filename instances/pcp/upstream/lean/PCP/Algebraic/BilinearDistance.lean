/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard

/-!
# Separation of binary bilinear maps

A bilinear separation argument that replaces the Theorem 2.5 step of Appendix B
of Amireddy–Behera–Srinivasan–Sudan–Willumsgaard. A nonzero binary bilinear map is
nonzero on at least one quarter of its input pairs: a nonzero column is supported
on half the rows, and each of those rows is supported on half its domain.

The main statement uses additive homomorphisms, so it also applies without
explicit vector-space coordinates. All bounds are normalized rational Hamming
distances.
-/

namespace PCP.Algebraic.BilinearDistance

open Finset

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Fintype U] [Fintype V]

/-- A binary bilinear map with a nonzero value is nonzero on at least one quarter
of all pairs. -/
theorem relativeDistance_bilinear_zero_le (B : U →+ V →+ ZMod 2)
    (u : U) (v : V) (h : B u v ≠ 0) :
    (1 : ℚ) / 4 ≤ relativeDistance (fun p : U × V => B p.1 p.2) 0 := by
  classical
  let L : U →+ ZMod 2 :=
    { toFun := fun x => B x v
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have hc : (2 : ℚ) * #{x | B x v ≠ 0} = Fintype.card U := by
    exact_mod_cast Hadamard.two_mul_nonzero_count L u h
  have hs : (∑ x, if B x v ≠ 0 then (1 : ℚ) / 2 else 0) ≤
      ∑ x, relativeDistance (B x) 0 := by
    apply sum_le_sum
    intro x _
    split_ifs with hx
    · exact le_of_eq (Hadamard.relativeDistance_addHom_zero (B x) v hx).symm
    · exact relativeDistance_nonneg _ _
  have hsum : (∑ x, if B x v ≠ 0 then (1 : ℚ) / 2 else 0) =
      (#{x | B x v ≠ 0} : ℚ) / 2 := by
    simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one_div]
  rw [hsum] at hs
  rw [relativeDistance_prod]
  change (1 : ℚ) / 4 ≤ (∑ x, relativeDistance (B x) 0) / Fintype.card U
  have hp : (0 : ℚ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hp).mpr
  linarith

/-- Two distinct binary bilinear maps differ on at least one quarter of pairs. -/
theorem relativeDistance_bilinear_le (B C : U →+ V →+ ZMod 2)
    (u : U) (v : V) (h : B u v ≠ C u v) :
    (1 : ℚ) / 4 ≤ relativeDistance (fun p : U × V => B p.1 p.2)
      (fun p => C p.1 p.2) := by
  have he : (B - C) u v ≠ 0 := by simpa using sub_ne_zero.mpr h
  have hd := relativeDistance_bilinear_zero_le (B - C) u v he
  simpa only [relativeDistance, hammingDist, Pi.zero_apply, AddMonoidHom.sub_apply,
    sub_ne_zero] using hd

/-- A binary bilinear map is zero if its nonzero fraction is less than one quarter. -/
theorem eq_zero_of_relativeDistance_lt (B : U →+ V →+ ZMod 2)
    (h : relativeDistance (fun p : U × V => B p.1 p.2) 0 < (1 : ℚ) / 4) : B = 0 := by
  ext u v
  by_contra hne
  exact (not_le_of_gt h) (relativeDistance_bilinear_zero_le B u v hne)

section Linear

variable [Module (ZMod 2) U] [Module (ZMod 2) V]

/-- The vector-space formulation of binary bilinear separation. -/
theorem relativeDistance_bilinear_zero_le_linear
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (u : U) (v : V) (h : B u v ≠ 0) :
    (1 : ℚ) / 4 ≤ relativeDistance (fun p : U × V => B p.1 p.2) 0 := by
  let B' : U →+ V →+ ZMod 2 :=
    { toFun := fun x => (B x).toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := by intro x x'; ext y; simp }
  exact relativeDistance_bilinear_zero_le B' u v h

/-- A bilinear form whose nonzero fraction is below one quarter vanishes everywhere. -/
theorem eq_zero_of_relativeDistance_lt_linear
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (h : relativeDistance (fun p : U × V => B p.1 p.2) 0 < (1 : ℚ) / 4) : B = 0 := by
  ext u v
  by_contra hne
  exact (not_le_of_gt h) (relativeDistance_bilinear_zero_le_linear B u v hne)

end Linear

end PCP.Algebraic.BilinearDistance
