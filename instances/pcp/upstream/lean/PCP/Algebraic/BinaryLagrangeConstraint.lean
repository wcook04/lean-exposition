/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardWeights
import PCP.Algebraic.LagrangeConstraint

/-!
# The interpolation check over binary Hadamard oracles

The field-valued interpolation equation is observed through a uniformly
sampled homogeneous binary linear functional. Each interpolation coefficient is
absorbed into its query label; zero-weight terms do not read the oracle. The
actual query list has at most `c+2` locations, and the check depends only on them.

For the encoding of any field-valued function, binary rejection is exactly half
the field check's rejection. Honest degree-at-most-`c` polynomials have zero
rejection. This file does not assert soundness for corrupted Hadamard oracles,
or certify running time or an implementation of the random-bit sampling.
-/

namespace PCP.Algebraic.BinaryLagrangeConstraint

open Finset PolynomialLine BinaryPolynomialSpace Hadamard HadamardWeights

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {c t r : ℕ}

/-- The actual binary interpolation check, with zero-weight oracle terms omitted. -/
noncomputable def check (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) : ZMod 2 :=
  H (point u v z) (homogeneousIndex hr w) -
    ∑ i, weightedRead hr ρ (H (point u v (a i))) (LagrangeConstraint.weight a z i) w

/-- Honest Hadamard answers observe exactly the field-valued residual. -/
theorem check_encode (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    check hr ρ a (fun x => encode r (ρ (f x))) u v z w =
      linearEncode (ρ (LagrangeConstraint.check a f u v z)) w := by
  simp only [check, weightedRead_encode, encode_homogeneousIndex,
    LagrangeConstraint.check_eq_sub_sum, linearEncode_comm, map_sub, map_sum]

/-- Perfect completeness at every choice of line, independent parameter, and binary label. -/
theorem check_eval (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {a : Fin (c + 1) → F} (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    check hr ρ a (fun x => encode r (ρ (MvPolynomial.eval x P))) u v z w = 0 := by
  rw [check_encode, LagrangeConstraint.check_eval ha P hP, map_zero]
  simp only [linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero]

/-- The query locations, with zero interpolation coefficients removed before reading. -/
noncomputable def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    List ((σ → F) × Coefficients t r) := by
  classical
  exact (point u v z, homogeneousIndex hr w) ::
    (List.finRange (c + 1)).filterMap (fun i =>
      if LagrangeConstraint.weight a z i = 0 then none
      else some (point u v (a i),
        homogeneousIndex hr (scaleLabel ρ (LagrangeConstraint.weight a z i) w)))

theorem queries_length_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    (queries hr ρ a u v z w).length ≤ c + 2 := by
  classical
  unfold queries
  simp only [List.length_cons]
  have h := List.length_filterMap_le (l := List.finRange (c + 1))
    (f := fun i => if LagrangeConstraint.weight a z i = 0 then none
      else some (point u v (a i),
        homogeneousIndex hr (scaleLabel ρ (LagrangeConstraint.weight a z i) w)))
  simp only [List.length_finRange] at h
  omega

/-- The binary decision depends only on the stated, bounded query list. -/
theorem check_congr (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (u v : σ → F) (z : F) (w : Fin t → ZMod 2)
    (H G : (σ → F) → Coefficients t r → ZMod 2)
    (h : ∀ p ∈ queries hr ρ a u v z w, H p.1 p.2 = G p.1 p.2) :
    check hr ρ a H u v z w = check hr ρ a G u v z w := by
  classical
  rw [check, check, h (point u v z, homogeneousIndex hr w) (by simp [queries])]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hi : LagrangeConstraint.weight a z i = 0
  · simp only [hi, weightedRead_zero]
  · rw [weightedRead_of_ne hr ρ _ _ hi, weightedRead_of_ne hr ρ _ _ hi]
    apply h (point u v (a i), homogeneousIndex hr (scaleLabel ρ (LagrangeConstraint.weight a z i) w))
    simp only [queries, List.mem_cons]
    apply Or.inr
    apply List.mem_filterMap.mpr
    exact ⟨i, by simp, by simp [hi]⟩

section Finite

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Normalized binary rejection, with the same field randomness as `LagrangeConstraint`. -/
noncomputable def rejectionRate (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance
    (fun s : (((σ → F) × (σ → F)) × F) × (Fin t → ZMod 2) =>
      check hr ρ a H s.1.1.1 s.1.1.2 0 s.2)
    (fun _ => 0)

/-- The binary projection detects precisely half of all nonzero field residuals. -/
theorem rejectionRate_encode (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (f : (σ → F) → F) :
    rejectionRate hr ρ a (fun x => encode r (ρ (f x))) =
      (1 : ℚ) / 2 * LagrangeConstraint.rejectionRate a f := by
  have hdist (x y : F) : relativeDistance (linearEncode (ρ x)) (linearEncode (ρ y)) =
      if x = y then 0 else (1 : ℚ) / 2 := by
    by_cases hxy : x = y
    · simp [hxy]
    · rw [ite_eq_right hxy]
      exact relativeDistance_linearEncode _ _ (fun h => hxy (ρ.injective h))
  have hz : (linearEncode (ρ 0) : (Fin t → ZMod 2) → ZMod 2) = fun _ => 0 := by
    funext w
    simp only [map_zero, linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero]
  have h := relativeDistance_concatenate (fun x : F => linearEncode (ρ x)) ((1 : ℚ) / 2)
    hdist (fun s : ((σ → F) × (σ → F)) × F => LagrangeConstraint.check a f s.1.1 s.1.2 0)
    (fun _ => 0)
  simp only [hz] at h
  simpa only [rejectionRate, check_encode, LagrangeConstraint.rejectionRate] using h

omit [DecidableEq F] in
/-- Zero normalized rejection for honestly encoded bounded-degree polynomials. -/
theorem rejectionRate_eval (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {a : Fin (c + 1) → F} (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) :
    rejectionRate hr ρ a (fun x => encode r (ρ (MvPolynomial.eval x P))) = 0 := by
  classical
  rw [rejectionRate_encode, LagrangeConstraint.rejectionRate_eval ha P hP, mul_zero]

end Finite

end PCP.Algebraic.BinaryLagrangeConstraint
