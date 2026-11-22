/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardSoundness
import PCP.Algebraic.HadamardAffineQueries
import PCP.Algebraic.BinaryConstraintRobust

/-!
# Decoding a table of received Hadamard words

The average rejection of the rowwise Hadamard tester yields one table of decoded
messages close both on the full coefficient-query space and on homogeneous
queries. No global small-error condition is needed: rows with rejection below
`1/28` use the proved Hadamard soundness theorem, while every other row has error
at most one, which is at most `28` times its rejection.

On good rows, homogeneous-query error is at most twice affine-query error, hence
at most six times rejection. Averaging the pointwise bounds gives the constant
`28` for both distances, with the same decoded message in both conclusions.
The construction uses classical choice and makes no computational-efficiency
claim. The generic finite row index may be empty.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {ι : Type*} {t r : ℕ}

/-- A row always has a decoded message satisfying both linear-in-rejection bounds.
Rows above the soundness threshold use only the universal distance bound. -/
theorem exists_row_message_distance_le (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    ∃ x : Fin t → ZMod 2,
      relativeDistance H (encode r x) ≤ 28 * testRejectionRate hr H ∧
      relativeDistance (fun w => H (homogeneousIndex hr w))
        (fun w => encode r x (homogeneousIndex hr w)) ≤ 28 * testRejectionRate hr H := by
  by_cases hgood : testRejectionRate hr H < (1 : ℚ) / 28
  · obtain ⟨x, hfull, haffine⟩ := test_soundness_at_rejectionRate hr H hgood
    have hhomogeneous := homogeneousDistance_le_twice_affine hr H (encode r x)
    have he : (fun p : Coefficients t 1 => encode r x (embed hr p)) = encode 1 x := by
      funext p
      exact evaluate_embed hr x p
    simp only [Function.comp_def] at hhomogeneous
    rw [he] at hhomogeneous
    have hnonneg := testRejectionRate_nonneg hr H
    exact ⟨x, by linarith, by linarith⟩
  · have hlarge : 1 ≤ 28 * testRejectionRate hr H := by
      have h := le_of_not_gt hgood
      linarith
    exact ⟨0, (relativeDistance_le_one _ _).trans hlarge,
      (relativeDistance_le_one _ _).trans hlarge⟩

section FiniteRows

variable [Fintype ι]

/-- Average of the actual normalized HadTest rejection rates over all rows. -/
noncomputable def averageRejectionRate (hr : 1 ≤ r)
    (H : ι → Coefficients t r → ZMod 2) : ℚ :=
  (∑ i, testRejectionRate hr (H i)) / Fintype.card ι

/-- The average is exactly rejection under a uniform row and an independent
uniform sample of the existing Hadamard tester's randomness. -/
theorem averageRejectionRate_eq_relativeDistance (hr : 1 ≤ r)
    (H : ι → Coefficients t r → ZMod 2) :
    averageRejectionRate hr H =
      relativeDistance (fun s : ι × TestRandomness t r => test hr (H s.1) s.2)
        (fun _ => true) := by
  rw [relativeDistance_prod]
  rfl

theorem averageRejectionRate_nonneg (hr : 1 ≤ r)
    (H : ι → Coefficients t r → ZMod 2) : 0 ≤ averageRejectionRate hr H := by
  rw [averageRejectionRate_eq_relativeDistance]
  exact relativeDistance_nonneg _ _

theorem averageRejectionRate_le_one (hr : 1 ≤ r)
    (H : ι → Coefficients t r → ZMod 2) : averageRejectionRate hr H ≤ 1 := by
  rw [averageRejectionRate_eq_relativeDistance]
  exact relativeDistance_le_one _ _

@[simp] theorem averageRejectionRate_encode (hr : 1 ≤ r) (x : ι → Fin t → ZMod 2) :
    averageRejectionRate hr (fun i => encode r (x i)) = 0 := by
  simp only [averageRejectionRate, testRejectionRate_encode, sum_const_zero, zero_div]

/-- A single decoded message table is close on both query domains. -/
theorem exists_messages_of_average_rejectionRate (hr : 1 ≤ r)
    (H : ι → Coefficients t r → ZMod 2) :
    ∃ x : ι → Fin t → ZMod 2,
      relativeDistance (fun p : ι × Coefficients t r => H p.1 p.2) (encodeFunction r x) ≤
        28 * averageRejectionRate hr H ∧
      relativeDistance (fun p : ι × (Fin t → ZMod 2) => H p.1 (homogeneousIndex hr p.2))
        (fun p => encode r (x p.1) (homogeneousIndex hr p.2)) ≤
        28 * averageRejectionRate hr H := by
  classical
  choose x hfull hhomogeneous using fun i => exists_row_message_distance_le hr (H i)
  refine ⟨x, ?_, ?_⟩
  · rw [relativeDistance_prod]
    calc
      _ ≤ (∑ i, 28 * testRejectionRate hr (H i)) / Fintype.card ι := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact sum_le_sum (fun i _ => hfull i)
      _ = 28 * averageRejectionRate hr H := by rw [← mul_sum, mul_div_assoc]; rfl
  · rw [relativeDistance_prod]
    calc
      _ ≤ (∑ i, 28 * testRejectionRate hr (H i)) / Fintype.card ι := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact sum_le_sum (fun i _ => hhomogeneous i)
      _ = 28 * averageRejectionRate hr H := by rw [← mul_sum, mul_div_assoc]; rfl

end FiniteRows

section FieldRows

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F]
variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- Express the decoded binary messages as field elements using the supplied
coordinate equivalence. The same field function satisfies both distance bounds. -/
theorem exists_field_function_of_average_rejectionRate (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    ∃ f : (σ → F) → F,
      relativeDistance (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
        (encodeFunction r (fun x => ρ (f x))) ≤ 28 * averageRejectionRate hr H ∧
      BinaryLagrangeConstraint.homogeneousDistance hr H (fun x => encode r (ρ (f x))) ≤
        28 * averageRejectionRate hr H := by
  obtain ⟨x, hfull, hhomogeneous⟩ := exists_messages_of_average_rejectionRate hr H
  refine ⟨fun u => ρ.symm (x u), ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hfull
  · simpa only [BinaryLagrangeConstraint.homogeneousDistance,
      LinearEquiv.apply_symm_apply] using hhomogeneous

end FieldRows

end PCP.Algebraic.Hadamard
