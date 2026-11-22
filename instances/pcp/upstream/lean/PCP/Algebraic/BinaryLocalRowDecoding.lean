/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLowDegreeBranchBounds
import PCP.Algebraic.GeneratorLowDegreeTest

/-!
# Decoding arbitrary received binary polynomial rows

The proved generator low-degree theorem supplies a polynomial on rows below its
rejection threshold. For all other rows, distance is at most one, which is
bounded by an explicit constant times rejection. The same polynomial satisfies
both the full-query and homogeneous-query bounds, with no small-error premise.
Coordinates may be any finite type, including the product types of the
set-multilinear inner encoding. No efficient decoding algorithm is claimed.
-/

namespace PCP.Algebraic.BinaryLocalRowDecoding

open Finset BinaryPolynomialSpace Hadamard BinaryLowDegreeTest
open scoped BigOperators

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F]
variable [Fintype F] [Fintype σ] [DecidableEq σ] {c t r : ℕ}

/-- A uniform decoding constant, incorporating the proved soundness threshold. -/
def decodingConstant (c : ℕ) : ℚ :=
  4 * (c + 2 : ℚ) ^ 2 * (112 * (c + 2 : ℚ) + 60)

theorem decodingConstant_nonneg (c : ℕ) : 0 ≤ decodingConstant c := by
  unfold decodingConstant
  positivity

/-- The small-rejection binary guarantee for arbitrary finite coordinate types.
It is derived from the proved generic field theorem, without transporting or
assuming a binary tester's soundness. -/
theorem exists_close_of_small_rejection
    (hq : 2 * c < Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (ha : GeneratorLowDegreeTest.IsGeneratorNodes a)
    (H : (σ → F) → Coefficients t r → ZMod 2)
    (hsmall : (112 * (c + 2 : ℕ) + 4) * rejectionRate hr ρ a H ≤
      GeneratorLowDegreeTest.smallError c) :
    ∃ Q : MvPolynomial σ F, Q.totalDegree ≤ c ∧
      relativeDistance (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
        (encodeFunction r (fun x => ρ (MvPolynomial.eval x Q))) ≤
          (112 * (c + 2 : ℚ) + 60) * rejectionRate hr ρ a H ∧
      BinaryLagrangeConstraint.homogeneousDistance hr H
        (fun x => encode r (ρ (MvPolynomial.eval x Q))) ≤
          (112 * (c + 2 : ℚ) + 60) * rejectionRate hr ρ a H := by
  classical
  let κ := rejectionRate hr ρ a H
  let n : ℚ := c + 2
  have hn : 0 ≤ n := by dsimp [n]; positivity
  obtain ⟨hη, hβ⟩ := branch_rejectionRates_le_twice hr ρ a H
  obtain ⟨f, hfull, hhom⟩ := exists_field_function_of_average_rejectionRate hr ρ H
  let ε := BinaryLagrangeConstraint.homogeneousDistance hr H (fun x => encode r (ρ (f x)))
  have hhom' : ε ≤ 56 * κ := by dsimp [ε, κ]; linarith
  have hfull' : relativeDistance (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
      (encodeFunction r (fun x => ρ (f x))) ≤ 56 * κ := by dsimp [κ]; linarith
  have hfield := BinaryLagrangeConstraint.field_rejectionRate_le hr ρ a H f
  have hrejection : LagrangeConstraint.rejectionRate a f ≤ (112 * n + 4) * κ := by
    have hmul := mul_le_mul_of_nonneg_left hhom' hn
    change LagrangeConstraint.rejectionRate a f ≤
      2 * BinaryLagrangeConstraint.rejectionRate hr ρ a H + 2 * (c + 2 : ℕ) * ε at hfield
    simp only [Nat.cast_add, Nat.cast_ofNat] at hfield
    change LagrangeConstraint.rejectionRate a f ≤
      2 * BinaryLagrangeConstraint.rejectionRate hr ρ a H + 2 * n * ε at hfield
    change BinaryLagrangeConstraint.rejectionRate hr ρ a H ≤ 2 * κ at hβ
    nlinarith
  have hsmall' : LagrangeConstraint.rejectionRate a f ≤ GeneratorLowDegreeTest.smallError c :=
    hrejection.trans (by simpa only [n, κ, Nat.cast_add, Nat.cast_ofNat] using hsmall)
  obtain ⟨Q, hQ, hclose⟩ := FixedLagrangeConstraint.exists_close hq ha f le_rfl
    (hsmall'.trans_lt (GeneratorLowDegreeTest.smallError_lt c))
  change relativeDistance f (fun x => MvPolynomial.eval x Q) ≤
    2 * LagrangeConstraint.rejectionRate a f at hclose
  have hfieldDistance : relativeDistance f (fun x => MvPolynomial.eval x Q) ≤
      2 * (112 * n + 4) * κ := by
    exact hclose.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hrejection (show (0 : ℚ) ≤ 2 by norm_num))
  refine ⟨Q, hQ, ?_, ?_⟩
  · have ht := relativeDistance_triangle
      (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
      (encodeFunction r (fun x => ρ (f x)))
      (encodeFunction r (fun x => ρ (MvPolynomial.eval x Q)))
    rw [relativeDistance_encodeFunction_map ρ ρ.injective hr] at ht
    have h : relativeDistance (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
        (encodeFunction r (fun x => ρ (MvPolynomial.eval x Q))) ≤
          (112 * n + 60) * κ := by
      ring_nf at hfieldDistance ⊢
      linarith
    simpa only [n, κ, Nat.cast_add, Nat.cast_ofNat] using h
  · have ht := BinaryLagrangeConstraint.homogeneousDistance_triangle hr H
      (fun x => encode r (ρ (f x))) (fun x => encode r (ρ (MvPolynomial.eval x Q)))
    rw [BinaryLagrangeConstraint.homogeneousDistance_encode] at ht
    have h : BinaryLagrangeConstraint.homogeneousDistance hr H
        (fun x => encode r (ρ (MvPolynomial.eval x Q))) ≤
          (112 * n + 60) * κ := by
      change _ ≤ ε + _ at ht
      ring_nf at hfieldDistance ⊢
      linarith
    simpa only [n, κ, Nat.cast_add, Nat.cast_ofNat] using h

/-- Every received row admits an actual bounded-degree polynomial satisfying
both distance bounds; there is no small-rejection hypothesis. -/
theorem exists_polynomial_distance_le
    (hq : 2 * c < Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (ha : GeneratorLowDegreeTest.IsGeneratorNodes a)
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    ∃ Q : MvPolynomial σ F, Q.totalDegree ≤ c ∧
      relativeDistance (fun p : (σ → F) × Coefficients t r => H p.1 p.2)
        (encodeFunction r (fun x => ρ (MvPolynomial.eval x Q))) ≤
          decodingConstant c * rejectionRate hr ρ a H ∧
      BinaryLagrangeConstraint.homogeneousDistance hr H
        (fun x => encode r (ρ (MvPolynomial.eval x Q))) ≤
          decodingConstant c * rejectionRate hr ρ a H := by
  classical
  by_cases hgood : (112 * (c + 2 : ℕ) + 4) * rejectionRate hr ρ a H ≤
      GeneratorLowDegreeTest.smallError c
  · obtain ⟨Q, hQ, hfull, hhom⟩ := exists_close_of_small_rejection hq hr ρ a ha H hgood
    have hfactor : 112 * (c + 2 : ℚ) + 60 ≤
        decodingConstant c := by
      dsimp [decodingConstant]
      have hn : (1 : ℚ) ≤ 4 * (c + 2 : ℚ) ^ 2 := by
        have hc : (0 : ℚ) ≤ c := Nat.cast_nonneg _
        nlinarith
      exact le_mul_of_one_le_left (by positivity) hn
    have hbound := mul_le_mul_of_nonneg_right hfactor (rejectionRate_nonneg hr ρ a H)
    exact ⟨Q, hQ, hfull.trans hbound, hhom.trans hbound⟩
  · have hlarge : 1 ≤ decodingConstant c * rejectionRate hr ρ a H := by
      have h := lt_of_not_ge hgood
      have hk := rejectionRate_nonneg hr ρ a H
      dsimp [GeneratorLowDegreeTest.smallError] at h
      have hpos : (0 : ℚ) < 4 * (c + 2 : ℚ) ^ 2 := by positivity
      have hh := (div_lt_iff₀ hpos).mp h
      dsimp [decodingConstant]
      simp only [Nat.cast_add, Nat.cast_ofNat] at hh
      have hnonneg := mul_nonneg hpos.le hk
      nlinarith
    exact ⟨0, by simp, (relativeDistance_le_one _ _).trans hlarge,
      (relativeDistance_le_one _ _).trans hlarge⟩

/-- A finite family can be decoded simultaneously, with both normalized global
distances bounded by the average actual row rejection. Empty families are allowed. -/
theorem exists_polynomials_of_average_rejection {I : Type*} [Fintype I]
    (hq : 2 * c < Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (ha : GeneratorLowDegreeTest.IsGeneratorNodes a)
    (H : I → (σ → F) → Coefficients t r → ZMod 2) :
    ∃ Q : I → MvPolynomial σ F, (∀ i, (Q i).totalDegree ≤ c) ∧
      relativeDistance
        (fun p : I × ((σ → F) × Coefficients t r) => H p.1 p.2.1 p.2.2)
        (fun p => encode r (ρ (MvPolynomial.eval p.2.1 (Q p.1))) p.2.2) ≤
          decodingConstant c * (𝔼 i, rejectionRate hr ρ a (H i)) ∧
      relativeDistance
        (fun p : I × ((σ → F) × (Fin t → ZMod 2)) =>
          H p.1 p.2.1 (homogeneousIndex hr p.2.2))
        (fun p => encode r (ρ (MvPolynomial.eval p.2.1 (Q p.1)))
          (homogeneousIndex hr p.2.2)) ≤
          decodingConstant c * (𝔼 i, rejectionRate hr ρ a (H i)) := by
  classical
  choose Q hQ hfull hhom using fun i => exists_polynomial_distance_le hq hr ρ a ha (H i)
  refine ⟨Q, hQ, ?_, ?_⟩
  · rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]
    calc
      _ ≤ (∑ i, decodingConstant c * rejectionRate hr ρ a (H i)) / Fintype.card I :=
        div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hfull i)) (Nat.cast_nonneg _)
      _ = _ := by rw [← mul_sum, mul_div_assoc]
  · rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]
    calc
      _ ≤ (∑ i, decodingConstant c * rejectionRate hr ρ a (H i)) / Fintype.card I :=
        div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hhom i)) (Nat.cast_nonneg _)
      _ = _ := by rw [← mul_sum, mul_div_assoc]

end PCP.Algebraic.BinaryLocalRowDecoding
