/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLagrangeConstraint
import PCP.Algebraic.HadamardTest
import PCP.Algebraic.FiniteDistance

/-!
# The binary low-degree test

The verifier chooses between Hadamard consistency and the generator constraint
at zero. Each field coefficient is incorporated into the homogeneous binary
label. An unused scalar in the finite seed does not affect the test.
-/

namespace PCP.Algebraic.BinaryLowDegreeTest

open Finset BinaryPolynomialSpace Hadamard

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {c t r : ℕ}

abbrev InterpolationRandomness (F σ : Type*) (t : ℕ) :=
  (((σ → F) × (σ → F)) × F) × (Fin t → ZMod 2)

abbrev TestRandomness (F σ : Type*) (t r : ℕ) :=
  Bool × (((σ → F) × Hadamard.TestRandomness t r) × InterpolationRandomness F σ t)

/-- The binary interpolation branch, expressed as an acceptance decision. -/
noncomputable def interpolationTest (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2)
    (s : InterpolationRandomness F σ t) : Bool := by
  classical
  exact decide (BinaryLagrangeConstraint.check hr ρ a H s.1.1.1 s.1.1.2 0 s.2 = 0)

/-- False chooses a Hadamard row; true chooses the interpolation check. -/
noncomputable def test (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (s : TestRandomness F σ t r) : Bool :=
  if s.1 then interpolationTest hr ρ a H s.2.2
  else Hadamard.test hr (H s.2.1.1) s.2.1.2

/-- The query list follows the selected branch and does not read the other branch. -/
noncomputable def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (s : TestRandomness F σ t r) :
    List ((σ → F) × Coefficients t r) :=
  if s.1 then
    BinaryLagrangeConstraint.queries hr ρ a s.2.2.1.1.1 s.2.2.1.1.2 0 s.2.2.2
  else (Hadamard.testQueries hr s.2.1.2).map (fun p => (s.2.1.1, p))

theorem queries_length_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (s : TestRandomness F σ t r) :
    (queries hr ρ a s).length ≤ max (2 * r + 4) (c + 2) := by
  unfold queries
  split
  · exact (BinaryLagrangeConstraint.queries_length_le hr ρ a _ _ _ _).trans (le_max_right _ _)
  · simp only [List.length_map, Hadamard.testQueries_length]
    exact le_max_left _ _

/-- The decision uses only the listed responses. -/
theorem test_congr (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (s : TestRandomness F σ t r)
    (H G : (σ → F) → Coefficients t r → ZMod 2)
    (h : ∀ p ∈ queries hr ρ a s, H p.1 p.2 = G p.1 p.2) :
    test hr ρ a H s = test hr ρ a G s := by
  classical
  unfold test
  split_ifs with hb
  · have he := BinaryLagrangeConstraint.check_congr hr ρ a
      s.2.2.1.1.1 s.2.2.1.1.2 0 s.2.2.2 H G
      (by simpa only [queries, hb, ↓reduceIte] using h)
    simp only [interpolationTest, he]
  · apply Hadamard.test_congr
    intro p hp
    apply h (s.2.1.1, p)
    simp only [queries, hb]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- Every honestly encoded bounded-degree polynomial passes every sample. -/
theorem test_eval (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {a : Fin (c + 1) → F} (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c)
    (s : TestRandomness F σ t r) :
    test hr ρ a (fun x => encode r (ρ (MvPolynomial.eval x P))) s = true := by
  classical
  unfold test
  split
  · simp only [interpolationTest, BinaryLagrangeConstraint.check_eval hr ρ ha P hP,
      decide_true]
  · exact Hadamard.test_encode hr _ _

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- Rejection probability under the explicit independent finite seed. -/
noncomputable def rejectionRate (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance (test hr ρ a H) (fun _ => true)

theorem interpolationTest_distance (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    relativeDistance (interpolationTest hr ρ a H) (fun _ => true) =
      BinaryLagrangeConstraint.rejectionRate hr ρ a H := by
  classical
  simp [interpolationTest, BinaryLagrangeConstraint.rejectionRate, relativeDistance, hammingDist]

/-- Exact branch accounting, including both unused independent seeds. -/
theorem rejectionRate_eq_average (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    rejectionRate hr ρ a H =
      ((∑ x, Hadamard.testRejectionRate hr (H x)) / Fintype.card (σ → F) +
        BinaryLagrangeConstraint.rejectionRate hr ρ a H) / 2 := by
  classical
  have hfst : relativeDistance
      (fun s : ((σ → F) × Hadamard.TestRandomness t r) ×
          InterpolationRandomness F σ t => Hadamard.test hr (H s.1.1) s.1.2)
      (fun _ => true) =
      (∑ x, Hadamard.testRejectionRate hr (H x)) / Fintype.card (σ → F) := by
    rw [relativeDistance_comp_fst
      (fun z : (σ → F) × Hadamard.TestRandomness t r => Hadamard.test hr (H z.1) z.2)
      (fun _ => true), relativeDistance_prod]
    rfl
  have hsnd : relativeDistance
      (fun s : ((σ → F) × Hadamard.TestRandomness t r) ×
          InterpolationRandomness F σ t => interpolationTest hr ρ a H s.2)
      (fun _ => true) = BinaryLagrangeConstraint.rejectionRate hr ρ a H := by
    rw [relativeDistance_prod]
    simp only [interpolationTest_distance, sum_const, card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero)
  rw [rejectionRate, relativeDistance_prod]
  simp only [Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat, test,
    Bool.false_eq_true, ↓reduceIte, hsnd, hfst]
  ring

theorem rejectionRate_nonneg (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    0 ≤ rejectionRate hr ρ a H := relativeDistance_nonneg _ _

theorem rejectionRate_eval (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) {a : Fin (c + 1) → F}
    (ha : Function.Injective a) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) :
    rejectionRate hr ρ a (fun x => encode r (ρ (MvPolynomial.eval x P))) = 0 := by
  have h := funext (test_eval hr ρ ha P hP)
  rw [rejectionRate, h, relativeDistance_self]

end Finite

end PCP.Algebraic.BinaryLowDegreeTest
