/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardComposition
import PCP.Algebraic.HadamardCorrection
import PCP.Algebraic.FiniteDistance

/-!
# Randomized derived polynomial oracles

Translate an affine query about `P(u)` into a degree-bounded query about `u`, then
self-correct that query using a fresh uniform coefficient seed. Each derived
answer makes two actual received-oracle reads. Its error at every requested
query is at most twice the corresponding row distance.

The averaged statements keep the self-correction seed explicit. The derived
oracle is not treated as a fixed nearby word. Arbitrary point-dependent label
maps and downstream decisions may be sampled before the fresh seed, which is
sufficient for replacing the single primary read in a zero-on-grid check.
-/

namespace PCP.Algebraic.HadamardDerivedOracle

open Finset BinaryPolynomialSpace Hadamard
open scoped BigOperators

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {t r : ℕ}

/-- A derived answer has an explicit fresh self-correction seed. -/
noncomputable def answer (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r) (H : Coefficients t r → ZMod 2)
    (L : Coefficients t 1) (R : Coefficients t r) : ZMod 2 :=
  selfCorrect H (HadamardComposition.query ρ P L hP) R

/-- The two actual query locations, counted with multiplicity even when they coincide. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r)
    (L : Coefficients t 1) (R : Coefficients t r) : List (Coefficients t r) :=
  [HadamardComposition.query ρ P L hP + R, R]

@[simp] theorem queries_length (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r)
    (L : Coefficients t 1) (R : Coefficients t r) : (queries ρ P hP L R).length = 2 := rfl

/-- The answer depends only on the stated two queries. -/
theorem answer_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r)
    (H G : Coefficients t r → ZMod 2) (L : Coefficients t 1) (R : Coefficients t r)
    (h : ∀ q ∈ queries ρ P hP L R, H q = G q) :
    answer ρ P hP H L R = answer ρ P hP G L R := by
  have h₁ := h (HadamardComposition.query ρ P L hP + R) (by simp [queries])
  have h₂ := h R (by simp [queries])
  simp only [answer, selfCorrect, h₁, h₂]

/-- Honest encodings give the requested affine observation for every seed. -/
theorem answer_encode (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r) (u : F)
    (L : Coefficients t 1) (R : Coefficients t r) :
    answer ρ P hP (encode r (ρ u)) L R = encode 1 (ρ (P.eval u)) L := by
  change selfCorrect (encode r (ρ u)).toAddMonoidHom
    (HadamardComposition.query ρ P L hP) R = _
  rw [selfCorrect_addHom]
  exact HadamardComposition.encode_query ρ P L hP u

/-- The derived read is reliable at every fixed requested affine query. -/
theorem answer_failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r) (u : F)
    (H : Coefficients t r → ZMod 2) (L : Coefficients t 1) :
    relativeDistance (answer ρ P hP H L) (fun _ => encode 1 (ρ (P.eval u)) L) ≤
      2 * relativeDistance H (encode r (ρ u)) := by
  have h := selfCorrect_failure_le (encode r (ρ u)).toAddMonoidHom H
    (HadamardComposition.query ρ P L hP)
  change relativeDistance (answer ρ P hP H L)
    (fun _ => encode r (ρ u) (HadamardComposition.query ρ P L hP)) ≤ _ at h
  rwa [HadamardComposition.encode_query] at h

/-- Any label distribution obtained from a uniform finite seed preserves the row bound.
The label map need not be injective, surjective, or independent of other sampled data. -/
theorem labels_failure_le {A : Type*} [Fintype A]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : Polynomial F) (hP : P.natDegree ≤ r) (u : F)
    (H : Coefficients t r → ZMod 2) (L : A → Coefficients t 1) :
    relativeDistance
      (fun s : A × Coefficients t r => answer ρ P hP H (L s.1) s.2)
      (fun s => encode 1 (ρ (P.eval u)) (L s.1)) ≤
        2 * relativeDistance H (encode r (ρ u)) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · have hz : relativeDistance
        (fun s : A × Coefficients t r => answer ρ P hP H (L s.1) s.2)
        (fun s => encode 1 (ρ (P.eval u)) (L s.1)) = 0 := by
      simp [relativeDistance]
    rw [hz]
    exact mul_nonneg (by norm_num) (relativeDistance_nonneg _ _)
  · exact relativeDistance_prod_le _ _ (fun a => answer_failure_le ρ P hP u H (L a))

section Rows

variable {I : Type*} [Fintype I]

/-- Full coefficient-space error of the primary received oracle. -/
noncomputable def fullDistance (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : I → Coefficients t r → ZMod 2) (f : I → F) : ℚ :=
  relativeDistance (fun iq : I × Coefficients t r => H iq.1 iq.2)
    (fun iq => encode r (ρ (f iq.1)) iq.2)

/-- Averaging rows and arbitrary point-dependent requested labels costs twice full distance.
The final coefficient seed is still fresh and explicitly sampled. -/
theorem averaged_failure_le {A : Type*} [Fintype A]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : I → Polynomial F) (hP : ∀ i, (P i).natDegree ≤ r)
    (H : I → Coefficients t r → ZMod 2) (f : I → F)
    (L : I → A → Coefficients t 1) :
    relativeDistance
      (fun s : I × (A × Coefficients t r) => answer ρ (P s.1) (hP s.1) (H s.1) (L s.1 s.2.1) s.2.2)
      (fun s => encode 1 (ρ ((P s.1).eval (f s.1))) (L s.1 s.2.1)) ≤
        2 * fullDistance ρ H f := by
  rw [relativeDistance_prod, fullDistance, relativeDistance_prod, ← mul_div_assoc, mul_sum]
  exact div_le_div_of_nonneg_right
    (sum_le_sum (fun i _ => labels_failure_le ρ (P i) (hP i) (f i) (H i) (L i)))
    (Nat.cast_nonneg _)

/-- Uniform affine output queries retain the same factor-two error bound. -/
theorem affine_failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : I → Polynomial F) (hP : ∀ i, (P i).natDegree ≤ r)
    (H : I → Coefficients t r → ZMod 2) (f : I → F) :
    relativeDistance
      (fun s : I × (Coefficients t 1 × Coefficients t r) =>
        answer ρ (P s.1) (hP s.1) (H s.1) s.2.1 s.2.2)
      (fun s => encode 1 (ρ ((P s.1).eval (f s.1))) s.2.1) ≤
        2 * fullDistance ρ H f :=
  averaged_failure_le ρ P hP H f (fun _ L => L)

/-- Homogeneous output queries also retain the factor-two bound; no restriction loss is needed. -/
theorem homogeneous_failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : I → Polynomial F) (hP : ∀ i, (P i).natDegree ≤ r)
    (H : I → Coefficients t r → ZMod 2) (f : I → F) :
    relativeDistance
      (fun s : I × ((Fin t → ZMod 2) × Coefficients t r) =>
        answer ρ (P s.1) (hP s.1) (H s.1) (homogeneousIndex (le_refl 1) s.2.1) s.2.2)
      (fun s => linearEncode (ρ ((P s.1).eval (f s.1))) s.2.1) ≤
        2 * fullDistance ρ H f := by
  simpa only [encode_homogeneousIndex] using
    averaged_failure_le ρ P hP H f (fun _ w => homogeneousIndex (le_refl 1) w)

/-- Replacing one derived answer costs only its marginal error.
Other randomness may be included in the label seed, before drawing the fresh correction seed. -/
theorem decision_distance_le {A B : Type*} [Fintype A] [DecidableEq B]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : I → Polynomial F) (hP : ∀ i, (P i).natDegree ≤ r)
    (H : I → Coefficients t r → ZMod 2) (f : I → F)
    (L : I → A → Coefficients t 1) (decision : I → A → ZMod 2 → B) :
    relativeDistance
      (fun s : I × (A × Coefficients t r) =>
        decision s.1 s.2.1 (answer ρ (P s.1) (hP s.1) (H s.1) (L s.1 s.2.1) s.2.2))
      (fun s => decision s.1 s.2.1 (encode 1 (ρ ((P s.1).eval (f s.1))) (L s.1 s.2.1))) ≤
        2 * fullDistance ρ H f := by
  apply (relativeDistance_le_of_disagreement _ _ _ _ ?_).trans
    (averaged_failure_le ρ P hP H f L)
  intro s hne he
  exact hne (congrArg (decision s.1 s.2.1) he)

/-- The rejection of a fresh randomized derived read inherits any fixed honest-decision bound.
This theorem does not freeze a correction seed or postulate a fixed derived oracle. -/
theorem rejection_transfer {A B : Type*} [Fintype A] [DecidableEq B]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : I → Polynomial F) (hP : ∀ i, (P i).natDegree ≤ r)
    (H : I → Coefficients t r → ZMod 2) (f : I → F)
    (L : I → A → Coefficients t 1) (decision : I → A → ZMod 2 → B)
    (accept : I → A → B) :
    relativeDistance
      (fun s : I × A => decision s.1 s.2 (encode 1 (ρ ((P s.1).eval (f s.1))) (L s.1 s.2)))
      (fun s => accept s.1 s.2) ≤
      relativeDistance
        (fun s : I × (A × Coefficients t r) =>
          decision s.1 s.2.1 (answer ρ (P s.1) (hP s.1) (H s.1) (L s.1 s.2.1) s.2.2))
        (fun s => accept s.1 s.2.1) + 2 * fullDistance ρ H f := by
  let ideal : I × A → B := fun s =>
    decision s.1 s.2 (encode 1 (ρ ((P s.1).eval (f s.1))) (L s.1 s.2))
  let actual : I × (A × Coefficients t r) → B := fun s =>
    decision s.1 s.2.1 (answer ρ (P s.1) (hP s.1) (H s.1) (L s.1 s.2.1) s.2.2)
  have hlift := relativeDistance_comp_equiv (Equiv.prodAssoc I A (Coefficients t r))
    (fun s : I × (A × Coefficients t r) => ideal (s.1, s.2.1))
    (fun s => accept s.1 s.2.1)
  simp only [Equiv.prodAssoc_apply] at hlift
  rw [relativeDistance_comp_fst (κ := Coefficients t r) ideal (fun s => accept s.1 s.2)] at hlift
  have ht := relativeDistance_triangle (fun s : I × (A × Coefficients t r) => ideal (s.1, s.2.1))
    actual (fun s => accept s.1 s.2.1)
  rw [← hlift, relativeDistance_comm (fun s : I × (A × Coefficients t r) =>
    ideal (s.1, s.2.1)) actual] at ht
  have he := decision_distance_le ρ P hP H f L decision
  change relativeDistance actual (fun s => ideal (s.1, s.2.1)) ≤ _ at he
  change relativeDistance ideal (fun s => accept s.1 s.2) ≤ _
  linarith

end Rows

section Cubic

variable [Nontrivial F]

/-- The three-color membership polynomial from the algebraic verifier. -/
noncomputable def cubic : Polynomial F := Polynomial.X ^ 3 - 1

/-- A point-dependent weight can be absorbed into the same cubic query. -/
noncomputable def weightedCubic (a : F) : Polynomial F := Polynomial.C a * cubic

omit [Algebra (ZMod 2) F] in
theorem natDegree_cubic_le : (cubic : Polynomial F).natDegree ≤ 3 := by
  calc
    _ ≤ max (Polynomial.X ^ 3 : Polynomial F).natDegree (1 : Polynomial F).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ = 3 := by simp

omit [Algebra (ZMod 2) F] in
theorem natDegree_weightedCubic_le (a : F) : (weightedCubic a).natDegree ≤ 3 :=
  (Polynomial.natDegree_C_mul_le a cubic).trans natDegree_cubic_le

omit [Algebra (ZMod 2) F] [Nontrivial F] in
@[simp] theorem eval_cubic (u : F) : (cubic : Polynomial F).eval u = u ^ 3 - 1 := by
  simp [cubic]

omit [Algebra (ZMod 2) F] [Nontrivial F] in
@[simp] theorem eval_weightedCubic (a u : F) :
    (weightedCubic a).eval u = a * (u ^ 3 - 1) := by
  simp [weightedCubic]

/-- Honest cubic derived reads produce the requested affine encoding bit. -/
theorem answer_cubic_encode (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (u : F)
    (L : Coefficients t 1) (R : Coefficients t 3) :
    answer ρ cubic natDegree_cubic_le (encode 3 (ρ u)) L R = encode 1 (ρ (u ^ 3 - 1)) L := by
  simpa only [eval_cubic] using answer_encode ρ cubic natDegree_cubic_le u L R

/-- Zero weights need no exclusion; the honest weighted cubic identity still holds. -/
theorem answer_weightedCubic_encode (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a u : F)
    (L : Coefficients t 1) (R : Coefficients t 3) :
    answer ρ (weightedCubic a) (natDegree_weightedCubic_le a) (encode 3 (ρ u)) L R =
      encode 1 (ρ (a * (u ^ 3 - 1))) L := by
  simpa only [eval_weightedCubic] using
    answer_encode ρ (weightedCubic a) (natDegree_weightedCubic_le a) u L R

variable {I : Type*} [Fintype I]

/-- Cubic membership reads have the same randomized homogeneous marginal bound. -/
theorem cubic_homogeneous_failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : I → Coefficients t 3 → ZMod 2) (f : I → F) :
    relativeDistance
      (fun s : I × ((Fin t → ZMod 2) × Coefficients t 3) =>
        answer ρ cubic natDegree_cubic_le (H s.1) (homogeneousIndex (le_refl 1) s.2.1) s.2.2)
      (fun s => linearEncode (ρ ((f s.1) ^ 3 - 1)) s.2.1) ≤ 2 * fullDistance ρ H f := by
  simpa only [eval_cubic] using
    homogeneous_failure_le ρ (fun _ => cubic) (fun _ => natDegree_cubic_le) H f

/-- Arbitrary point-dependent weights preserve the bound, including every zero-weight point. -/
theorem weightedCubic_homogeneous_failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (E : I → F) (H : I → Coefficients t 3 → ZMod 2) (f : I → F) :
    relativeDistance
      (fun s : I × ((Fin t → ZMod 2) × Coefficients t 3) =>
        answer ρ (weightedCubic (E s.1)) (natDegree_weightedCubic_le (E s.1))
          (H s.1) (homogeneousIndex (le_refl 1) s.2.1) s.2.2)
      (fun s => linearEncode (ρ (E s.1 * ((f s.1) ^ 3 - 1))) s.2.1) ≤
        2 * fullDistance ρ H f := by
  simpa only [eval_weightedCubic] using
    homogeneous_failure_le ρ (fun i => weightedCubic (E i))
      (fun i => natDegree_weightedCubic_le (E i)) H f

end Cubic
end PCP.Algebraic.HadamardDerivedOracle
