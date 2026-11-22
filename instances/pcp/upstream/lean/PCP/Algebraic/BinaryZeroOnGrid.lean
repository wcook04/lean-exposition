/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ZeroOnGridCheck
import PCP.Algebraic.HadamardWeights
import PCP.Algebraic.FiniteDistance

/-!
# Binary zero-on-grid verification

The verifier reads three homogeneous Hadamard bits at a uniform point and a
shared uniform binary label. It checks `M(x,0)=0` and `M(x,Z_H(x))=P(x)` through
that label. A failed field pair is detected on at least half the labels, so the
proved algebraic zero-on-grid bound transfers to honest binary encodings.

Robustness is stated in terms of the three actual answer-error marginals. The
certificate queries lie on special graphs, so their errors are not silently
replaced by the certificate oracle's global distance.
-/

namespace PCP.Algebraic.BinaryZeroOnGrid

open Finset MvPolynomial BinaryPolynomialSpace Hadamard HadamardWeights GridVanishing
open scoped BigOperators

variable {F : Type*} [Field F] {m d t r : ℕ}

/-- The first certificate query substitutes zero in the second variable block. -/
def zeroPoint (x : Fin m → F) : (Fin m ⊕ Fin m) → F := Sum.elim x (fun _ => 0)

/-- The recovery query substitutes the coordinate grid-vanishing polynomials. -/
noncomputable def recoveryPoint (H : Finset F) (x : Fin m → F) : (Fin m ⊕ Fin m) → F :=
  Sum.elim x (fun i => eval x (coordinate H i))

/-- Both checks use the same linear label and reject if either residual is nonzero. -/
def checkBits (p m₀ mZ : ZMod 2) : ZMod 2 × ZMod 2 := (m₀, mZ - p)

/-- The actual three-read test on two received binary oracles. -/
noncomputable def check (hr : 1 ≤ r) (H : Finset F)
    (p : (Fin m → F) → Coefficients t r → ZMod 2)
    (M : ((Fin m ⊕ Fin m) → F) → Coefficients t r → ZMod 2)
    (x : Fin m → F) (w : Fin t → ZMod 2) : ZMod 2 × ZMod 2 :=
  checkBits (p x (homogeneousIndex hr w))
    (M (zeroPoint x) (homogeneousIndex hr w))
    (M (recoveryPoint H x) (homogeneousIndex hr w))

/-- All three actual query locations, tagged by their oracle. -/
noncomputable def queries (hr : 1 ≤ r) (H : Finset F) (x : Fin m → F)
    (w : Fin t → ZMod 2) :
    List (((Fin m → F) × Coefficients t r) ⊕
      (((Fin m ⊕ Fin m) → F) × Coefficients t r)) :=
  [Sum.inl (x, homogeneousIndex hr w),
    Sum.inr (zeroPoint x, homogeneousIndex hr w),
    Sum.inr (recoveryPoint H x, homogeneousIndex hr w)]

@[simp] theorem queries_length (hr : 1 ≤ r) (H : Finset F) (x : Fin m → F)
    (w : Fin t → ZMod 2) : (queries hr H x w).length = 3 := rfl

section Encoding

variable [Algebra (ZMod 2) F]

/-- Honest answers are the homogeneous projections of the two actual field residuals. -/
theorem check_encode (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : Finset F) (P : MvPolynomial (Fin m) F)
    (M : MvPolynomial (Fin m ⊕ Fin m) F) (x : Fin m → F) (w : Fin t → ZMod 2) :
    check hr H (fun x => encode r (ρ (eval x P))) (fun x => encode r (ρ (eval x M))) x w =
      (linearEncode (ρ (eval (zeroPoint x) M)) w,
        linearEncode (ρ (eval (recoveryPoint H x) M - eval x P)) w) := by
  simp only [check, checkBits, encode_homogeneousIndex, linearEncode_comm, map_sub]

/-- A formal vanishing certificate passes at every point and label. -/
theorem check_encode_eq_zero (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {H : Finset F} {P : MvPolynomial (Fin m) F}
    {M : MvPolynomial (Fin m ⊕ Fin m) F} (hM : IsCertificate H P M)
    (x : Fin m → F) (w : Fin t → ZMod 2) :
    check hr H (fun x => encode r (ρ (eval x P))) (fun x => encode r (ρ (eval x M))) x w =
      (0, 0) := by
  have hzero : eval (zeroPoint x) M = 0 := by
    simpa [zeroPoint, eval_substitute] using congrArg (eval x) hM.1
  have hrec : eval (recoveryPoint H x) M = eval x P := by
    simpa only [recoveryPoint, eval_substitute] using congrArg (eval x) hM.2
  rw [check_encode, hzero, hrec, sub_self, map_zero]
  simp only [linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero]

private theorem linearEncode_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) :
    (linearEncode (ρ 0) : (Fin t → ZMod 2) → ZMod 2) = fun _ => 0 := by
  funext w
  simp only [map_zero, linearEncode_apply, Pi.zero_apply, zero_mul, sum_const_zero]

/-- Projecting two distinct field pairs by one shared label detects at least one half. -/
theorem pair_distance_ge_half (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a b : F × F) (hab : a ≠ b) :
    (1 : ℚ) / 2 ≤ relativeDistance
      (fun w => (linearEncode (ρ a.1) w, linearEncode (ρ a.2) w))
      (fun w => (linearEncode (ρ b.1) w, linearEncode (ρ b.2) w)) := by
  have hcoord : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra hn
    push Not at hn
    exact hab (Prod.ext hn.1 hn.2)
  rcases hcoord with h | h
  · rw [← relativeDistance_linearEncode (ρ a.1) (ρ b.1) (fun he => h (ρ.injective he))]
    exact relativeDistance_le_of_disagreement _ _ _ _
      (fun _ hne he => hne (congrArg Prod.fst he))
  · rw [← relativeDistance_linearEncode (ρ a.2) (ρ b.2) (fun he => h (ρ.injective he))]
    exact relativeDistance_le_of_disagreement _ _ _ _
      (fun _ hne he => hne (congrArg Prod.snd he))

end Encoding

section Finite

variable [Fintype F] [DecidableEq F]

/-- Normalized rejection of either binary residual, sampling the point and shared label. -/
noncomputable def rejectionRate (hr : 1 ≤ r) (H : Finset F)
    (p : (Fin m → F) → Coefficients t r → ZMod 2)
    (M : ((Fin m ⊕ Fin m) → F) → Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance (fun s : (Fin m → F) × (Fin t → ZMod 2) => check hr H p M s.1 s.2)
    (fun _ => (0, 0))

variable [Algebra (ZMod 2) F]

/-- A shared binary label detects at least half of the failed field-level pairs. -/
theorem rejectionRate_encode_ge_half_field (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Finset F)
    (P : MvPolynomial (Fin m) F) (M : MvPolynomial (Fin m ⊕ Fin m) F) :
    (1 - acceptanceRate H P M) / 2 ≤
      rejectionRate hr H (fun x => encode r (ρ (eval x P)))
        (fun x => encode r (ρ (eval x M))) := by
  let a : (Fin m → F) → F × F := fun x => (eval (zeroPoint x) M, eval (recoveryPoint H x) M)
  let b : (Fin m → F) → F × F := fun x => (0, eval x P)
  have ha : acceptanceRate H P M = relativeAgreement a b := rfl
  have hbin : rejectionRate hr H (fun x => encode r (ρ (eval x P)))
      (fun x => encode r (ρ (eval x M))) = relativeDistance
      (fun s : (Fin m → F) × (Fin t → ZMod 2) =>
        (linearEncode (ρ (a s.1).1) s.2, linearEncode (ρ (a s.1).2) s.2))
      (fun s => (linearEncode (ρ (b s.1).1) s.2, linearEncode (ρ (b s.1).2) s.2)) := by
    simp only [rejectionRate, check, checkBits, encode_homogeneousIndex, a, b,
      linearEncode_zero, relativeDistance, hammingDist, ne_eq, Prod.mk.injEq, sub_eq_zero]
  rw [ha, relativeAgreement_eq_one_sub_relativeDistance, hbin, relativeDistance_prod]
  have hs := sum_le_sum (s := (univ : Finset (Fin m → F))) (g := fun x =>
      relativeDistance (fun w => (linearEncode (ρ (a x).1) w, linearEncode (ρ (a x).2) w))
        (fun w => (linearEncode (ρ (b x).1) w, linearEncode (ρ (b x).2) w)))
    (f := fun x => if a x = b x then (0 : ℚ) else 1 / 2) (fun x _ => by
      by_cases hx : a x = b x
      · simp only [hx, ↓reduceIte, relativeDistance_self, le_refl]
      · simpa only [hx, ↓reduceIte] using pair_distance_ge_half ρ (a x) (b x) hx)
  have hmean := div_le_div_of_nonneg_right hs
    (show (0 : ℚ) ≤ Fintype.card (Fin m → F) by positivity)
  have hid : (∑ x, if a x = b x then (0 : ℚ) else 1 / 2) =
      (hammingDist a b : ℚ) / 2 := by
    rw [hammingDist, natCast_card_filter]
    simp only [sum_div]
    apply sum_congr rfl
    intro x _
    by_cases hx : a x = b x <;> simp [hx]
  rw [hid] at hmean
  simpa only [relativeDistance, sub_sub_cancel, div_right_comm] using hmean

omit [DecidableEq F] in
/-- The actual polynomial-oracle rejection bound for the binary two-check verifier. -/
theorem rejectionRate_encode_ge_of_not_vanishesOn (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin m) F) (M : MvPolynomial (Fin m ⊕ Fin m) F)
    (hP : P.totalDegree ≤ d) (hM : M.totalDegree ≤ d) (hnot : ¬ VanishesOn H P) :
    (1 - ((d * H.card : ℕ) : ℚ) / Fintype.card F) / 2 ≤
      rejectionRate hr H (fun x => encode r (ρ (eval x P)))
        (fun x => encode r (ρ (eval x M))) := by
  classical
  have hf := acceptanceRate_le_of_not_vanishesOn H hH P M hP hM hnot
  have hb := rejectionRate_encode_ge_half_field hr ρ H P M
  linarith

omit [DecidableEq F] in
/-- A formal certificate has zero binary rejection. -/
theorem rejectionRate_encode_eq_zero (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) {H : Finset F}
    {P : MvPolynomial (Fin m) F} {M : MvPolynomial (Fin m ⊕ Fin m) F}
    (hM : IsCertificate H P M) :
    rejectionRate hr H (fun x => encode r (ρ (eval x P)))
      (fun x => encode r (ρ (eval x M))) = 0 := by
  simp only [rejectionRate, check_encode_eq_zero hr ρ hM, relativeDistance_self]

omit [DecidableEq F] in
/-- Every vanishing polynomial has an honestly encoded certificate of no larger degree. -/
theorem exists_rejectionRate_encode_eq_zero (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin m) F) (hP : VanishesOn H P) :
    ∃ M : MvPolynomial (Fin m ⊕ Fin m) F,
      M.totalDegree ≤ P.totalDegree ∧
        rejectionRate hr H (fun x => encode r (ρ (eval x P)))
          (fun x => encode r (ρ (eval x M))) = 0 := by
  classical
  obtain ⟨M, hdeg, hcert⟩ := (vanishesOn_iff_exists_certificate H hH P).mp hP
  exact ⟨M, hdeg, rejectionRate_encode_eq_zero hr ρ hcert⟩

end Finite
end PCP.Algebraic.BinaryZeroOnGrid
