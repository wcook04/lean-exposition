/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryDistance
import PCP.Algebraic.GridInterpolation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
# Multilinear representatives of binary polynomial functions

Replace each positive exponent by one and combine coefficients when monomials coincide.
This linear operation does not increase total degree and preserves evaluations on `𝔽₂`.
Together with binary evaluation injectivity, it gives a unique multilinear representative
of every binary polynomial function and transfers the distance bound to `IsLowDegree`.
-/

namespace PCP.Algebraic

open Finset MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Truncate every monomial exponent at one. -/
noncomputable def multilinearExponent (s : σ →₀ ℕ) : σ →₀ ℕ :=
  s.mapRange (fun n => min n 1) (by simp)

@[simp] theorem multilinearExponent_apply (s : σ →₀ ℕ) (i : σ) :
    multilinearExponent s i = min (s i) 1 := rfl

theorem multilinearExponent_eq_self {s : σ →₀ ℕ} (h : ∀ i, s i ≤ 1) :
    multilinearExponent s = s := by
  ext i
  exact min_eq_left (h i)

/-- Multilinear reduction as a linear map on coefficients. -/
noncomputable def multilinearReduction : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.mapDomainLinearMap R R multilinearExponent

@[simp] theorem multilinearReduction_monomial (s : σ →₀ ℕ) (a : R) :
    multilinearReduction (monomial s a) = monomial (multilinearExponent s) a := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem multilinearReduction_apply (p : MvPolynomial σ R) :
    multilinearReduction p = ∑ s ∈ p.support, monomial (multilinearExponent s) (p.coeff s) := by
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, multilinearReduction_monomial]

theorem multilinearReduction_isMultilinear (p : MvPolynomial σ R) :
    IsMultilinear (multilinearReduction p) := by
  classical
  intro i
  apply degreeOf_le_iff.mpr
  intro s hs
  change s ∈ ((AddMonoidAlgebra.coeff p).mapDomain multilinearExponent).support at hs
  obtain ⟨t, _, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support hs)
  exact min_le_right _ _

theorem totalDegree_multilinearReduction_le (p : MvPolynomial σ R) :
    (multilinearReduction p).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  change s ∈ ((AddMonoidAlgebra.coeff p).mapDomain multilinearExponent).support at hs
  obtain ⟨t, ht, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support hs)
  apply le_trans _ (le_totalDegree ht)
  rw [multilinearExponent, Finsupp.sum_mapRange_index (by simp)]
  exact Finset.sum_le_sum fun i _ => min_le_left _ _

theorem multilinearReduction_eq_self {p : MvPolynomial σ R} (hp : IsMultilinear p) :
    multilinearReduction p = p := by
  apply (AddMonoidAlgebra.coeffLinearEquiv R).injective
  change Finsupp.mapDomain multilinearExponent (AddMonoidAlgebra.coeff p) =
    AddMonoidAlgebra.coeff p
  refine (Finsupp.mapDomain_congr (f := multilinearExponent) (g := id) ?_).trans
    Finsupp.mapDomain_id
  intro s hs
  exact multilinearExponent_eq_self (fun i => (monomial_le_degreeOf i hs).trans (hp i))

@[simp] theorem multilinearReduction_idempotent (p : MvPolynomial σ R) :
    multilinearReduction (multilinearReduction p) = multilinearReduction p :=
  multilinearReduction_eq_self (multilinearReduction_isMultilinear p)

@[simp] theorem multilinearReduction_C (a : R) :
    multilinearReduction (C a : MvPolynomial σ R) = C a :=
  multilinearReduction_eq_self (fun i => by simp)

@[simp] theorem multilinearReduction_X_pow (i : σ) (n : ℕ) :
    multilinearReduction ((X i : MvPolynomial σ R) ^ n) = X i ^ min n 1 := by
  rw [X_pow_eq_monomial, multilinearReduction_monomial, X_pow_eq_monomial]
  simp [multilinearExponent, Finsupp.mapRange_single]

@[simp] theorem multilinearReduction_X (i : σ) :
    multilinearReduction (X i : MvPolynomial σ R) = X i := by
  simpa using multilinearReduction_X_pow (R := R) i 1

private theorem binary_pow_min_one (a : ZMod 2) (n : ℕ) : a ^ min n 1 = a ^ n := by
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> cases n <;> simp

/-- Reduction preserves the evaluation function on the Boolean cube. -/
@[simp] theorem eval_multilinearReduction (p : MvPolynomial σ (ZMod 2)) (x : σ → ZMod 2) :
    eval x (multilinearReduction p) = eval x p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial s a =>
      rw [multilinearReduction_monomial, eval_monomial, eval_monomial]
      congr 1
      rw [multilinearExponent, Finsupp.prod_mapRange_index (by simp)]
      apply Finset.prod_congr rfl
      intro i _
      exact binary_pow_min_one _ _

variable {m d : ℕ}

/-- Binary polynomial functions have a unique multilinear representative, of no larger degree. -/
theorem existsUnique_multilinear_representative (p : MvPolynomial (Fin m) (ZMod 2)) :
    ∃! q : MvPolynomial (Fin m) (ZMod 2), IsMultilinear q ∧
      q.totalDegree ≤ p.totalDegree ∧ ∀ x, eval x q = eval x p := by
  refine ⟨multilinearReduction p,
    ⟨multilinearReduction_isMultilinear p, totalDegree_multilinearReduction_le p,
      eval_multilinearReduction p⟩, ?_⟩
  intro q hq
  apply binary_eval_injective hq.1 (multilinearReduction_isMultilinear p)
  funext x
  change eval x q = eval x (multilinearReduction p)
  rw [hq.2.2, eval_multilinearReduction]

theorem isLowDegree_iff_exists_multilinear {f : (Fin m → ZMod 2) → ZMod 2} :
    IsLowDegree d f ↔ ∃ p : MvPolynomial (Fin m) (ZMod 2),
      IsMultilinear p ∧ p.totalDegree ≤ d ∧ (fun x => eval x p) = f := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨multilinearReduction p, multilinearReduction_isMultilinear p,
      (totalDegree_multilinearReduction_le p).trans hp, funext (eval_multilinearReduction p)⟩
  · rintro ⟨p, _, hp, rfl⟩
    exact isLowDegree_eval p hp

/-- The binary distance bound for the paper's space of polynomial functions. -/
theorem IsLowDegree.binary_relativeDistance_ge {f g : (Fin m → ZMod 2) → ZMod 2}
    (hf : IsLowDegree d f) (hg : IsLowDegree d g) (hne : f ≠ g) :
    (1 : ℚ) / 2 ^ d ≤ relativeDistance f g := by
  obtain ⟨p, hp, hpdeg, rfl⟩ := isLowDegree_iff_exists_multilinear.mp hf
  obtain ⟨q, hq, hqdeg, rfl⟩ := isLowDegree_iff_exists_multilinear.mp hg
  exact binary_eval_distance_ge p q hp hq hpdeg hqdeg (fun h => hne (h ▸ rfl))

theorem IsLowDegree.binary_eq_of_close {f g w : (Fin m → ZMod 2) → ZMod 2} {ε : ℚ}
    (hf : IsLowDegree d f) (hg : IsLowDegree d g)
    (hradius : 2 * ε < (1 : ℚ) / 2 ^ d)
    (hwf : relativeDistance w f ≤ ε) (hwg : relativeDistance w g ≤ ε) : f = g :=
  eq_of_relativeDistance_le_of_separated
    (C := {f | IsLowDegree d f})
    (fun _ hf _ hg hne => hf.binary_relativeDistance_ge hg hne) hradius hf hg hwf hwg

/-- The canonical multilinear representative of a Boolean-cube function. -/
noncomputable def binaryRepresentative (m : ℕ) :
    ((Fin m → ZMod 2) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin m) (ZMod 2) :=
  (GridInterpolation.interpolate (σ := Fin m) (univ : Finset (ZMod 2))).comp
    (LinearMap.pi fun a : Fin m → (univ : Finset (ZMod 2)) =>
      LinearMap.proj (fun i => (a i : ZMod 2)))

theorem binaryRepresentative_apply (f : (Fin m → ZMod 2) → ZMod 2) :
    binaryRepresentative m f = GridInterpolation.interpolate (univ : Finset (ZMod 2))
      (fun a : Fin m → (univ : Finset (ZMod 2)) => f (fun i => (a i : ZMod 2))) := rfl

theorem binaryRepresentative_isMultilinear (f : (Fin m → ZMod 2) → ZMod 2) :
    IsMultilinear (binaryRepresentative m f) := by
  intro i
  rw [binaryRepresentative_apply]
  simpa using GridInterpolation.degreeOf_interpolate_le (univ : Finset (ZMod 2)) _ i

@[simp] theorem eval_binaryRepresentative (f : (Fin m → ZMod 2) → ZMod 2)
    (x : Fin m → ZMod 2) : eval x (binaryRepresentative m f) = f x := by
  exact GridInterpolation.eval_interpolate (univ : Finset (ZMod 2)) _
    (fun i => ⟨x i, mem_univ _⟩)

theorem totalDegree_binaryRepresentative_le (f : (Fin m → ZMod 2) → ZMod 2) :
    (binaryRepresentative m f).totalDegree ≤ m := by
  rw [binaryRepresentative_apply]
  simpa using GridInterpolation.totalDegree_interpolate_le (σ := Fin m)
    (univ : Finset (ZMod 2)) (fun a => f (fun i => (a i : ZMod 2)))

/-- The representative from a table equals monomial reduction of any representing polynomial. -/
theorem binaryRepresentative_eval (p : MvPolynomial (Fin m) (ZMod 2)) :
    binaryRepresentative m (fun x => eval x p) = multilinearReduction p := by
  apply binary_eval_injective (binaryRepresentative_isMultilinear _)
    (multilinearReduction_isMultilinear p)
  funext x
  exact (eval_binaryRepresentative _ x).trans (eval_multilinearReduction p x).symm

/-- The canonical representative preserves the degree filtration of polynomial functions. -/
theorem binaryRepresentative_degree_le_iff (f : (Fin m → ZMod 2) → ZMod 2) :
    (binaryRepresentative m f).totalDegree ≤ d ↔ IsLowDegree d f := by
  constructor
  · intro h
    exact ⟨binaryRepresentative m f, h, funext (eval_binaryRepresentative f)⟩
  · rintro ⟨p, hp, rfl⟩
    rw [binaryRepresentative_eval]
    exact (totalDegree_multilinearReduction_le p).trans hp

theorem existsUnique_binary_multilinear (f : (Fin m → ZMod 2) → ZMod 2) :
    ∃! p : MvPolynomial (Fin m) (ZMod 2), IsMultilinear p ∧ ∀ x, eval x p = f x := by
  refine ⟨binaryRepresentative m f,
    ⟨binaryRepresentative_isMultilinear f, eval_binaryRepresentative f⟩, ?_⟩
  intro p hp
  apply binary_eval_injective hp.1 (binaryRepresentative_isMultilinear f)
  funext x
  exact (hp.2 x).trans (eval_binaryRepresentative f x).symm

end PCP.Algebraic
