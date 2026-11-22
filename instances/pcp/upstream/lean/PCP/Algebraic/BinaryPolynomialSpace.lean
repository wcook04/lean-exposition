/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.MultilinearReduction
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite coefficient coordinates for low-degree binary polynomials

The coordinate set for Definition 3.5 consists of subsets of the variables of
size at most `r`. Coefficient vectors therefore describe multilinear polynomials.
This realizes the paper's length `2 ^ (∑ k ≤ r, t.choose k)` and distinguishes
formal reduced representatives from arbitrary expressions with the same evaluations.
-/

namespace PCP.Algebraic.BinaryPolynomialSpace

open Finset MvPolynomial

/-- Squarefree monomials of total degree at most `r` in `t` variables. -/
abbrev Monomials (t r : ℕ) := {s : Finset (Fin t) // s.card ≤ r}

/-- A finite binary coefficient vector, including the coefficient of the empty monomial. -/
abbrev Coefficients (t r : ℕ) := Monomials t r → ZMod 2

variable {t r : ℕ}

/-- The exponent vector of a squarefree monomial. -/
noncomputable def exponent (s : Finset (Fin t)) : Fin t →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

@[simp] theorem exponent_apply (s : Finset (Fin t)) (i : Fin t) :
    exponent s i = if i ∈ s then 1 else 0 := by
  simp [exponent]

@[simp] theorem support_exponent (s : Finset (Fin t)) : (exponent s).support = s := by
  ext i
  simp [Finsupp.mem_support_iff]

theorem exponent_injective : Function.Injective (exponent (t := t)) := by
  intro s u h
  simpa using congrArg Finsupp.support h

@[simp] theorem exponent_singleton (i : Fin t) : exponent {i} = Finsupp.single i 1 := by
  simp [exponent, Finsupp.indicator_singleton]

theorem sum_exponent (s : Finset (Fin t)) : (exponent s).sum (fun _ n => n) = s.card := by
  simp [Finsupp.sum]

theorem exponent_support_eq (s : Fin t →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    exponent s.support = s := by
  ext i
  by_cases hi : s i = 0
  · simp [hi, Finsupp.mem_support_iff]
  · have hsi : s i = 1 := by have := hs i; omega
    simp [Finsupp.mem_support_iff, hsi]

/-- Convert coefficient coordinates into a formal multilinear polynomial. -/
noncomputable def polynomial (t r : ℕ) :
    Coefficients t r →ₗ[ZMod 2] MvPolynomial (Fin t) (ZMod 2) :=
  ∑ s : Monomials t r, (monomial (exponent s.val)).comp (LinearMap.proj s)

theorem polynomial_apply (c : Coefficients t r) :
    polynomial t r c = ∑ s : Monomials t r, monomial (exponent s.val) (c s) := by
  simp [polynomial]

@[simp] theorem polynomial_single (s : Monomials t r) (a : ZMod 2) :
    polynomial t r (Pi.single s a) = monomial (exponent s.val) a := by
  classical
  rw [polynomial_apply]
  simp [Pi.single_apply, apply_ite]

@[simp] theorem coeff_polynomial (c : Coefficients t r) (s : Monomials t r) :
    (polynomial t r c).coeff (exponent s.val) = c s := by
  classical
  rw [polynomial_apply, coeff_sum]
  simp [coeff_monomial, exponent_injective.eq_iff, Subtype.val_inj]

theorem polynomial_injective : Function.Injective (polynomial t r) := by
  intro c d h
  funext s
  simpa using congrArg (fun p => p.coeff (exponent s.val)) h

theorem polynomial_isMultilinear (c : Coefficients t r) : IsMultilinear (polynomial t r c) := by
  classical
  intro i
  rw [polynomial_apply]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro s _
  by_cases hc : c s = 0
  · simp [hc]
  · rw [degreeOf_monomial_eq _ _ hc, exponent_apply]
    split_ifs <;> omega

theorem totalDegree_polynomial_le (c : Coefficients t r) : (polynomial t r c).totalDegree ≤ r := by
  rw [polynomial_apply]
  apply totalDegree_finsetSum_le
  intro s _
  exact (totalDegree_monomial_le _ _).trans
    (by simpa only [Function.id_def, sum_exponent] using s.property)

/-- Read a polynomial's squarefree coefficients. -/
noncomputable def coefficients (p : MvPolynomial (Fin t) (ZMod 2)) : Coefficients t r :=
  fun s => p.coeff (exponent s.val)

@[simp] theorem coefficients_polynomial (c : Coefficients t r) :
    coefficients (polynomial t r c) = c := by
  funext s
  exact coeff_polynomial c s

/-- The coefficient representation recovers every bounded multilinear polynomial. -/
theorem polynomial_coefficients (p : MvPolynomial (Fin t) (ZMod 2))
    (hp : IsMultilinear p) (hdeg : p.totalDegree ≤ r) : polynomial t r (coefficients p) = p := by
  classical
  ext s
  by_cases hs : s ∈ p.support
  · have hexp : exponent s.support = s :=
      exponent_support_eq s (fun i => (monomial_le_degreeOf i hs).trans (hp i))
    have hcard : s.support.card ≤ r := by
      rw [← sum_exponent s.support, hexp]
      exact (le_totalDegree hs).trans hdeg
    simpa [hexp, coefficients] using coeff_polynomial (coefficients (r := r) p)
      (⟨s.support, hcard⟩ : Monomials t r)
  · have hz : p.coeff s = 0 := notMem_support_iff.mp hs
    rw [hz, polynomial_apply, coeff_sum]
    apply sum_eq_zero
    intro u _
    by_cases hu : exponent u.val = s
    · simp [hu, coefficients, hz]
    · simp [coeff_monomial, hu]

/-- Bounded reduced polynomials and coefficient vectors are equivalent. -/
noncomputable def polynomialEquiv (t r : ℕ) :
    Coefficients t r ≃ {p : MvPolynomial (Fin t) (ZMod 2) //
      IsMultilinear p ∧ p.totalDegree ≤ r} where
  toFun c := ⟨polynomial t r c, polynomial_isMultilinear c, totalDegree_polynomial_le c⟩
  invFun p := coefficients p.val
  left_inv := coefficients_polynomial
  right_inv p := Subtype.ext (polynomial_coefficients p.val p.property.1 p.property.2)

/-- Evaluation at one Boolean point is linear in the coefficient vector. -/
noncomputable def evaluate (x : Fin t → ZMod 2) : Coefficients t r →ₗ[ZMod 2] ZMod 2 where
  toFun c := eval x (polynomial t r c)
  map_add' c d := by simp
  map_smul' a c := by simp [MvPolynomial.smul_eq_C_mul]

theorem evaluate_apply (x : Fin t → ZMod 2) (c : Coefficients t r) :
    evaluate x c = eval x (polynomial t r c) := rfl

/-- Reduce an arbitrary degree-bounded expression before reading its squarefree coordinates. -/
theorem evaluate_reduced_coefficients (p : MvPolynomial (Fin t) (ZMod 2))
    (hp : p.totalDegree ≤ r) (x : Fin t → ZMod 2) :
    evaluate x (coefficients (r := r) (multilinearReduction p)) = eval x p := by
  rw [evaluate_apply, polynomial_coefficients _ (multilinearReduction_isMultilinear p)
    ((totalDegree_multilinearReduction_le p).trans hp), eval_multilinearReduction]

theorem evaluate_single (x : Fin t → ZMod 2) (s : Monomials t r) (a : ZMod 2) :
    evaluate x (Pi.single s a) = a * ∏ i ∈ s.val, x i := by
  rw [evaluate_apply, polynomial_single, eval_monomial, Finsupp.prod, support_exponent]
  congr 1
  apply prod_congr rfl
  intro i hi
  simp [hi]

/-- The constant polynomial, stored in the empty-monomial coordinate. -/
noncomputable def constant (a : ZMod 2) : Coefficients t r :=
  Pi.single ⟨∅, by simp⟩ a

@[simp] theorem evaluate_constant (x : Fin t → ZMod 2) (a : ZMod 2) :
    evaluate x (constant (t := t) (r := r) a) = a := by
  simp [constant, evaluate_single]

/-- A coordinate function is available whenever the degree bound is positive. -/
noncomputable def variableCoeff (hr : 1 ≤ r) (i : Fin t) : Coefficients t r :=
  Pi.single ⟨{i}, by simpa using hr⟩ 1

@[simp] theorem polynomial_variableCoeff (hr : 1 ≤ r) (i : Fin t) :
    polynomial t r (variableCoeff hr i) = X i := by
  simp [variableCoeff, X]

@[simp] theorem evaluate_variableCoeff (x : Fin t → ZMod 2) (hr : 1 ≤ r) (i : Fin t) :
    evaluate x (variableCoeff hr i) = x i := by
  simp [variableCoeff, evaluate_single]

theorem evaluation_injective : Function.Injective
    (fun c : Coefficients t r => fun x => evaluate x c) := by
  intro c d h
  apply polynomial_injective
  exact binary_eval_injective (polynomial_isMultilinear c) (polynomial_isMultilinear d) h

/-- Coefficient vectors represent exactly the binary functions of degree at most `r`. -/
theorem isLowDegree_iff (f : (Fin t → ZMod 2) → ZMod 2) :
    IsLowDegree r f ↔ ∃ c : Coefficients t r, (fun x => evaluate x c) = f := by
  constructor
  · intro hf
    refine ⟨coefficients (binaryRepresentative t f), ?_⟩
    funext x
    rw [evaluate_apply, polynomial_coefficients _ (binaryRepresentative_isMultilinear f)
      ((binaryRepresentative_degree_le_iff f).mpr hf), eval_binaryRepresentative]
  · rintro ⟨c, rfl⟩
    exact isLowDegree_eval _ (totalDegree_polynomial_le c)

/-- The finite coefficient space indexes the low-degree polynomial functions without duplicates. -/
noncomputable def functionEquiv (t r : ℕ) :
    Coefficients t r ≃ {f : (Fin t → ZMod 2) → ZMod 2 // IsLowDegree r f} :=
  Equiv.ofBijective
    (fun c => ⟨fun x => evaluate x c, isLowDegree_eval _ (totalDegree_polynomial_le c)⟩)
    ⟨fun _ _ h => evaluation_injective (congrArg Subtype.val h), by
      rintro ⟨f, hf⟩
      obtain ⟨c, hc⟩ := (isLowDegree_iff f).mp hf
      exact ⟨c, Subtype.ext hc⟩⟩

/-- The number of squarefree monomials of degree at most `r`, including degree zero. -/
theorem card_monomials (t r : ℕ) :
    Fintype.card (Monomials t r) = ∑ k ∈ range (r + 1), t.choose k := by
  classical
  rw [Fintype.card_subtype]
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Finset (Fin t)))
    (range (r + 1)) Finset.card
  simp only [mem_range, Nat.lt_succ_iff] at h
  rw [← h]
  apply sum_congr rfl
  intro k _
  have hs : (univ.filter fun s : Finset (Fin t) => s.card = k) =
      (univ : Finset (Fin t)).powersetCard k := by
    ext s
    simp
  rw [hs, card_powersetCard]
  simp

/-- The coordinate count, and hence code length, in Definition 3.5. -/
theorem card_coefficients (t r : ℕ) :
    Fintype.card (Coefficients t r) = 2 ^ (∑ k ∈ range (r + 1), t.choose k) := by
  simp [card_monomials]

/-- The same cardinality holds for the paper's space of low-degree polynomial functions. -/
theorem card_lowDegree_functions (t r : ℕ) :
    Nat.card {f : (Fin t → ZMod 2) → ZMod 2 // IsLowDegree r f} =
      2 ^ (∑ k ∈ range (r + 1), t.choose k) := by
  rw [← Nat.card_congr (functionEquiv t r), Nat.card_eq_fintype_card, card_coefficients]

end PCP.Algebraic.BinaryPolynomialSpace
