/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Error-locator algebra for Berlekamp–Welch decoding

This generalizes the algebra in Arora–Safra, §5.2, Lemma 5.2.5, from `10h`
distinct nodes with at most `2h` errors to any finite set of distinct nodes.
The locator is an explicit product over the actual error positions. It is monic,
has exactly as many degrees as errors, and gives a nontrivial solution to the
received-word equations when multiplied by the genuine polynomial.

With sufficiently many agreements, every degree-bounded solution satisfies the
formal identity `N = s * E`. Polynomial division therefore recovers `s` when
`E ≠ 0`. The zero solution is retained in the identity theorem and explicitly
excluded when asserting quotient recovery. No decoding algorithm or running-time
bound is claimed, and the field itself need not be finite.

Source: https://www.cs.umd.edu/users/gasarch/TOPICS/pcp/AS.pdf, printed pp. 109–110.
-/

namespace PCP.Algebraic.BerlekampWelch

open Finset Polynomial

variable {F ι : Type*} [Field F] {d e : ℕ}

/-- The homogeneous equations in the error locator `E` and numerator `N`. -/
def Equations (a w : ι → F) (E N : Polynomial F) : Prop :=
  ∀ i, N.eval (a i) = w i * E.eval (a i)

variable [Fintype ι]

/-- Positions where the received word differs from the specified genuine polynomial. -/
noncomputable def errors (a w : ι → F) (s : Polynomial F) : Finset ι := by
  classical
  exact univ.filter (fun i => s.eval (a i) ≠ w i)

/-- Positions of agreement with the specified genuine polynomial. -/
noncomputable def agreements (a w : ι → F) (s : Polynomial F) : Finset ι := by
  classical
  exact univ.filter (fun i => s.eval (a i) = w i)

@[simp] theorem mem_errors (a w : ι → F) (s : Polynomial F) (i : ι) :
    i ∈ errors a w s ↔ s.eval (a i) ≠ w i := by
  classical
  simp [errors]

@[simp] theorem mem_agreements (a w : ι → F) (s : Polynomial F) (i : ι) :
    i ∈ agreements a w s ↔ s.eval (a i) = w i := by
  classical
  simp [agreements]

theorem agreements_card_add_errors_card (a w : ι → F) (s : Polynomial F) :
    (agreements a w s).card + (errors a w s).card = Fintype.card ι := by
  classical
  exact card_filter_add_card_filter_not (s := univ) (fun i => s.eval (a i) = w i)

/-- The explicit monic polynomial vanishing at all error positions; it is one if there are none. -/
noncomputable def errorLocator (a w : ι → F) (s : Polynomial F) : Polynomial F :=
  ∏ i ∈ errors a w s, (X - C (a i))

theorem errorLocator_monic (a w : ι → F) (s : Polynomial F) :
    (errorLocator a w s).Monic :=
  monic_prod_X_sub_C a (errors a w s)

theorem errorLocator_ne_zero (a w : ι → F) (s : Polynomial F) :
    errorLocator a w s ≠ 0 := (errorLocator_monic a w s).ne_zero

/-- Its exact degree counts erroneous positions, even without assuming node distinctness. -/
theorem natDegree_errorLocator (a w : ι → F) (s : Polynomial F) :
    (errorLocator a w s).natDegree = (errors a w s).card := by
  rw [errorLocator, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem eval_errorLocator_eq_zero_of_error (a w : ι → F) (s : Polynomial F)
    (i : ι) (hi : s.eval (a i) ≠ w i) : (errorLocator a w s).eval (a i) = 0 := by
  classical
  rw [errorLocator, eval_prod]
  apply prod_eq_zero (mem_errors a w s i |>.mpr hi)
  simp

/-- Multiplying the genuine polynomial by its error locator solves every received-word equation. -/
theorem errorLocator_equations (a w : ι → F) (s : Polynomial F) :
    Equations a w (errorLocator a w s) (s * errorLocator a w s) := by
  intro i
  by_cases hi : s.eval (a i) = w i
  · simp only [eval_mul, hi]
  · simp only [eval_mul, eval_errorLocator_eq_zero_of_error a w s i hi, mul_zero]

/-- Explicit existence of a nonzero-locator solution when at most `e` positions are corrupted. -/
theorem exists_solution (a w : ι → F) (s : Polynomial F) (hs : s.natDegree ≤ d)
    (herr : (errors a w s).card ≤ e) :
    ∃ E N : Polynomial F, E ≠ 0 ∧ E.natDegree ≤ e ∧ N.natDegree ≤ d + e ∧
      Equations a w E N := by
  have hE : (errorLocator a w s).natDegree ≤ e :=
    (natDegree_errorLocator a w s).trans_le herr
  exact ⟨errorLocator a w s, s * errorLocator a w s, errorLocator_ne_zero a w s, hE,
    natDegree_mul_le.trans (Nat.add_le_add hs hE), errorLocator_equations a w s⟩

/-- Enough distinct agreement nodes force every bounded solution to represent the same ratio. -/
theorem numerator_eq_mul_of_agreements (a w : ι → F) (ha : Function.Injective a)
    (s E N : Polynomial F) (hs : s.natDegree ≤ d) (hE : E.natDegree ≤ e)
    (hN : N.natDegree ≤ d + e) (heq : Equations a w E N)
    (hag : d + e < (agreements a w s).card) : N = s * E := by
  classical
  apply eq_of_natDegree_lt_card_of_eval_eq N (s * E)
    (f := fun i : {i // i ∈ agreements a w s} => a i)
    (ha.comp Subtype.val_injective)
  · intro i
    rw [heq i, eval_mul, (mem_agreements a w s i).mp i.property]
  · have hdeg : max N.natDegree (s * E).natDegree ≤ d + e :=
      max_le hN (natDegree_mul_le.trans (Nat.add_le_add hs hE))
    exact hdeg.trans_lt (by simpa only [Fintype.card_coe] using hag)

/-- The usual node-count condition implies the required strict agreement count. -/
theorem numerator_eq_mul_of_error_bound (a w : ι → F) (ha : Function.Injective a)
    (s E N : Polynomial F) (hs : s.natDegree ≤ d) (hE : E.natDegree ≤ e)
    (hN : N.natDegree ≤ d + e) (heq : Equations a w E N)
    (herr : (errors a w s).card ≤ e) (hcard : d + 2 * e < Fintype.card ι) : N = s * E := by
  apply numerator_eq_mul_of_agreements a w ha s E N hs hE hN heq
  have hpartition := agreements_card_add_errors_card a w s
  omega

/-- The locator divides the numerator, including the trivial zero solution. -/
theorem locator_dvd_numerator (a w : ι → F) (ha : Function.Injective a)
    (s E N : Polynomial F) (hs : s.natDegree ≤ d) (hE : E.natDegree ≤ e)
    (hN : N.natDegree ≤ d + e) (heq : Equations a w E N)
    (hag : d + e < (agreements a w s).card) : E ∣ N := by
  rw [numerator_eq_mul_of_agreements a w ha s E N hs hE hN heq hag]
  exact dvd_mul_left E s

/-- Every nonzero-locator solution recovers the genuine polynomial by exact polynomial division. -/
theorem quotient_eq_of_agreements (a w : ι → F) (ha : Function.Injective a)
    (s E N : Polynomial F) (hs : s.natDegree ≤ d) (hE : E.natDegree ≤ e)
    (hN : N.natDegree ≤ d + e) (heq : Equations a w E N)
    (hag : d + e < (agreements a w s).card) (hE0 : E ≠ 0) : N / E = s := by
  rw [numerator_eq_mul_of_agreements a w ha s E N hs hE hN heq hag]
  exact mul_div_cancel_right₀ s hE0

/-- A nontrivial solution cannot have zero locator once the number of distinct
nodes exceeds the numerator's degree bound. No genuine polynomial is needed here. -/
theorem locator_ne_zero_of_nontrivial (a w : ι → F) (ha : Function.Injective a)
    (E N : Polynomial F) (hN : N.natDegree ≤ d + e) (heq : Equations a w E N)
    (hcard : d + e < Fintype.card ι) (hne : (E, N) ≠ (0, 0)) : E ≠ 0 := by
  intro hE
  have hN0 : N = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero N ha
    (fun i => by simpa only [hE, eval_zero, mul_zero] using heq i) (hN.trans_lt hcard)
  exact hne (by simp only [hE, hN0])

end PCP.Algebraic.BerlekampWelch
