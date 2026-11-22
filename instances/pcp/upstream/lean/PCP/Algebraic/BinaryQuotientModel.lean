/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryIrreduciblePolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Algebra

/-!
# The semantic quotient model of binary coefficient words

The computed irreducible polynomial of degree `t` defines a quotient field.
Its monic power basis identifies the quotient with exactly `t` binary coefficients:
the identification sends a word to the sum of its coefficients times successive
powers of the distinguished root. This is a semantic reference for separately
implemented coefficient arithmetic; the quotient field operations and the inverse
coordinate map here are not claimed to be executable.
-/

namespace PCP.Algebraic.BinaryQuotientModel

open Polynomial Module

abbrev Word (t : ℕ) := Fin t → ZMod 2

/-- The quotient by the computed monic irreducible polynomial. -/
abbrev Model (t : ℕ) (ht : 0 < t) :=
  AdjoinRoot (BinaryIrreduciblePolynomial.polynomial t ht)

instance polynomialIrreducible (t : ℕ) (ht : 0 < t) :
    Fact (Irreducible (BinaryIrreduciblePolynomial.polynomial t ht)) :=
  ⟨BinaryIrreduciblePolynomial.polynomial_irreducible t ht⟩

/-- The actual lower coefficients of the selected polynomial. -/
def lowerCoefficients (t : ℕ) (ht : 0 < t) : Word t :=
  (BinaryIrreduciblePolynomial.coefficientEquiv t).symm
    (BinaryIrreduciblePolynomial.selectedCode t ht)

theorem lowerCoefficients_apply (t : ℕ) (ht : 0 < t) (i : Fin t) :
    lowerCoefficients t ht i = (BinaryIrreduciblePolynomial.polynomial t ht).coeff i.val := by
  rw [BinaryIrreduciblePolynomial.polynomial_coeff]
  simp [lowerCoefficients, BinaryIrreduciblePolynomial.coefficient, i.isLt]

noncomputable section

/-- The residue class of the polynomial variable. -/
def root (t : ℕ) (ht : 0 < t) : Model t ht :=
  AdjoinRoot.root (BinaryIrreduciblePolynomial.polynomial t ht)

/-- The monic polynomial power basis, with its dimension rewritten to `t`. -/
def basis (t : ℕ) (ht : 0 < t) : Basis (Fin t) (ZMod 2) (Model t ht) :=
  (AdjoinRoot.powerBasis' (BinaryIrreduciblePolynomial.polynomial_monic t ht)).basis.reindex
    (finCongr (BinaryIrreduciblePolynomial.polynomial_natDegree t ht))

@[simp] theorem basis_apply (t : ℕ) (ht : 0 < t) (i : Fin t) :
    basis t ht i = root t ht ^ i.val := by
  rw [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Evaluation of the displayed coefficient word in the quotient model. -/
def toModel (t : ℕ) (ht : 0 < t) (v : Word t) : Model t ht :=
  ∑ i, algebraMap (ZMod 2) (Model t ht) (v i) * root t ht ^ i.val

/-- The coefficient equivalence uses the specific monic power basis. -/
def coefficientEquiv (t : ℕ) (ht : 0 < t) : Word t ≃ₗ[ZMod 2] Model t ht :=
  (basis t ht).equivFun.symm

@[simp] theorem coefficientEquiv_apply (t : ℕ) (ht : 0 < t) (v : Word t) :
    coefficientEquiv t ht v = toModel t ht v := by
  simp [coefficientEquiv, Basis.equivFun_symm_apply, toModel, Algebra.smul_def]

theorem toModel_bijective (t : ℕ) (ht : 0 < t) : Function.Bijective (toModel t ht) := by
  change Function.Bijective (fun v => toModel t ht v)
  simp_rw [← coefficientEquiv_apply]
  exact (coefficientEquiv t ht).bijective

theorem toModel_injective (t : ℕ) (ht : 0 < t) : Function.Injective (toModel t ht) :=
  (toModel_bijective t ht).1

theorem toModel_surjective (t : ℕ) (ht : 0 < t) : Function.Surjective (toModel t ht) :=
  (toModel_bijective t ht).2

instance instFintype (t : ℕ) (ht : 0 < t) : Fintype (Model t ht) :=
  Fintype.ofEquiv (Word t) (coefficientEquiv t ht).toEquiv

@[simp] theorem card_model (t : ℕ) (ht : 0 < t) : Fintype.card (Model t ht) = 2 ^ t := by
  rw [← Fintype.card_congr (coefficientEquiv t ht).toEquiv]
  simp [Word]

instance instCharP (t : ℕ) (ht : 0 < t) : CharP (Model t ht) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (Model t ht)).injective 2

/-- The relation used to reduce multiplication by the distinguished root. -/
theorem root_relation (t : ℕ) (ht : 0 < t) :
    root t ht ^ t + toModel t ht (lowerCoefficients t ht) = 0 := by
  have h := AdjoinRoot.eval₂_root (BinaryIrreduciblePolynomial.polynomial t ht)
  rw [Polynomial.eval₂_eq_sum_range,
    BinaryIrreduciblePolynomial.polynomial_natDegree, Finset.sum_range_succ] at h
  have hlead : (BinaryIrreduciblePolynomial.polynomial t ht).coeff t = 1 := by
    simpa using (BinaryIrreduciblePolynomial.polynomial_monic t ht).coeff_natDegree
  rw [toModel]
  simp_rw [lowerCoefficients_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    algebraMap (ZMod 2) (Model t ht) ((BinaryIrreduciblePolynomial.polynomial t ht).coeff i) *
      root t ht ^ i)]
  simpa [root,
    AdjoinRoot.algebraMap_eq, hlead, add_comm] using h

end

end PCP.Algebraic.BinaryQuotientModel
