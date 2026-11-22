/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

/-!
# A uniform finite search for binary irreducible polynomials

Monic degree-`t` polynomials are enumerated by the `2^t` binary words of their
lower coefficients. Irreducibility is checked by explicit coefficient convolution
against all monic factor pairs of positive degrees adding to `t`. For every positive `t`,
the least successful numeric word gives an actual monic irreducible polynomial
of degree `t`.

The finite-field primitive element theorem proves that the search succeeds; no
primitive element or minimal polynomial is chosen in the computed result.
This module makes no running-time assertion about the exhaustive search.
-/

namespace PCP.Algebraic.BinaryIrreduciblePolynomial

open Polynomial

/-- Explicit binary digits, in the base-two order used by `finFunctionFinEquiv`. -/
def coefficientEquiv (t : ℕ) : (Fin t → ZMod 2) ≃ Fin (2 ^ t) :=
  (Equiv.arrowCongr (Equiv.refl (Fin t)) (ZMod.finEquiv 2).toEquiv.symm).trans
    (@finFunctionFinEquiv 2 t)

/-- Extend the lower coefficient word by the monic leading coefficient and zeroes. -/
def coefficient (t : ℕ) (i : Fin (2 ^ t)) (k : ℕ) : ZMod 2 :=
  if hk : k < t then (coefficientEquiv t).symm i ⟨k, hk⟩ else if k = t then 1 else 0

/-- The polynomial at one explicit finite address, using `ofFn`'s coefficient
constructor directly to avoid passing its noncomputable polynomial-module instance. -/
def candidate (t : ℕ) (i : Fin (2 ^ t)) : (ZMod 2)[X] :=
  ⟨.ofCoeff (List.ofFn (fun k : Fin (t + 1) => coefficient t i k.val)).toFinsupp⟩

@[simp] theorem candidate_coeff (t : ℕ) (i : Fin (2 ^ t)) (k : ℕ) :
    (candidate t i).coeff k = coefficient t i k := by
  by_cases hk : k < t + 1
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hk
  · change (Polynomial.ofFn (t + 1) (fun k => coefficient t i k.val)).coeff k = _
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    simp [coefficient, show ¬ k < t by omega, show k ≠ t by omega]

@[simp] theorem candidate_natDegree (t : ℕ) (i : Fin (2 ^ t)) :
    (candidate t i).natDegree = t := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  · simp [coefficient]

theorem candidate_monic (t : ℕ) (i : Fin (2 ^ t)) : (candidate t i).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, candidate_natDegree, candidate_coeff]
  simp [coefficient]

/-- Enumeration contains every monic polynomial of the prescribed degree. -/
theorem exists_candidate {t : ℕ} {p : (ZMod 2)[X]} (hp : p.Monic)
    (hdeg : p.natDegree = t) : ∃ i, candidate t i = p := by
  refine ⟨coefficientEquiv t (fun k => p.coeff k.val), ?_⟩
  ext k
  rw [candidate_coeff]
  by_cases hk : k < t
  · simp [coefficient, hk]
  · by_cases hkt : k = t
    · subst k
      simp [coefficient, ← hdeg, hp.coeff_natDegree]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [coefficient, hk, hkt]

/-- Multiplication on coefficient words uses only finite sums in `ZMod 2`. -/
def ProductMatches (t : ℕ) (i : Fin (2 ^ t)) (d : ℕ)
    (j : Fin (2 ^ d)) (k : Fin (2 ^ (t - d))) : Prop :=
  ∀ n : Fin (t + 1),
    (∑ ab ∈ Finset.antidiagonal n.val,
      coefficient d j ab.1 * coefficient (t - d) k ab.2) = coefficient t i n.val

instance (t : ℕ) (i : Fin (2 ^ t)) (d : ℕ) (j : Fin (2 ^ d))
    (k : Fin (2 ^ (t - d))) : Decidable (ProductMatches t i d j k) := by
  unfold ProductMatches
  infer_instance

/-- The finite convolution is exactly polynomial multiplication. -/
theorem productMatches_iff (t : ℕ) (i : Fin (2 ^ t)) (d : ℕ) (hd : d ≤ t)
    (j : Fin (2 ^ d)) (k : Fin (2 ^ (t - d))) :
    ProductMatches t i d j k ↔ candidate d j * candidate (t - d) k = candidate t i := by
  constructor
  · intro h
    ext n
    by_cases hn : n < t + 1
    · simpa [Polynomial.coeff_mul] using h ⟨n, hn⟩
    · have hprod : (candidate d j * candidate (t - d) k).natDegree = t := by
        rw [(candidate_monic d j).natDegree_mul (candidate_monic (t - d) k),
          candidate_natDegree, candidate_natDegree, Nat.add_sub_of_le hd]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simp; omega)]
  · intro h n
    have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff n.val) h
    simpa [Polynomial.coeff_mul] using hc

/-- A finite test excluding all monic factorizations of positive degrees. -/
def Passes (t : ℕ) (i : Fin (2 ^ t)) : Prop :=
  0 < t ∧ ∀ d : Fin (t + 1), 0 < d.val → d.val < t →
    ∀ j : Fin (2 ^ d.val), ∀ k : Fin (2 ^ (t - d.val)), ¬ ProductMatches t i d.val j k

instance (t : ℕ) (i : Fin (2 ^ t)) : Decidable (Passes t i) := by
  unfold Passes
  infer_instance

/-- The test is exactly irreducibility, including the degree-zero boundary. -/
theorem passes_iff_irreducible (t : ℕ) (i : Fin (2 ^ t)) :
    Passes t i ↔ Irreducible (candidate t i) := by
  have hm := candidate_monic t i
  by_cases ht : 0 < t
  · have hp1 : candidate t i ≠ 1 := by
      intro h
      have := candidate_natDegree t i
      rw [h, natDegree_one] at this
      omega
    rw [hm.irreducible_iff_natDegree]
    constructor
    · rintro ⟨_, h⟩
      refine ⟨hp1, fun f g hf hg hfg => ?_⟩
      by_contra hn
      have hfpos : 0 < f.natDegree := by omega
      have hgpos : 0 < g.natDegree := by omega
      have hsum : f.natDegree + g.natDegree = t := by
        rw [← hf.natDegree_mul hg, hfg, candidate_natDegree]
      have hflt : f.natDegree < t := by omega
      obtain ⟨j, hj⟩ := exists_candidate hf rfl
      have hdeg : g.natDegree = t - f.natDegree := by omega
      obtain ⟨k, hk⟩ := exists_candidate hg hdeg
      apply h ⟨f.natDegree, Nat.lt_succ_of_lt hflt⟩ hfpos hflt j k
      apply (productMatches_iff t i f.natDegree (by omega) j k).mpr
      rw [hj, hk, hfg]
    · rintro ⟨_, h⟩
      refine ⟨ht, fun d hd hdt j k hmatch => ?_⟩
      have hp := (productMatches_iff t i d.val (by omega) j k).mp hmatch
      have hz := h _ _ (candidate_monic _ _) (candidate_monic _ _) hp
      simp only [candidate_natDegree] at hz
      omega
  · have hzero : t = 0 := Nat.eq_zero_of_not_pos ht
    have hp : candidate t i = 1 := hm.natDegree_eq_zero.mp (by simpa using hzero)
    simp [Passes, ht, hp]

/-- Existence comes from a primitive element of the finite degree-`t` extension.
The extension and its primitive element occur only in this proof. -/
theorem exists_monic_irreducible (t : ℕ) (ht : 0 < t) :
    ∃ p : (ZMod 2)[X], p.Monic ∧ Irreducible p ∧ p.natDegree = t := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 t)
  have hi : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hi, minpoly.irreducible hi, ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα).trans
    (GaloisField.finrank 2 ht.ne')

/-- The finite, explicitly decidable set of successful numeric words. -/
def goodCodes (t : ℕ) : Finset (Fin (2 ^ t)) := Finset.univ.filter (Passes t)

theorem goodCodes_nonempty (t : ℕ) (ht : 0 < t) : (goodCodes t).Nonempty := by
  obtain ⟨p, hp, hirr, hdeg⟩ := exists_monic_irreducible t ht
  obtain ⟨i, rfl⟩ := exists_candidate hp hdeg
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (passes_iff_irreducible t i).mpr hirr⟩⟩

/-- Choose the least successful word by finite computation, not by choice. -/
def selectedCode (t : ℕ) (ht : 0 < t) : Fin (2 ^ t) :=
  (goodCodes t).min' (goodCodes_nonempty t ht)

theorem selectedCode_passes (t : ℕ) (ht : 0 < t) : Passes t (selectedCode t ht) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (goodCodes_nonempty t ht))).2

/-- The choice is pinned down by numeric order, not merely by existence. -/
theorem selectedCode_le {t : ℕ} (ht : 0 < t) (i : Fin (2 ^ t)) (hi : Passes t i) :
    selectedCode t ht ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- The actual uniform binary irreducible-polynomial selector. -/
def polynomial (t : ℕ) (ht : 0 < t) : (ZMod 2)[X] := candidate t (selectedCode t ht)

theorem polynomial_monic (t : ℕ) (ht : 0 < t) : (polynomial t ht).Monic :=
  candidate_monic t _

@[simp] theorem polynomial_natDegree (t : ℕ) (ht : 0 < t) :
    (polynomial t ht).natDegree = t := candidate_natDegree t _

theorem polynomial_irreducible (t : ℕ) (ht : 0 < t) : Irreducible (polynomial t ht) := by
  apply (passes_iff_irreducible t (selectedCode t ht)).mp
  exact selectedCode_passes t ht

/-- The computed bits are the actual coefficients of the selected polynomial. -/
theorem polynomial_coeff (t : ℕ) (ht : 0 < t) (k : ℕ) :
    (polynomial t ht).coeff k = coefficient t (selectedCode t ht) k :=
  candidate_coeff t _ k

end PCP.Algebraic.BinaryIrreduciblePolynomial
