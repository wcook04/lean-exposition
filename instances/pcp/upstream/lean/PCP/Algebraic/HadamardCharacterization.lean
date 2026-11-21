/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard
import PCP.Algebraic.BinaryPolynomialProduct
import Mathlib.Algebra.Module.ZMod

/-!
# Local characterization of low-degree Hadamard codewords

Claim 3.9, in Boolean coordinates: a word is an evaluation codeword exactly when
it preserves addition, the constant one, and products whose degrees fit the query
bound. Multiplication uses reduced representatives, as required by the finite query
space. The existence statement also holds at degree zero; the recovered message
is unique only at positive degree.

This is an exact characterization. The soundness of the robust, randomly sampled
syntactic test of Lemma 3.10 is `Hadamard.test_soundness` in `HadamardSoundness`.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {t r : ℕ}

/-- The three local algebraic laws of Claim 3.9. -/
structure IsLocallyConsistent (H : Coefficients t r → ZMod 2) : Prop where
  map_add (p q : Coefficients t r) : H (p + q) = H p + H q
  map_one : H (constant 1) = 1
  map_mul (p q : Coefficients t r)
      (h : (polynomial t r p).totalDegree + (polynomial t r q).totalDegree ≤ r) :
    H (boundedProduct p q h) = H p * H q

/-- Evaluation obeys all three local laws. -/
theorem isLocallyConsistent_encode (x : Fin t → ZMod 2) :
    IsLocallyConsistent (encode r x) where
  map_add := (encode r x).map_add
  map_one := encode_constant x 1
  map_mul p q h := evaluate_boundedProduct x p q h

/-- Read the message from coordinate queries; at degree zero choose the zero vector. -/
noncomputable def decodedMessage (H : Coefficients t r → ZMod 2) (i : Fin t) : ZMod 2 :=
  if hr : 1 ≤ r then H (variableCoeff hr i) else 0

@[simp] theorem decodedMessage_apply (H : Coefficients t r → ZMod 2) (hr : 1 ≤ r)
    (i : Fin t) : decodedMessage H i = H (variableCoeff hr i) := by
  simp [decodedMessage, hr]

@[simp] theorem decodedMessage_degree_zero (H : Coefficients t 0 → ZMod 2) :
    decodedMessage H = 0 := by
  funext i
  simp [decodedMessage]

@[simp] theorem decodedMessage_encode (hr : 1 ≤ r) (x : Fin t → ZMod 2) :
    decodedMessage (encode r x) = x := by
  funext i
  simp [decodedMessage_apply _ hr]

namespace IsLocallyConsistent

variable {H : Coefficients t r → ZMod 2} (hH : IsLocallyConsistent H)

/-- Additivity already implies binary linearity. -/
noncomputable def toLinearMap : Coefficients t r →ₗ[ZMod 2] ZMod 2 :=
  (AddMonoidHom.mk' H hH.map_add).toZModLinearMap 2

@[simp] theorem toLinearMap_apply (p : Coefficients t r) : hH.toLinearMap p = H p := rfl

include hH

/-- Multiplication determines every squarefree monomial from the coordinate queries. -/
theorem map_monomial (s : Finset (Fin t)) (hs : s.card ≤ r) :
    H (Pi.single (⟨s, hs⟩ : Monomials t r) 1) = ∏ i ∈ s, decodedMessage H i := by
  induction s using Finset.induction_on with
  | empty => simpa [constant] using hH.map_one
  | @insert i s hi ih =>
    have hs' : s.card ≤ r := (card_le_card (subset_insert i s)).trans hs
    have hcard : s.card + 1 ≤ r := by simpa only [card_insert_of_notMem hi] using hs
    have hr : 1 ≤ r := by omega
    let q : Coefficients t r := Pi.single ⟨s, hs'⟩ 1
    have hdeg : (polynomial t r (variableCoeff hr i)).totalDegree +
        (polynomial t r q).totalDegree ≤ r := by
      simpa only [q, polynomial_variableCoeff, MvPolynomial.totalDegree_X,
        totalDegree_polynomial_single_one, Nat.add_comm] using hcard
    have hprod : boundedProduct (variableCoeff hr i) q hdeg =
        Pi.single (⟨insert i s, hs⟩ : Monomials t r) 1 := by
      apply evaluation_injective
      funext x
      simp [q, evaluate_single, hi]
    rw [← hprod, hH.map_mul, show H q = ∏ j ∈ s, decodedMessage H j from ih hs']
    simp only [prod_insert hi, decodedMessage_apply H hr]

/-- The locally consistent word is exactly the encoding of its coordinate-query values. -/
theorem eq_encode : H = encode r (decodedMessage H) := by
  apply funext
  intro p
  change hH.toLinearMap p = encode r (decodedMessage H) p
  rw [← Finset.univ_sum_single p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hsingle : Pi.single s (p s) = (p s) • Pi.single s (1 : ZMod 2) := by
    funext u
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  rw [hsingle, map_smul, map_smul]
  congr 1
  change H (Pi.single s 1) = evaluate (decodedMessage H) (Pi.single s 1)
  rw [evaluate_single, one_mul]
  exact hH.map_monomial s.val s.property

end IsLocallyConsistent

/-- Claim 3.9: the three local laws characterize evaluation codewords. -/
theorem isLocallyConsistent_iff (H : Coefficients t r → ZMod 2) :
    IsLocallyConsistent H ↔ ∃ x : Fin t → ZMod 2, H = encode r x := by
  constructor
  · intro hH
    exact ⟨decodedMessage H, hH.eq_encode⟩
  · rintro ⟨x, rfl⟩
    exact isLocallyConsistent_encode x

/-- Equivalently, the word is the restriction of a unital ring homomorphism on all polynomials. -/
theorem isLocallyConsistent_iff_ringHom (H : Coefficients t r → ZMod 2) :
    IsLocallyConsistent H ↔
      ∃ φ : MvPolynomial (Fin t) (ZMod 2) →+* ZMod 2,
        ∀ p : Coefficients t r, H p = φ (polynomial t r p) := by
  rw [isLocallyConsistent_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨MvPolynomial.eval x, fun _ => rfl⟩
  · rintro ⟨φ, hφ⟩
    have he : φ = MvPolynomial.eval (fun i => φ (MvPolynomial.X i)) := by
      apply MvPolynomial.ringHom_ext'
      · exact Subsingleton.elim _ _
      · intro i
        simp only [MvPolynomial.eval_X]
    refine ⟨fun i => φ (MvPolynomial.X i), funext (fun p => ?_)⟩
    exact (hφ p).trans (RingHom.congr_fun he _)

/-- Transport Claim 3.9 through the paper's bijective field-coordinate map. -/
theorem isLocallyConsistent_iff_of_equiv {α : Type*} (ρ : α ≃ (Fin t → ZMod 2))
    (H : Coefficients t r → ZMod 2) :
    IsLocallyConsistent H ↔ ∃ u : α, H = encode r (ρ u) := by
  rw [isLocallyConsistent_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ρ.symm x, by simpa using hx⟩
  · rintro ⟨u, hu⟩
    exact ⟨ρ u, hu⟩

/-- At positive degree the message supplied by the characterization is unique. -/
theorem isLocallyConsistent_iff_existsUnique (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) :
    IsLocallyConsistent H ↔ ∃! x : Fin t → ZMod 2, H = encode r x := by
  rw [isLocallyConsistent_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    apply encode_injective hr
    exact LinearMap.ext (fun p => congrFun (hy.symm.trans hx) p)
  · rintro ⟨x, hx, _⟩
    exact ⟨x, hx⟩

end PCP.Algebraic.Hadamard
