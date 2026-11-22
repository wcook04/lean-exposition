/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BilinearDistance
import PCP.Algebraic.BinaryPolynomialEmbedding
import PCP.Algebraic.HadamardCharacterization

/-!
# Bilinear defects characterize Hadamard codewords

An algebraic variant of the induction in Appendix B. For a linear functional on
the query space, its multiplicativity defect is bilinear in the two queries.
The quarter-distance bound therefore promotes a sufficiently small defect to
an exact product law. The degree-one by degree-`r-1` law alone determines every
squarefree monomial, and hence the whole codeword. This uses only the last of
the multiplication checks from the paper's tester.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {t a b r : ℕ}

/-- The bilinear discrepancy between applying a linear functional to a product
and multiplying its values on the two factors. -/
noncomputable def multiplicativityDefect
    (L : Coefficients t r →ₗ[ZMod 2] ZMod 2) (h : a + b ≤ r) :
    Coefficients t a →+ Coefficients t b →+ ZMod 2 := by
  refine AddMonoidHom.mk' (fun p => AddMonoidHom.mk'
    (fun q => L (mixedProduct h p q) -
      L (embed (by omega : a ≤ r) p) * L (embed (by omega : b ≤ r) q)) ?_) ?_
  · intro q q'
    simp only [mixedProduct_add_right, map_add, mul_add]
    ring
  · intro p p'
    apply AddMonoidHom.ext
    intro q
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply,
      mixedProduct_add_left, map_add, add_mul]
    ring

@[simp] theorem multiplicativityDefect_apply
    (L : Coefficients t r →ₗ[ZMod 2] ZMod 2) (h : a + b ≤ r)
    (p : Coefficients t a) (q : Coefficients t b) :
    multiplicativityDefect L h p q = L (mixedProduct h p q) -
      L (embed (by omega : a ≤ r) p) * L (embed (by omega : b ≤ r) q) := rfl

/-- A discrepancy below one quarter forces exact multiplicativity on the two
specified degree spaces. -/
theorem map_mixedProduct_of_relativeDistance_lt
    (L : Coefficients t r →ₗ[ZMod 2] ZMod 2) (h : a + b ≤ r)
    (hdefect : relativeDistance
      (fun p : Coefficients t a × Coefficients t b => L (mixedProduct h p.1 p.2))
      (fun p => L (embed (by omega : a ≤ r) p.1) *
        L (embed (by omega : b ≤ r) p.2)) < (1 : ℚ) / 4)
    (p : Coefficients t a) (q : Coefficients t b) :
    L (mixedProduct h p q) = L (embed (by omega : a ≤ r) p) *
      L (embed (by omega : b ≤ r) q) := by
  have hd : relativeDistance
      (fun pq : Coefficients t a × Coefficients t b =>
        multiplicativityDefect L h pq.1 pq.2) 0 < (1 : ℚ) / 4 := by
    simpa only [multiplicativityDefect_apply, relativeDistance, hammingDist,
      Pi.zero_apply, sub_ne_zero] using hdefect
  have hz := BilinearDistance.eq_zero_of_relativeDistance_lt (multiplicativityDefect L h) hd
  have hpq := congrArg (fun B : Coefficients t a →+ Coefficients t b →+ ZMod 2 => B p q) hz
  simpa only [multiplicativityDefect_apply, AddMonoidHom.zero_apply, sub_eq_zero] using hpq

/-- A unital linear functional preserving the maximal-degree tested products
is the evaluation codeword specified by its coordinate queries. -/
theorem eq_encode_of_unit_of_mixedProduct (hr : 1 ≤ r)
    (L : Coefficients t r →ₗ[ZMod 2] ZMod 2) (hunit : L (constant 1) = 1)
    (hmul : 2 ≤ r → ∀ (p : Coefficients t 1) (q : Coefficients t (r - 1)),
      L (mixedProduct (by omega : 1 + (r - 1) ≤ r) p q) =
        L (embed hr p) * L (embed (Nat.sub_le r 1) q)) :
    (L : Coefficients t r → ZMod 2) = encode r (decodedMessage L) := by
  have hmon : ∀ (s : Finset (Fin t)) (hs : s.card ≤ r),
      L (Pi.single (⟨s, hs⟩ : Monomials t r) 1) = ∏ i ∈ s, decodedMessage L i := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; simpa [constant] using hunit
    | @insert i s hi ih =>
      intro hs
      have hcard : s.card + 1 ≤ r := by simpa only [card_insert_of_notMem hi] using hs
      by_cases he : s = ∅
      · subst s
        simp [decodedMessage_apply L hr, variableCoeff]
      · have hpos : 0 < s.card := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
        have hr2 : 2 ≤ r := by omega
        let q : Coefficients t (r - 1) := Pi.single ⟨s, by omega⟩ 1
        have hemb : embed (Nat.sub_le r 1) q =
            Pi.single (⟨s, by omega⟩ : Monomials t r) 1 := by
          apply evaluation_injective
          funext x
          simp only [evaluate_embed, q, evaluate_single]
        have hprod : mixedProduct (by omega : 1 + (r - 1) ≤ r)
            (variableCoeff (le_refl 1) i) q =
            Pi.single (⟨insert i s, hs⟩ : Monomials t r) 1 := by
          apply evaluation_injective
          funext x
          simp [q, evaluate_single, hi]
        rw [← hprod, hmul hr2, embed_variableCoeff, hemb, ih]
        simp only [prod_insert hi, decodedMessage_apply L hr]
  funext p
  rw [← Finset.univ_sum_single p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hsingle : Pi.single s (p s) = (p s) • Pi.single s (1 : ZMod 2) := by
    funext u
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  rw [hsingle, map_smul, map_smul]
  congr 1
  change L (Pi.single s 1) = evaluate (decodedMessage L) (Pi.single s 1)
  rw [evaluate_single, one_mul]
  exact hmon s.val s.property

/-- A unital linear word with multiplicativity error below one quarter is an
evaluation codeword. For `r = 1` there is no multiplication hypothesis. -/
theorem eq_encode_of_unit_of_multiplicativityDistance_lt (hr : 1 ≤ r)
    (L : Coefficients t r →ₗ[ZMod 2] ZMod 2) (hunit : L (constant 1) = 1)
    (hdefect : 2 ≤ r → relativeDistance
      (fun p : Coefficients t 1 × Coefficients t (r - 1) =>
        L (mixedProduct (by omega : 1 + (r - 1) ≤ r) p.1 p.2))
      (fun p => L (embed hr p.1) * L (embed (Nat.sub_le r 1) p.2)) < (1 : ℚ) / 4) :
    (L : Coefficients t r → ZMod 2) = encode r (decodedMessage L) := by
  apply eq_encode_of_unit_of_mixedProduct hr L hunit
  intro hr2 p q
  exact map_mixedProduct_of_relativeDistance_lt L _ (hdefect hr2) p q

end PCP.Algebraic.Hadamard
