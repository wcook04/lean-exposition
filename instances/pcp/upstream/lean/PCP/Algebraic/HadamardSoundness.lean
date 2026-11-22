/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BLR
import PCP.Algebraic.HadamardTestMarginals
import PCP.Algebraic.HadamardRobustBounds
import PCP.Algebraic.BilinearHadamard

/-!
# Robust soundness of the low-degree Hadamard test

The mathematical soundness conclusion of Lemma 3.10 / Appendix B: rejection at
most `δ < 1/28` implies proximity at most `δ` on the full query space and at most
`3δ` on the affine degree-one queries, to one and the same encoding. BLR supplies
the nearby linear word; corrected checks force its unit and multiplicativity.
The concrete tester and its query bound are in `HadamardTest`. Running-time and
random-bit implementation certificates are separate obligations.
-/

namespace PCP.Algebraic.Hadamard

open BinaryPolynomialSpace

variable {t r : ℕ}

/-- Lemma 3.10: low rejection yields a codeword close on both full and degree-one queries. -/
theorem test_soundness (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    {δ : ℚ} (hδ : δ < (1 : ℚ) / 28) (hH : testRejectionRate hr H ≤ δ) :
    ∃ x : Fin t → ZMod 2,
      relativeDistance H (encode r x) ≤ δ ∧
      relativeDistance (fun p : Coefficients t 1 => H (embed hr p)) (encode 1 x) ≤
        3 * δ := by
  have hblr : BLR.rejectionProbability H ≤ δ :=
    (linearityRejection_le_testRejection hr H).trans hH
  obtain ⟨L, hL⟩ := BLR.exists_linearMap_distance_le_of_rejection_le H hblr
  have hunit : L (constant 1) = 1 :=
    eq_of_selfCorrect_check_of_le L.toAddMonoidHom H (constant 1) 1
      (by linarith : δ < (1 : ℚ) / 3) hL
      ((unitRejection_le_testRejection hr H).trans hH)
  have he : (L : Coefficients t r → ZMod 2) = encode r (decodedMessage L) := by
    apply eq_encode_of_unit_of_multiplicativityDistance_lt hr L hunit
    intro hr2
    have hp := (maximalProductRejection_le_testRejection hr hr2 H).trans hH
    exact multiplicative_defect_lt_quarter L.toAddMonoidHom H
      (fun p : Coefficients t 1 × Coefficients t (r - 1) => embed hr p.1)
      (fun p => embed (Nat.sub_le r 1) p.2)
      (fun p => mixedProduct (by omega : 1 + (r - 1) ≤ r) p.1 p.2) hδ hL hp
  refine ⟨decodedMessage L, ?_, ?_⟩
  · rwa [← he]
  · have hd := restriction_distance_le_three L.toAddMonoidHom H (embed hr) hL
      ((degreeOneRejection_le_testRejection hr H).trans hH)
    have hres : (fun p : Coefficients t 1 => L (embed hr p)) =
        encode 1 (decodedMessage L) := by
      funext p
      have h := congrFun he (embed hr p)
      simpa only [encode, evaluate_embed] using h
    change relativeDistance (fun p => H (embed hr p))
      (fun p => L (embed hr p)) ≤ 3 * δ at hd
    rwa [hres] at hd

/-- The quantitative statement with the actual rejection rate as its error parameter. -/
theorem test_soundness_at_rejectionRate (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (hH : testRejectionRate hr H < (1 : ℚ) / 28) :
    ∃ x : Fin t → ZMod 2,
      relativeDistance H (encode r x) ≤ testRejectionRate hr H ∧
      relativeDistance (fun p : Coefficients t 1 => H (embed hr p)) (encode 1 x) ≤
        3 * testRejectionRate hr H :=
  test_soundness hr H hH le_rfl

/-- Zero rejection characterizes exactly the codewords. -/
theorem testRejectionRate_eq_zero_iff_encode (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    testRejectionRate hr H = 0 ↔ ∃ x : Fin t → ZMod 2, H = encode r x := by
  constructor
  · intro h
    obtain ⟨x, hx, _⟩ := test_soundness hr H (δ := 0) (by norm_num) h.le
    exact ⟨x, relativeDistance_eq_zero_iff.mp
      (le_antisymm hx (relativeDistance_nonneg _ _))⟩
  · rintro ⟨x, rfl⟩
    exact testRejectionRate_encode hr x

end PCP.Algebraic.Hadamard
