/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryPolynomialEmbedding
import PCP.Algebraic.HadamardCorrection

/-!
# The syntactic test for low-degree Hadamard codes

This is the paper's HadTest, using uniformly sampled finite coefficient vectors. The
sample contains independent `R`, `R'`, an affine degree-one query `L`, and one
degree-`k+1` query for each `k : Fin (r-1)`. All checks share the same `R` and `L`.

The nonadaptive query list has length `2*r+4` at positive degree. Repeated locations
are allowed, so this also bounds the number of distinct oracle locations. The
decision depends only on those locations, and honest codewords always pass.
No running-time or random-bit implementation certificate is asserted here.
-/

namespace PCP.Algebraic.Hadamard

open BinaryPolynomialSpace

variable {t r : ℕ}

/-- The independent choices in HadTest, including all loop iterations. -/
abbrev TestRandomness (t r : ℕ) :=
  Coefficients t r × Coefficients t r × Coefficients t 1 ×
    ((k : Fin (r - 1)) → Coefficients t (k.val + 1))

namespace TestRandomness

def base (s : TestRandomness t r) : Coefficients t r := s.1
def auxiliary (s : TestRandomness t r) : Coefficients t r := s.2.1
def linear (s : TestRandomness t r) : Coefficients t 1 := s.2.2.1
def factor (s : TestRandomness t r) (k : Fin (r - 1)) : Coefficients t (k.val + 1) :=
  s.2.2.2 k

theorem factorDegree_le (k : Fin (r - 1)) : k.val + 1 ≤ r := by omega
theorem productDegree_le (k : Fin (r - 1)) : 1 + (k.val + 1) ≤ r := by omega

/-- The degree-one query viewed in the full oracle domain. -/
noncomputable def linearQuery (hr : 1 ≤ r) (s : TestRandomness t r) : Coefficients t r :=
  embed hr s.linear

/-- The `k+2` iteration's degree-`k+1` query in the full domain. -/
noncomputable def factorQuery (s : TestRandomness t r) (k : Fin (r - 1)) :
    Coefficients t r := embed (factorDegree_le k) (s.factor k)

/-- The reduced product queried in the `k+2` iteration. -/
noncomputable def productQuery (s : TestRandomness t r) (k : Fin (r - 1)) :
    Coefficients t r := mixedProduct (productDegree_le k) s.linear (s.factor k)

end TestRandomness

/-- All four families of checks in HadTest. -/
def testAccepts (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : Prop :=
  H (s.base + s.auxiliary) = H s.base + H s.auxiliary ∧
  H (constant 1 + s.base) - H s.base = 1 ∧
  H (s.linearQuery hr + s.base) - H s.base = H (s.linearQuery hr) ∧
  ∀ k : Fin (r - 1),
    H (s.productQuery k + s.base) - H s.base =
      (H (s.linearQuery hr + s.base) - H s.base) *
      (H (s.factorQuery k + s.base) - H s.base)

/-- The Boolean decision, where `true` means accept. -/
noncomputable def test (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : Bool := by
  classical
  exact decide (testAccepts hr H s)

@[simp] theorem test_eq_true_iff (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : test hr H s = true ↔ testAccepts hr H s := by
  classical
  simp [test]

/-- The full list of oracle locations; shared responses are reused between checks. -/
noncomputable def testQueries (hr : 1 ≤ r) (s : TestRandomness t r) :
    List (Coefficients t r) :=
  [s.base, s.auxiliary, s.base + s.auxiliary, constant 1 + s.base,
    s.linearQuery hr + s.base, s.linearQuery hr] ++
    (List.finRange (r - 1)).flatMap (fun k =>
      [s.productQuery k + s.base, s.factorQuery k + s.base])

/-- The paper's `2*r+4` query bound, with exact accounting for response reuse. -/
theorem testQueries_length (hr : 1 ≤ r) (s : TestRandomness t r) :
    (testQueries hr s).length = 2 * r + 4 := by
  simp [testQueries, List.length_flatMap]
  omega

theorem testQueries_card_le (hr : 1 ≤ r) (s : TestRandomness t r) :
    (testQueries hr s).toFinset.card ≤ 2 * r + 4 := by
  classical
  exact (List.toFinset_card_le _).trans_eq (testQueries_length hr s)

/-- A decision really uses only the locations in the declared query list. -/
theorem testAccepts_congr (hr : 1 ≤ r) (s : TestRandomness t r)
    (H H' : Coefficients t r → ZMod 2)
    (h : ∀ p ∈ testQueries hr s, H p = H' p) :
    testAccepts hr H s ↔ testAccepts hr H' s := by
  have hb := h s.base (by simp [testQueries])
  have ha := h s.auxiliary (by simp [testQueries])
  have hab := h (s.base + s.auxiliary) (by simp [testQueries])
  have hu := h (constant 1 + s.base) (by simp [testQueries])
  have hl := h (s.linearQuery hr) (by simp [testQueries])
  have hlb := h (s.linearQuery hr + s.base) (by simp [testQueries])
  have hp (k : Fin (r - 1)) := h (s.productQuery k + s.base)
    (by simp only [testQueries, List.mem_append, List.mem_cons,
          List.mem_flatMap, List.mem_finRange, true_and]
        exact Or.inr ⟨k, Or.inl rfl⟩)
  have hf (k : Fin (r - 1)) := h (s.factorQuery k + s.base)
    (by simp only [testQueries, List.mem_append, List.mem_cons,
          List.mem_flatMap, List.mem_finRange, true_and]
        exact Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
  simp only [testAccepts, hb, ha, hab, hu, hl, hlb, hp, hf]

theorem test_congr (hr : 1 ≤ r) (s : TestRandomness t r)
    (H H' : Coefficients t r → ZMod 2)
    (h : ∀ p ∈ testQueries hr s, H p = H' p) : test hr H s = test hr H' s := by
  classical
  simp only [test, propext (testAccepts_congr hr s H H' h)]

/-- The rejection probability for the independent uniform choices in `TestRandomness`. -/
noncomputable def testRejectionRate (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance (test hr H) (fun _ => true)

theorem testRejectionRate_eq_zero_iff (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) :
    testRejectionRate hr H = 0 ↔ ∀ s, testAccepts hr H s := by
  rw [testRejectionRate, relativeDistance_eq_zero_iff]
  simp only [funext_iff, test_eq_true_iff]

theorem testRejectionRate_nonneg (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) :
    0 ≤ testRejectionRate hr H := relativeDistance_nonneg _ _

theorem testRejectionRate_le_one (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) :
    testRejectionRate hr H ≤ 1 := relativeDistance_le_one _ _

/-- Every honest encoding passes every check, for every possible random choice. -/
theorem testAccepts_encode (hr : 1 ≤ r) (x : Fin t → ZMod 2)
    (s : TestRandomness t r) : testAccepts hr (encode r x) s := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro k
  simp only [map_add, add_sub_cancel_right]
  change evaluate x (s.productQuery k) =
    evaluate x (s.linearQuery hr) * evaluate x (s.factorQuery k)
  simp only [TestRandomness.productQuery, TestRandomness.linearQuery,
    TestRandomness.factorQuery, evaluate_mixedProduct, evaluate_embed]

@[simp] theorem test_encode (hr : 1 ≤ r) (x : Fin t → ZMod 2)
    (s : TestRandomness t r) : test hr (encode r x) s = true :=
  (test_eq_true_iff hr _ s).mpr (testAccepts_encode hr x s)

/-- Perfect completeness in normalized form (Lemma 3.10, first part). -/
@[simp] theorem testRejectionRate_encode (hr : 1 ≤ r) (x : Fin t → ZMod 2) :
    testRejectionRate hr (encode r x) = 0 := by
  have h : test hr (encode r x) = fun _ => true := funext (test_encode hr x)
  rw [testRejectionRate, h]
  exact relativeDistance_self _

end PCP.Algebraic.Hadamard
