/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardTest
import PCP.Algebraic.FiniteDistance

/-!
# The individual rejection events of the Hadamard test

Each marginal is bounded by the rejection probability of HadTest. The proofs
explicitly remove independent unused samples by finite equivalences, including
the dependent family of lower-degree factors in the multiplication loop.
-/

namespace PCP.Algebraic.Hadamard

open BinaryPolynomialSpace

variable {t r : ℕ}

private theorem distance_sampling_equiv {A B S α : Type*}
    [Fintype A] [Finite B] [Fintype S] [Nonempty B] [DecidableEq α]
    (e : S ≃ A × B) (f g : A → α) :
    relativeDistance (fun s => f (e s).1) (fun s => g (e s).1) =
      relativeDistance f g := by
  let := Fintype.ofFinite B
  exact (relativeDistance_comp_equiv e (fun p => f p.1) (fun p => g p.1)).trans
    (relativeDistance_comp_fst f g)

/-- Every failed constituent check forces rejection of the whole sample. -/
theorem testEvent_failure_le (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    {α : Type*} [DecidableEq α] (f g : TestRandomness t r → α)
    (h : ∀ s, testAccepts hr H s → f s = g s) :
    relativeDistance f g ≤ testRejectionRate hr H := by
  apply relativeDistance_le_of_disagreement f g (test hr H) (fun _ => true)
  intro s hs ht
  exact hs (h s ((test_eq_true_iff hr H s).mp ht))

/-- The BLR check on its own pair of independent full-degree queries. -/
theorem linearityRejection_le_testRejection (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    relativeDistance
      (fun p : Coefficients t r × Coefficients t r => H (p.1 + p.2))
      (fun p => H p.1 + H p.2) ≤ testRejectionRate hr H := by
  have he := distance_sampling_equiv
    (Equiv.prodAssoc (Coefficients t r) (Coefficients t r)
      (Coefficients t 1 × ((k : Fin (r - 1)) → Coefficients t (k.val + 1)))).symm
    (fun p : Coefficients t r × Coefficients t r => H (p.1 + p.2))
    (fun p => H p.1 + H p.2)
  rw [← he]
  exact testEvent_failure_le hr H _ _ (fun _ h => h.1)

/-- The corrected unit check, averaged only over its random shift. -/
theorem unitRejection_le_testRejection (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    relativeDistance (selfCorrect H (constant 1)) (fun _ => 1) ≤
      testRejectionRate hr H := by
  have he := relativeDistance_comp_fst
    (κ := Coefficients t r × Coefficients t 1 ×
      ((k : Fin (r - 1)) → Coefficients t (k.val + 1)))
    (selfCorrect H (constant 1)) (fun _ => 1)
  rw [← he]
  exact testEvent_failure_le hr H _ _ (fun _ h => h.2.1)

private def linearSamplingEquiv (t r : ℕ) : TestRandomness t r ≃
    (Coefficients t 1 × Coefficients t r) ×
      (Coefficients t r × ((k : Fin (r - 1)) → Coefficients t (k.val + 1))) where
  toFun s := ((s.2.2.1, s.1), (s.2.1, s.2.2.2))
  invFun p := (p.1.2, p.2.1, p.1.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Degree-one consistency, with its affine query and shift sampled independently. -/
theorem degreeOneRejection_le_testRejection (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    relativeDistance
      (fun p : Coefficients t 1 × Coefficients t r => selfCorrect H (embed hr p.1) p.2)
      (fun p => H (embed hr p.1)) ≤ testRejectionRate hr H := by
  have he := distance_sampling_equiv (linearSamplingEquiv t r)
    (fun p : Coefficients t 1 × Coefficients t r => selfCorrect H (embed hr p.1) p.2)
    (fun p => H (embed hr p.1))
  rw [← he]
  exact testEvent_failure_le hr H _ _ (fun _ h => h.2.2.1)

private def productSamplingEquiv (t : ℕ) (k : Fin (r - 1)) : TestRandomness t r ≃
    ((Coefficients t 1 × Coefficients t (k.val + 1)) × Coefficients t r) ×
      (Coefficients t r ×
        ((j : {j : Fin (r - 1) // j ≠ k}) → Coefficients t (j.val.val + 1))) :=
  (Equiv.prodCongr (Equiv.refl (Coefficients t r))
    (Equiv.prodCongr (Equiv.refl (Coefficients t r))
      (Equiv.prodCongr (Equiv.refl (Coefficients t 1))
        (Equiv.piSplitAt k (fun j : Fin (r - 1) => Coefficients t (j.val + 1)))))).trans
    { toFun := fun s => (((s.2.2.1, s.2.2.2.1), s.1), (s.2.1, s.2.2.2.2))
      invFun := fun p => (p.1.2, p.2.1, p.1.1.1, p.1.1.2, p.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Each corrected multiplication check, with exactly its three independent inputs. -/
theorem productRejection_le_testRejection (hr : 1 ≤ r)
    (H : Coefficients t r → ZMod 2) (k : Fin (r - 1)) :
    relativeDistance
      (fun p : (Coefficients t 1 × Coefficients t (k.val + 1)) × Coefficients t r =>
        selfCorrect H (mixedProduct (TestRandomness.productDegree_le k) p.1.1 p.1.2) p.2)
      (fun p => selfCorrect H (embed hr p.1.1) p.2 *
        selfCorrect H (embed (TestRandomness.factorDegree_le k) p.1.2) p.2) ≤
      testRejectionRate hr H := by
  have he := distance_sampling_equiv (productSamplingEquiv t k)
    (fun p : (Coefficients t 1 × Coefficients t (k.val + 1)) × Coefficients t r =>
      selfCorrect H (mixedProduct (TestRandomness.productDegree_le k) p.1.1 p.1.2) p.2)
    (fun p => selfCorrect H (embed hr p.1.1) p.2 *
      selfCorrect H (embed (TestRandomness.factorDegree_le k) p.1.2) p.2)
  rw [← he]
  exact testEvent_failure_le hr H _ _ (fun _ h => h.2.2.2 k)

/-- The final multiplication check, with degree parameters stated without index casts. -/
theorem maximalProductRejection_le_testRejection (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (H : Coefficients t r → ZMod 2) :
    relativeDistance
      (fun p : (Coefficients t 1 × Coefficients t (r - 1)) × Coefficients t r =>
        selfCorrect H (mixedProduct (by omega : 1 + (r - 1) ≤ r) p.1.1 p.1.2) p.2)
      (fun p => selfCorrect H (embed hr p.1.1) p.2 *
        selfCorrect H (embed (Nat.sub_le r 1) p.1.2) p.2) ≤
      testRejectionRate hr H := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  exact productRejection_le_testRejection hr H (⟨n, by omega⟩ : Fin (n + 2 - 1))

end PCP.Algebraic.Hadamard
