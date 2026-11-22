/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BooleanCoefficientArithmetic
import PCP.Algebraic.BinaryDifferenceConsistency
import PCP.Algebraic.BinaryStandardLocalCorrection
import PCP.Algebraic.FieldQueryArithmetic

/-!
# Executable Hadamard tests, difference checks, and standard correction

These procedures compute their labels using finite coefficient arithmetic. Exact
identities with the semantic definitions preserve the existing query lists and
verdicts on arbitrary received oracles, including corrupted ones. This is an
executable implementation bridge, not a machine-time certificate.
-/

namespace PCP.Algebraic.ComputableHadamardTest

open BinaryPolynomialSpace Hadamard

variable {t r : ℕ}

/-- The degree-one query, padded to the requested coefficient space. -/
def linearQuery (hr : 1 ≤ r) (s : TestRandomness t r) : Coefficients t r :=
  BooleanCoefficientArithmetic.embed hr s.linear

/-- The iteration's degree-bounded factor query. -/
def factorQuery (s : TestRandomness t r) (k : Fin (r - 1)) : Coefficients t r :=
  BooleanCoefficientArithmetic.embed (TestRandomness.factorDegree_le k) (s.factor k)

/-- The iteration's product, computed by union convolution. -/
def productQuery (s : TestRandomness t r) (k : Fin (r - 1)) : Coefficients t r :=
  BooleanCoefficientArithmetic.mixedProduct (TestRandomness.productDegree_le k)
    s.linear (s.factor k)

/-- The finite conjunction of the actual Hadamard consistency checks. -/
def Accepts (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : Prop :=
  H (s.base + s.auxiliary) = H s.base + H s.auxiliary ∧
  H (BooleanCoefficientArithmetic.constant 1 + s.base) - H s.base = 1 ∧
  H (linearQuery hr s + s.base) - H s.base = H (linearQuery hr s) ∧
  ∀ k : Fin (r - 1),
    H (productQuery s k + s.base) - H s.base =
      (H (linearQuery hr s + s.base) - H s.base) *
      (H (factorQuery s k + s.base) - H s.base)

instance (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2) (s : TestRandomness t r) :
    Decidable (Accepts hr H s) := by
  unfold Accepts
  infer_instance

/-- Executable acceptance on an arbitrary received row. -/
def test (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : Bool := decide (Accepts hr H s)

/-- Every queried coefficient word, in exactly the original order. -/
def queries (hr : 1 ≤ r) (s : TestRandomness t r) : List (Coefficients t r) :=
  [s.base, s.auxiliary, s.base + s.auxiliary, BooleanCoefficientArithmetic.constant 1 + s.base,
    linearQuery hr s + s.base, linearQuery hr s] ++
    (List.finRange (r - 1)).flatMap (fun k =>
      [productQuery s k + s.base, factorQuery s k + s.base])

@[simp] theorem linearQuery_eq (hr : 1 ≤ r) (s : TestRandomness t r) :
    linearQuery hr s = s.linearQuery hr := by
  simp [linearQuery, TestRandomness.linearQuery]

@[simp] theorem factorQuery_eq (s : TestRandomness t r) (k : Fin (r - 1)) :
    factorQuery s k = s.factorQuery k := by
  simp [factorQuery, TestRandomness.factorQuery]

@[simp] theorem productQuery_eq (s : TestRandomness t r) (k : Fin (r - 1)) :
    productQuery s k = s.productQuery k := by
  simp [productQuery, TestRandomness.productQuery]

@[simp] theorem accepts_iff (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : Accepts hr H s ↔ testAccepts hr H s := by
  simp [Accepts, testAccepts]

@[simp] theorem test_eq (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) : test hr H s = Hadamard.test hr H s := by
  apply Bool.eq_iff_iff.mpr
  simpa only [test, Hadamard.test, decide_eq_true_eq] using accepts_iff hr H s

@[simp] theorem queries_eq (hr : 1 ≤ r) (s : TestRandomness t r) :
    queries hr s = Hadamard.testQueries hr s := by
  simp [queries, Hadamard.testQueries]

end PCP.Algebraic.ComputableHadamardTest

namespace PCP.Algebraic.ComputableBinaryDifferenceConsistency

open BinaryPolynomialSpace

variable {F σ : Type*} {t r : ℕ}

/-- Executable three-query difference residual. -/
def check (hr : 1 ≤ r)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2)
    (a b : σ → F) (w : Fin t → ZMod 2) : ZMod 2 :=
  g (Sum.elim a b) (BooleanCoefficientArithmetic.homogeneousIndex hr w) -
    (f a (BooleanCoefficientArithmetic.homogeneousIndex hr w) -
      f b (BooleanCoefficientArithmetic.homogeneousIndex hr w))

/-- The same three physical locations, with computed labels. -/
def queries (hr : 1 ≤ r) (a b : σ → F) (w : Fin t → ZMod 2) :
    List (BinaryDifferenceConsistency.Query F σ t r) :=
  [Sum.inr (Sum.elim a b, BooleanCoefficientArithmetic.homogeneousIndex hr w),
    Sum.inl (a, BooleanCoefficientArithmetic.homogeneousIndex hr w),
    Sum.inl (b, BooleanCoefficientArithmetic.homogeneousIndex hr w)]

@[simp] theorem check_eq (hr : 1 ≤ r)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2)
    (a b : σ → F) (w : Fin t → ZMod 2) :
    check hr f g a b w = BinaryDifferenceConsistency.check hr f g a b w := by
  simp [check, BinaryDifferenceConsistency.check]

@[simp] theorem queries_eq (hr : 1 ≤ r) (a b : σ → F) (w : Fin t → ZMod 2) :
    queries hr a b w = BinaryDifferenceConsistency.queries hr a b w := by
  simp [queries, BinaryDifferenceConsistency.queries]

end PCP.Algebraic.ComputableBinaryDifferenceConsistency

namespace PCP.Algebraic.ComputableBinaryStandardLocalCorrection

open BinaryPolynomialSpace PolynomialLine

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}

/-- The finite root-of-unity correction sum, using computed homogeneous labels. -/
def correct (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : (σ → F) → Coefficients t 1 → ZMod 2)
    (u v : σ → F) (w : Fin t → ZMod 2) : ZMod 2 :=
  ∑ i : Fin (c + 1), H (point u v (ζ ^ (i.val + 1)))
    (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1)
      (FieldQueryArithmetic.scaleLabel ρ
        (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes c ζ) 0 i) w))

/-- The executable list of root-of-unity correction locations. -/
def queries (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (u v : σ → F) (w : Fin t → ZMod 2) :
    List ((σ → F) × Coefficients t 1) :=
  List.ofFn (fun i : Fin (c + 1) => (point u v (ζ ^ (i.val + 1)),
    BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1)
      (FieldQueryArithmetic.scaleLabel ρ
        (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes c ζ) 0 i) w)))

@[simp] theorem correct_eq (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : (σ → F) → Coefficients t 1 → ZMod 2)
    (u v : σ → F) (w : Fin t → ZMod 2) :
    correct c ζ ρ H u v w = BinaryStandardLocalCorrection.correct c ζ ρ H u v w := by
  simp [correct, BinaryStandardLocalCorrection.correct,
    GeneratorLowDegreeTest.nodes, GeneratorLowDegreeTest.weights]

@[simp] theorem queries_eq (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (u v : σ → F) (w : Fin t → ZMod 2) :
    queries c ζ ρ u v w = BinaryStandardLocalCorrection.queries c ζ ρ u v w := by
  simp [queries, BinaryStandardLocalCorrection.queries,
    GeneratorLowDegreeTest.nodes, GeneratorLowDegreeTest.weights]

end PCP.Algebraic.ComputableBinaryStandardLocalCorrection
