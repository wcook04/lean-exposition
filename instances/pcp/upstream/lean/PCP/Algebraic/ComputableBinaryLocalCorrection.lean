/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ComputableHadamardTest
import PCP.Algebraic.FieldQueryArithmetic

/-!
# Executable interpolation, binary testing, and local correction

All runtime labels and field expressions use the explicit coefficient and field
arithmetic. The equality theorems hold for arbitrary received tables and preserve
the exact query order and optional answers of the semantic procedures. These are
semantic implementation identities; the concrete machine-time bound for their
production use is supplied by `PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.ComputableBinaryLagrangeConstraint

open BinaryPolynomialSpace PolynomialLine

variable {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {c t r : ℕ}

/-- Skip a zero-weight query before consulting the received oracle. -/
def weightedRead (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : Coefficients t r → ZMod 2) (a : F) (w : Fin t → ZMod 2) : ZMod 2 :=
  if a = 0 then 0 else H (BooleanCoefficientArithmetic.homogeneousIndex hr
    (FieldQueryArithmetic.scaleLabel ρ a w))

/-- The interpolation residual with finite-product weights. -/
def check (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) : ZMod 2 :=
  H (point u v z) (BooleanCoefficientArithmetic.homogeneousIndex hr w) -
    ∑ i, weightedRead hr ρ (H (point u v (a i)))
      (FieldQueryArithmetic.interpolationWeight a z i) w

/-- The executable query list omits exactly the zero-weight terms. -/
def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    List ((σ → F) × Coefficients t r) :=
  (point u v z, BooleanCoefficientArithmetic.homogeneousIndex hr w) ::
    (List.finRange (c + 1)).filterMap (fun i =>
      if FieldQueryArithmetic.interpolationWeight a z i = 0 then none
      else some (point u v (a i), BooleanCoefficientArithmetic.homogeneousIndex hr
        (FieldQueryArithmetic.scaleLabel ρ (FieldQueryArithmetic.interpolationWeight a z i) w)))

@[simp] theorem weightedRead_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : Coefficients t r → ZMod 2) (a : F) (w : Fin t → ZMod 2) :
    weightedRead hr ρ H a w = HadamardWeights.weightedRead hr ρ H a w := by
  simp [weightedRead, HadamardWeights.weightedRead]

@[simp] theorem check_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    check hr ρ a H u v z w = BinaryLagrangeConstraint.check hr ρ a H u v z w := by
  simp [check, BinaryLagrangeConstraint.check]

@[simp] theorem queries_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    queries hr ρ a u v z w = BinaryLagrangeConstraint.queries hr ρ a u v z w := by
  simp only [queries, BinaryLagrangeConstraint.queries,
    BooleanCoefficientArithmetic.homogeneousIndex_eq, FieldQueryArithmetic.scaleLabel_eq,
    FieldQueryArithmetic.interpolationWeight_eq]
  congr 1
  congr 1
  funext i
  split_ifs <;> rfl

end PCP.Algebraic.ComputableBinaryLagrangeConstraint

namespace PCP.Algebraic.ComputableBinaryLowDegreeTest

open BinaryPolynomialSpace BinaryLowDegreeTest

variable {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {c t r : ℕ}

/-- Executable interpolation acceptance. -/
def interpolationTest (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (s : InterpolationRandomness F σ t) : Bool :=
  decide (ComputableBinaryLagrangeConstraint.check hr ρ a H s.1.1.1 s.1.1.2 0 s.2 = 0)

/-- The selected Hadamard or interpolation branch. -/
def test (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (s : TestRandomness F σ t r) : Bool :=
  if s.1 then interpolationTest hr ρ a H s.2.2
  else ComputableHadamardTest.test hr (H s.2.1.1) s.2.1.2

/-- Only the selected branch's locations are queried. -/
def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (s : TestRandomness F σ t r) :
    List ((σ → F) × Coefficients t r) :=
  if s.1 then
    ComputableBinaryLagrangeConstraint.queries hr ρ a
      s.2.2.1.1.1 s.2.2.1.1.2 0 s.2.2.2
  else (ComputableHadamardTest.queries hr s.2.1.2).map (fun p => (s.2.1.1, p))

@[simp] theorem interpolationTest_eq (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) (s : InterpolationRandomness F σ t) :
    interpolationTest hr ρ a H s = BinaryLowDegreeTest.interpolationTest hr ρ a H s := by
  simp [interpolationTest, BinaryLowDegreeTest.interpolationTest]

@[simp] theorem test_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (s : TestRandomness F σ t r) : test hr ρ a H s = BinaryLowDegreeTest.test hr ρ a H s := by
  simp [test, BinaryLowDegreeTest.test]

@[simp] theorem queries_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (s : TestRandomness F σ t r) :
    queries hr ρ a s = BinaryLowDegreeTest.queries hr ρ a s := by
  simp [queries, BinaryLowDegreeTest.queries]

end PCP.Algebraic.ComputableBinaryLowDegreeTest

namespace PCP.Algebraic.ComputableBinaryLocalCorrection

open BinaryPolynomialSpace PolynomialLine BinaryLocalCorrection

variable {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {m c t : ℕ}

/-- The executable weighted local corrector, including both rejection branches. -/
def run (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    Option (ZMod 2) :=
  if ComputableBinaryLowDegreeTest.test (le_refl 1) ρ nodes (H b) s then
    if ComputableBinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c (z : F)) v w =
        f (point a b (z : F)) (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) w) then
      some (ComputableBinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c 0) v w)
    else none
  else none

/-- Supply the corrector's parameters from its structural sample. -/
def sample (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) (s : Sample F σ m c t) :
    Option (ZMod 2) :=
  run ρ nodes ζ f H a s.1 s.2.1 s.2.2.1.1 s.2.2.1.2 s.2.2.2

/-- The exact semantic list, computing every coefficient label directly. -/
def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    List (Query F σ m c t) :=
  Sum.inl (point a b (z : F), BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) w) ::
    ((ComputableBinaryLowDegreeTest.queries (le_refl 1) ρ nodes s).map
      (fun p => Sum.inr (b, p)) ++
      (ComputableBinaryStandardLocalCorrection.queries c ζ ρ
        (SetMultilinear.evaluationPoint m c (z : F)) v w).map (fun p => Sum.inr (b, p)) ++
      (ComputableBinaryStandardLocalCorrection.queries c ζ ρ
        (SetMultilinear.evaluationPoint m c 0) v w).map (fun p => Sum.inr (b, p)))

@[simp] theorem run_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    run ρ nodes ζ f H a b z v w s = BinaryLocalCorrection.run ρ nodes ζ f H a b z v w s := by
  simp [run, BinaryLocalCorrection.run]

@[simp] theorem sample_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) (s : Sample F σ m c t) :
    sample ρ nodes ζ f H a s = BinaryLocalCorrection.sample ρ nodes ζ f H a s := by
  simp [sample, BinaryLocalCorrection.sample]

@[simp] theorem queries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    queries ρ nodes ζ a b z v w s = BinaryLocalCorrection.queries ρ nodes ζ a b z v w s := by
  simp [queries, BinaryLocalCorrection.queries]

end PCP.Algebraic.ComputableBinaryLocalCorrection

namespace PCP.Algebraic.ComputableEncodedLineLowDegreeTest

open BinaryPolynomialSpace PolynomialLine EncodedLineLowDegreeTest

variable {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {m c t r : ℕ}

/-- The computed comparison bit from the auxiliary encoded line. -/
def corrected (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (ζ : F) (H : Auxiliary F σ m c t) (s : Sample F σ m c t r) : ZMod 2 :=
  ComputableBinaryStandardLocalCorrection.correct c ζ ρ (H s.1)
    (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2

/-- All three executable outer checks must accept. -/
def test (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t)
    (s : Sample F σ m c t r) : Bool :=
  ComputableHadamardTest.test hr (f s.1.1) s.2.2.2.1 &&
    ComputableBinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2.2 &&
    decide (corrected ρ ζ H s =
      f (point s.1.1 s.1.2 s.2.1) (BooleanCoefficientArithmetic.homogeneousIndex hr s.2.2.1.2))

/-- The exact concatenation of all three checks' locations. -/
def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (s : Sample F σ m c t r) :
    List (Query F σ m c t r) :=
  (ComputableHadamardTest.queries hr s.2.2.2.1).map (fun p => Sum.inl (s.1.1, p)) ++
    (ComputableBinaryLowDegreeTest.queries (le_refl 1) ρ nodes s.2.2.2.2).map
      (fun p => Sum.inr (s.1, p)) ++
    (ComputableBinaryStandardLocalCorrection.queries c ζ ρ
      (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2).map
        (fun p => Sum.inr (s.1, p)) ++
    [Sum.inl (point s.1.1 s.1.2 s.2.1,
      BooleanCoefficientArithmetic.homogeneousIndex hr s.2.2.1.2)]

omit [DecidableEq F] in
@[simp] theorem corrected_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (ζ : F) (H : Auxiliary F σ m c t) (s : Sample F σ m c t r) :
    corrected ρ ζ H s = EncodedLineLowDegreeTest.corrected ρ ζ H s := by
  simp [corrected, EncodedLineLowDegreeTest.corrected]

@[simp] theorem test_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t)
    (s : Sample F σ m c t r) :
    test hr ρ nodes ζ f H s = EncodedLineLowDegreeTest.test hr ρ nodes ζ f H s := by
  simp [test, EncodedLineLowDegreeTest.test]

@[simp] theorem queries_eq (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (s : Sample F σ m c t r) :
    queries hr ρ nodes ζ s = EncodedLineLowDegreeTest.queries hr ρ nodes ζ s := by
  simp [queries, EncodedLineLowDegreeTest.queries]

end PCP.Algebraic.ComputableEncodedLineLowDegreeTest
