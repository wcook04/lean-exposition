/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ComputableBinaryLocalCorrection
import PCP.Algebraic.BooleanCoefficientRecovery

/-!
# Executable derived zero-on-grid checks

The primary query is supplied as an executable coefficient transformation.
The production verifier uses the cubic subset transform. Both certificate calls
use the concrete local corrector, preserving the independent correction masks
and every query occurrence. Exact identities transport the existing guarantees.
-/

namespace PCP.Algebraic.ComputableDerivedZeroOnGrid

open BinaryPolynomialSpace BinaryZeroOnGrid BinaryZeroOnGridCorrection

variable {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {n m c t r : ℕ}

/-- One certificate call, with the requested label supplied separately. -/
def call {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (M : (σ → F) → Coefficients t 1 → ZMod 2)
    (A : (σ → F) → BinaryLocalCorrection.RowOracle F m c t) (a : σ → F)
    (w : Fin t → ZMod 2) (s : CallSeed F σ m c t) : Option (ZMod 2) :=
  ComputableBinaryLocalCorrection.run ρ nodes ζ M A a s.1 s.2.1 s.2.2.1 w s.2.2.2

@[simp] theorem call_eq {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (M : (σ → F) → Coefficients t 1 → ZMod 2)
    (A : (σ → F) → BinaryLocalCorrection.RowOracle F m c t) (a : σ → F)
    (w : Fin t → ZMod 2) (s : CallSeed F σ m c t) :
    call ρ nodes ζ M A a w s = BinaryZeroOnGridCorrection.call ρ nodes ζ M A a w s := by
  simp only [call, ComputableBinaryLocalCorrection.run_eq, BinaryZeroOnGridCorrection.call]

/-- Combine the two corrected certificate bits with the supplied primary bit. -/
def withPrimaryBit (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : TestSample F n m c t) (b : ZMod 2) : Option (ZMod 2 × ZMod 2) :=
  optionCheck (some b)
    (call ρ nodes ζ M (A (zeroPoint s.1)) (zeroPoint s.1) s.2.1 s.2.2.1)
    (call ρ nodes ζ M (A (FieldQueryArithmetic.recoveryPoint H s.1))
      (FieldQueryArithmetic.recoveryPoint H s.1) s.2.1 s.2.2.2)

@[simp] theorem withPrimaryBit_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : TestSample F n m c t) (b : ZMod 2) :
    withPrimaryBit ρ nodes ζ H M A s b = DerivedZeroOnGrid.withPrimaryBit ρ nodes ζ H M A s b := by
  simp only [withPrimaryBit, call_eq, FieldQueryArithmetic.recoveryPoint_eq,
    DerivedZeroOnGrid.withPrimaryBit]

/-- A fresh coefficient mask corrects the directly computed primary query. -/
def check (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Coefficients t 1 → Coefficients t r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) : Option (ZMod 2 × ZMod 2) :=
  withPrimaryBit ρ nodes ζ H M A (DerivedZeroOnGrid.gridSeed s)
    (Hadamard.selfCorrect (p s.1)
      (Q s.1 (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) s.2.1.1)) s.2.2)

theorem check_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Coefficients t 1 → Coefficients t r)
    (P : (Fin n → F) → Polynomial F) (hP : ∀ x, (P x).natDegree ≤ r)
    (hQ : ∀ x L, Q x L = HadamardComposition.query ρ (P x) L (hP x))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    check ρ Q nodes ζ H p M A s = DerivedZeroOnGrid.check ρ P hP nodes ζ H p M A s := by
  simp only [check, withPrimaryBit_eq, BooleanCoefficientArithmetic.homogeneousIndex_eq,
    hQ, DerivedZeroOnGrid.check, HadamardDerivedOracle.answer]

/-- The concrete query list of a certificate call. -/
def callQueries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a : CertificatePoint F n)
    (w : Fin t → ZMod 2) (s : CallSeed F (Fin n ⊕ Fin n) m c t) :
    List (BinaryLocalCorrection.Query F (Fin n ⊕ Fin n) m c t) :=
  ComputableBinaryLocalCorrection.queries ρ nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2

@[simp] theorem callQueries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a : CertificatePoint F n)
    (w : Fin t → ZMod 2) (s : CallSeed F (Fin n ⊕ Fin n) m c t) :
    callQueries ρ nodes ζ a w s = DerivedZeroOnGrid.callQueries ρ nodes ζ a w s := by
  simp only [callQueries, ComputableBinaryLocalCorrection.queries_eq, DerivedZeroOnGrid.callQueries]

/-- Both primary reads and the two unchanged certificate call lists. -/
def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Coefficients t 1 → Coefficients t r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    List (DerivedZeroOnGrid.Query F n m c t r) :=
  ([Q s.1 (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) s.2.1.1) + s.2.2,
    s.2.2]).map (fun q => Sum.inl (s.1, q)) ++
  (callQueries ρ nodes ζ (zeroPoint s.1) s.2.1.1 s.2.1.2.1).map
    (fun q => Sum.inr (zeroPoint s.1, q)) ++
  (callQueries ρ nodes ζ (FieldQueryArithmetic.recoveryPoint H s.1) s.2.1.1 s.2.1.2.2).map
    (fun q => Sum.inr (FieldQueryArithmetic.recoveryPoint H s.1, q))

theorem queries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Coefficients t 1 → Coefficients t r)
    (P : (Fin n → F) → Polynomial F) (hP : ∀ x, (P x).natDegree ≤ r)
    (hQ : ∀ x L, Q x L = HadamardComposition.query ρ (P x) L (hP x))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    queries ρ Q nodes ζ H s = DerivedZeroOnGrid.queries ρ P hP nodes ζ H s := by
  simp only [queries, callQueries_eq, FieldQueryArithmetic.recoveryPoint_eq,
    BooleanCoefficientArithmetic.homogeneousIndex_eq, hQ,
    DerivedZeroOnGrid.queries, HadamardDerivedOracle.queries]

end PCP.Algebraic.ComputableDerivedZeroOnGrid
