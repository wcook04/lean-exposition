/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ComputableBinaryLocalCorrection
import PCP.Algebraic.ComputableDerivedZeroOnGrid
import PCP.Algebraic.BooleanCoefficientRecovery
import PCP.Algebraic.ThreeColorFullFieldSampling

/-!
# Executable seven-branch and whole-field three-color verifiers

Every branch uses explicit finite coefficient and field arithmetic, including
cubic translations and the public adjacency extension. The identities below
preserve the exact semantic query lists and verdicts on every received proof.
These executable definitions do not assert a concrete machine-time bound.
-/

namespace PCP.Algebraic.ComputableThreeColorVerifier

open ThreeColorVerifier

variable {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {n m c t : ℕ}

/-- The seven executable branch verdicts, in the production order. -/
def branchTest (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (i : Fin 7) :
    BranchSeed F n m c t i → Bool := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact ComputableEncodedLineLowDegreeTest.test (by omega) ρ nodes ζ π.color π.colorLines
  · exact ComputableEncodedLineLowDegreeTest.test (le_refl 1) ρ nodes ζ π.validCert π.validLines
  · exact ComputableEncodedLineLowDegreeTest.test (by omega) ρ nodes ζ
      π.difference π.differenceLines
  · exact ComputableEncodedLineLowDegreeTest.test (le_refl 1) ρ nodes ζ π.properCert π.properLines
  · exact fun s => decide (ComputableDerivedZeroOnGrid.check ρ
      (fun _ => BooleanCoefficientRecovery.cubicQuery ρ) nodes ζ H π.color π.validCert
      (validAuxiliary π) s = some (0, 0))
  · exact fun s => decide (ComputableDerivedZeroOnGrid.check ρ
      (fun x => BooleanCoefficientRecovery.weightedCubicQuery ρ
        (FieldQueryArithmetic.edgeValue H G x))
      nodes ζ H (flatDifference π) π.properCert (properAuxiliary π) s = some (0, 0))
  · exact fun s => decide (ComputableBinaryDifferenceConsistency.check (by omega)
      π.color π.difference s.1.1 s.1.2 s.2 = 0)

/-- Decide the conjunction over the explicit seven branches. -/
def test (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (s : Sample F n m c t) : Bool :=
  decide (∀ i : Fin 7, branchTest ρ nodes ζ H G π i (s i) = true)

/-- Every executable branch list is routed to the original physical tables. -/
def branchQueries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (i : Fin 7) : BranchSeed F n m c t i → List (Query F n m c t) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact fun s => (ComputableEncodedLineLowDegreeTest.queries (by omega) ρ nodes ζ s).map
      colorQuery
  · exact fun s => (ComputableEncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map
      validQuery
  · exact fun s => (ComputableEncodedLineLowDegreeTest.queries (by omega) ρ nodes ζ s).map
      differenceQuery
  · exact fun s => (ComputableEncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map
      properQuery
  · exact fun s => (ComputableDerivedZeroOnGrid.queries ρ
      (fun _ => BooleanCoefficientRecovery.cubicQuery ρ) nodes ζ H s).map validGridQuery
  · exact fun s => (ComputableDerivedZeroOnGrid.queries ρ
      (fun x => BooleanCoefficientRecovery.weightedCubicQuery ρ
        (FieldQueryArithmetic.edgeValue H G x))
      nodes ζ H s).map properGridQuery
  · exact fun s => (ComputableBinaryDifferenceConsistency.queries (by omega)
      s.1.1 s.1.2 s.2).map differenceCheckQuery

/-- Concatenate all seven original physical query lists in order. -/
def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (s : Sample F n m c t) : List (Query F n m c t) :=
  (List.ofFn (fun i : Fin 7 => branchQueries ρ nodes ζ H G i (s i))).flatten

@[simp] theorem branchTest_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (i : Fin 7) :
    branchTest ρ nodes ζ H G π i = ThreeColorVerifier.branchTest ρ nodes ζ H G π i := by
  fin_cases i <;> funext s
  · exact ComputableEncodedLineLowDegreeTest.test_eq (by omega) ρ nodes ζ
      π.color π.colorLines s
  · exact ComputableEncodedLineLowDegreeTest.test_eq (le_refl 1) ρ nodes ζ
      π.validCert π.validLines s
  · exact ComputableEncodedLineLowDegreeTest.test_eq (by omega) ρ nodes ζ
      π.difference π.differenceLines s
  · exact ComputableEncodedLineLowDegreeTest.test_eq (le_refl 1) ρ nodes ζ
      π.properCert π.properLines s
  · exact congrArg (fun z : Option (ZMod 2 × ZMod 2) => decide (z = some (0, 0)))
      (ComputableDerivedZeroOnGrid.check_eq ρ _
        (fun _ => HadamardDerivedOracle.cubic)
        (fun _ => HadamardDerivedOracle.natDegree_cubic_le)
        (fun _ L => BooleanCoefficientRecovery.cubicQuery_eq ρ L)
        nodes ζ H π.color π.validCert (validAuxiliary π) s)
  · exact congrArg (fun z : Option (ZMod 2 × ZMod 2) => decide (z = some (0, 0)))
      (ComputableDerivedZeroOnGrid.check_eq ρ _
        (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
        (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
        (by intro x L; simp only [FieldQueryArithmetic.edgeValue_eq,
            BooleanCoefficientRecovery.weightedCubicQuery_eq])
        nodes ζ H (flatDifference π) π.properCert (properAuxiliary π) s)
  · exact congrArg (fun z : ZMod 2 => decide (z = 0))
      (ComputableBinaryDifferenceConsistency.check_eq (by omega)
        π.color π.difference s.1.1 s.1.2 s.2)

@[simp] theorem test_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (s : Sample F n m c t) :
    test ρ nodes ζ H G π s = ThreeColorVerifier.test ρ nodes ζ H G π s := by
  apply Bool.eq_iff_iff.mpr
  simp [test, ThreeColorVerifier.test]

@[simp] theorem branchQueries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (i : Fin 7) :
    branchQueries (m := m) ρ nodes ζ H G i =
      ThreeColorVerifier.branchQueries ρ nodes ζ H G i := by
  fin_cases i <;> funext s
  · exact congrArg (List.map colorQuery)
      (ComputableEncodedLineLowDegreeTest.queries_eq (by omega) ρ nodes ζ s)
  · exact congrArg (List.map validQuery)
      (ComputableEncodedLineLowDegreeTest.queries_eq (le_refl 1) ρ nodes ζ s)
  · exact congrArg (List.map differenceQuery)
      (ComputableEncodedLineLowDegreeTest.queries_eq (by omega) ρ nodes ζ s)
  · exact congrArg (List.map properQuery)
      (ComputableEncodedLineLowDegreeTest.queries_eq (le_refl 1) ρ nodes ζ s)
  · exact congrArg (List.map validGridQuery)
      (ComputableDerivedZeroOnGrid.queries_eq ρ _
        (fun _ => HadamardDerivedOracle.cubic)
        (fun _ => HadamardDerivedOracle.natDegree_cubic_le)
        (fun _ L => BooleanCoefficientRecovery.cubicQuery_eq ρ L) nodes ζ H s)
  · exact congrArg (List.map properGridQuery)
      (ComputableDerivedZeroOnGrid.queries_eq ρ _
        (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
        (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
        (by intro x L; simp only [FieldQueryArithmetic.edgeValue_eq,
            BooleanCoefficientRecovery.weightedCubicQuery_eq]) nodes ζ H s)
  · exact congrArg (List.map differenceCheckQuery)
      (ComputableBinaryDifferenceConsistency.queries_eq (by omega) s.1.1 s.1.2 s.2)

@[simp] theorem queries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (s : Sample F n m c t) :
    queries ρ nodes ζ H G s = ThreeColorVerifier.queries ρ nodes ζ H G s := by
  simp only [queries, ThreeColorVerifier.queries, branchQueries_eq]

end PCP.Algebraic.ComputableThreeColorVerifier

namespace PCP.Algebraic.ComputableThreeColorFullFieldSampling

open ThreeColorVerifier ThreeColorFullFieldSampling

variable {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {n m c t : ℕ}

/-- Decode the four nonzero parameters, accepting immediately if any is zero. -/
def test (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (s : RawSample F n m c t) : Bool :=
  match FieldQueryArithmetic.decodeSeed s with
  | none => true
  | some a => ComputableThreeColorVerifier.test ρ nodes ζ H G π a

/-- Invalid whole-field samples make no reads. -/
def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (s : RawSample F n m c t) : List (Query F n m c t) :=
  match FieldQueryArithmetic.decodeSeed s with
  | none => []
  | some a => ComputableThreeColorVerifier.queries ρ nodes ζ H G a

@[simp] theorem test_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (π : Proof F n m c t) (s : RawSample F n m c t) :
    test ρ nodes ζ H G π s = ThreeColorFullFieldSampling.test ρ nodes ζ H G π s := by
  simp only [test, FieldQueryArithmetic.decodeSeed_eq, ThreeColorFullFieldSampling.test]
  cases decode s <;> simp

@[simp] theorem queries_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (s : RawSample F n m c t) :
    queries ρ nodes ζ H G s = ThreeColorFullFieldSampling.queries ρ nodes ζ H G s := by
  simp only [queries, FieldQueryArithmetic.decodeSeed_eq, ThreeColorFullFieldSampling.queries]
  cases decode s <;> simp

end PCP.Algebraic.ComputableThreeColorFullFieldSampling
