/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.EncodedLineLowDegreeTest
import PCP.Algebraic.DerivedZeroOnGridSoundness
import PCP.Algebraic.ThreeColorGrid
import PCP.Algebraic.GridCoordinateTransport
import PCP.Algebraic.FiniteConjunction

/-!
# The concrete seven-check algebraic three-color verifier

Four encoded-line low-degree tests, two derived zero-on-grid tests, and one
binary difference check share eight physical received tables. In particular each
certificate's encoded line table is shared between its low-degree test and the
local correction calls. The proper-constraint branch flattens the two vertex
coordinate blocks; its edge polynomial is public input, not a proof table.

All seven checks run on independent finite seeds. The query list certifies
`20*c+107` bit reads. This is a finite-sampling verifier, without a running-time
or uniform-bit-sampling claim.
-/

namespace PCP.Algebraic.ThreeColorVerifier

open Finset MvPolynomial BinaryPolynomialSpace Hadamard

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n m c t : ℕ}

abbrev Vertex (F : Type*) (n : ℕ) := Fin n → F
abbrev PairPoint (F : Type*) (n : ℕ) := (Fin n ⊕ Fin n) → F
abbrev ProperPoint (F : Type*) (n : ℕ) := (Fin (n + n) ⊕ Fin (n + n)) → F

/-- The four primary tables and their four shared encoded-line tables. -/
structure Proof (F : Type*) (n m c t : ℕ) where
  color : Vertex F n → Coefficients t 3 → ZMod 2
  validCert : PairPoint F n → Coefficients t 1 → ZMod 2
  difference : PairPoint F n → Coefficients t 3 → ZMod 2
  properCert : ProperPoint F n → Coefficients t 1 → ZMod 2
  colorLines : EncodedLineLowDegreeTest.Auxiliary F (Fin n) m c t
  validLines : EncodedLineLowDegreeTest.Auxiliary F (Fin n ⊕ Fin n) m c t
  differenceLines : EncodedLineLowDegreeTest.Auxiliary F (Fin n ⊕ Fin n) m c t
  properLines : EncodedLineLowDegreeTest.Auxiliary F (Fin (n + n) ⊕ Fin (n + n)) m c t

/-- The exact coordinate flattening used only by the proper-constraint branch. -/
def flatten (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv

/-- The public adjacency extension, on the flattened pair of vertex coordinates. -/
noncomputable def edgePolynomial (H : Finset F) (G : SimpleGraph (Fin n → H)) :
    MvPolynomial (Fin (n + n)) F := by
  classical
  exact rename (flatten n) (ThreeColorGrid.edgeExtension H G)

/-- Evaluate public adjacency at the original two vertex blocks. -/
noncomputable def edgeValue (H : Finset F) (G : SimpleGraph (Fin n → H))
    (x : Fin (n + n) → F) : F := by
  classical
  exact eval (x ∘ flatten n) (ThreeColorGrid.edgeExtension H G)

omit [Algebra (ZMod 2) F] in
@[simp] theorem edgeValue_eq_eval (H : Finset F) (G : SimpleGraph (Fin n → H))
    (x : Fin (n + n) → F) : edgeValue H G x = eval x (edgePolynomial H G) := by
  classical
  exact (MvPolynomial.eval_rename (flatten n) x (ThreeColorGrid.edgeExtension H G)).symm

/-- View the same difference oracle on flattened coordinates. -/
def flatDifference (π : Proof F n m c t) :
    (Fin (n + n) → F) → Coefficients t 3 → ZMod 2 :=
  GridCoordinateTransport.rows (flatten n) π.difference

/-- The local corrector uses the same valid-certificate line table as its outer test. -/
def validAuxiliary (π : Proof F n m c t) : BinaryZeroOnGridCorrection.Auxiliary F n m c t :=
  fun a b => π.validLines (a, b)

/-- Likewise for the proper certificate, after flattening the constraint coordinates. -/
def properAuxiliary (π : Proof F n m c t) :
    BinaryZeroOnGridCorrection.Auxiliary F (n + n) m c t :=
  fun a b => π.properLines (a, b)

/-- Branch order: color, valid certificate, difference, proper certificate,
valid grid, proper grid, difference consistency. -/
def BranchSeed (F : Type*) [Monoid F] (n m c t : ℕ) : Fin 7 → Type _ :=
  ![EncodedLineLowDegreeTest.Sample F (Fin n) m c t 3,
    EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 1,
    EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 3,
    EncodedLineLowDegreeTest.Sample F (Fin (n + n) ⊕ Fin (n + n)) m c t 1,
    DerivedZeroOnGrid.TestSample F n m c t 3,
    DerivedZeroOnGrid.TestSample F (n + n) m c t 3,
    ((Vertex F n × Vertex F n) × (Fin t → ZMod 2))]

abbrev Sample (F : Type*) [Monoid F] (n m c t : ℕ) :=
  (i : Fin 7) → BranchSeed F n m c t i

/-- The seven concrete branch verdicts. -/
noncomputable def branchTest (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (i : Fin 7) : BranchSeed F n m c t i → Bool := by
  classical
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact EncodedLineLowDegreeTest.test (by omega) ρ nodes ζ π.color π.colorLines
  · exact EncodedLineLowDegreeTest.test (le_refl 1) ρ nodes ζ π.validCert π.validLines
  · exact EncodedLineLowDegreeTest.test (by omega) ρ nodes ζ π.difference π.differenceLines
  · exact EncodedLineLowDegreeTest.test (le_refl 1) ρ nodes ζ π.properCert π.properLines
  · exact fun s => decide (DerivedZeroOnGrid.check ρ (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H π.color π.validCert
      (validAuxiliary π) s = some (0, 0))
  · exact fun s => decide (DerivedZeroOnGrid.check ρ
      (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
      nodes ζ H (flatDifference π) π.properCert (properAuxiliary π) s = some (0, 0))
  · exact fun s => decide (BinaryDifferenceConsistency.check (by omega)
      π.color π.difference s.1.1 s.1.2 s.2 = 0)

/-- All seven branches must accept. -/
noncomputable def test (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) : Sample F n m c t → Bool :=
  FiniteConjunction.test (branchTest ρ nodes ζ H G π)

/-- An actual query to one of the eight physical tables. -/
inductive Query (F : Type*) (n m c t : ℕ) where
  | color : Vertex F n → Coefficients t 3 → Query F n m c t
  | validCert : PairPoint F n → Coefficients t 1 → Query F n m c t
  | difference : PairPoint F n → Coefficients t 3 → Query F n m c t
  | properCert : ProperPoint F n → Coefficients t 1 → Query F n m c t
  | colorLine : (Vertex F n × Vertex F n) → BinaryLocalCorrection.InnerPoint F m c →
      Coefficients t 1 → Query F n m c t
  | validLine : (PairPoint F n × PairPoint F n) → BinaryLocalCorrection.InnerPoint F m c →
      Coefficients t 1 → Query F n m c t
  | differenceLine : (PairPoint F n × PairPoint F n) → BinaryLocalCorrection.InnerPoint F m c →
      Coefficients t 1 → Query F n m c t
  | properLine : (ProperPoint F n × ProperPoint F n) → BinaryLocalCorrection.InnerPoint F m c →
      Coefficients t 1 → Query F n m c t

/-- A physical query is answered by precisely its tagged received table. -/
def read (π : Proof F n m c t) : Query F n m c t → ZMod 2
  | .color x q => π.color x q
  | .validCert x q => π.validCert x q
  | .difference x q => π.difference x q
  | .properCert x q => π.properCert x q
  | .colorLine uv x q => π.colorLines uv x q
  | .validLine uv x q => π.validLines uv x q
  | .differenceLine uv x q => π.differenceLines uv x q
  | .properLine uv x q => π.properLines uv x q

/-- Embedding the primary-color low-degree test's queries. -/
def colorQuery : EncodedLineLowDegreeTest.Query F (Fin n) m c t 3 → Query F n m c t
  | .inl (x, q) => .color x q
  | .inr (uv, x, q) => .colorLine uv x q

def validQuery : EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m c t 1 → Query F n m c t
  | .inl (x, q) => .validCert x q
  | .inr (uv, x, q) => .validLine uv x q

def differenceQuery :
    EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m c t 3 → Query F n m c t
  | .inl (x, q) => .difference x q
  | .inr (uv, x, q) => .differenceLine uv x q

def properQuery :
    EncodedLineLowDegreeTest.Query F (Fin (n + n) ⊕ Fin (n + n)) m c t 1 → Query F n m c t
  | .inl (x, q) => .properCert x q
  | .inr (uv, x, q) => .properLine uv x q

/-- Correction queries are routed to the same physical certificate and line tables. -/
def validGridQuery : DerivedZeroOnGrid.Query F n m c t 3 → Query F n m c t
  | .inl (x, q) => .color x q
  | .inr (_, .inl (x, q)) => .validCert x q
  | .inr (a, .inr (b, x, q)) => .validLine (a, b) x q

/-- Only the difference-table point is pulled back through the coordinate equivalence. -/
def properGridQuery : DerivedZeroOnGrid.Query F (n + n) m c t 3 → Query F n m c t
  | .inl (x, q) => .difference (x ∘ flatten n) q
  | .inr (_, .inl (x, q)) => .properCert x q
  | .inr (a, .inr (b, x, q)) => .properLine (a, b) x q

def differenceCheckQuery : BinaryDifferenceConsistency.Query F (Fin n) t 3 → Query F n m c t
  | .inl (x, q) => .color x q
  | .inr (x, q) => .difference x q

/-- Every branch's list is mapped to physical proof-table locations. -/
noncomputable def branchQueries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (i : Fin 7) : BranchSeed F n m c t i → List (Query F n m c t) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact fun s => (EncodedLineLowDegreeTest.queries (by omega) ρ nodes ζ s).map colorQuery
  · exact fun s => (EncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map validQuery
  · exact fun s => (EncodedLineLowDegreeTest.queries (by omega) ρ nodes ζ s).map differenceQuery
  · exact fun s => (EncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map properQuery
  · exact fun s => (DerivedZeroOnGrid.queries ρ (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H s).map validGridQuery
  · exact fun s => (DerivedZeroOnGrid.queries ρ
      (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
      nodes ζ H s).map properGridQuery
  · exact fun s => (BinaryDifferenceConsistency.queries (by omega) s.1.1 s.1.2 s.2).map
      differenceCheckQuery

/-- The verifier performs every listed branch, so its complete list concatenates all seven. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : Sample F n m c t) : List (Query F n m c t) :=
  (List.ofFn (fun i : Fin 7 => branchQueries ρ nodes ζ H G i (s i))).flatten

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_colorQuery (π : Proof F n m c t)
    (q : EncodedLineLowDegreeTest.Query F (Fin n) m c t 3) :
    read π (colorQuery q) = EncodedLineLowDegreeTest.read π.color π.colorLines q := by
  cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_validQuery (π : Proof F n m c t)
    (q : EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m c t 1) :
    read π (validQuery q) = EncodedLineLowDegreeTest.read π.validCert π.validLines q := by
  cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_differenceQuery (π : Proof F n m c t)
    (q : EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m c t 3) :
    read π (differenceQuery q) =
      EncodedLineLowDegreeTest.read π.difference π.differenceLines q := by
  cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_properQuery (π : Proof F n m c t)
    (q : EncodedLineLowDegreeTest.Query F (Fin (n + n) ⊕ Fin (n + n)) m c t 1) :
    read π (properQuery q) = EncodedLineLowDegreeTest.read π.properCert π.properLines q := by
  cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_validGridQuery (π : Proof F n m c t)
    (q : DerivedZeroOnGrid.Query F n m c t 3) :
    read π (validGridQuery q) =
      DerivedZeroOnGrid.read π.color π.validCert (validAuxiliary π) q := by
  rcases q with q | ⟨a, q⟩
  · rfl
  · cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_properGridQuery (π : Proof F n m c t)
    (q : DerivedZeroOnGrid.Query F (n + n) m c t 3) :
    read π (properGridQuery q) =
      DerivedZeroOnGrid.read (flatDifference π) π.properCert (properAuxiliary π) q := by
  rcases q with q | ⟨a, q⟩
  · rfl
  · cases q <;> rfl

omit [Field F] [Algebra (ZMod 2) F] in
@[simp] private theorem read_differenceCheckQuery (π : Proof F n m c t)
    (q : BinaryDifferenceConsistency.Query F (Fin n) t 3) :
    read π (differenceCheckQuery q) = BinaryDifferenceConsistency.read π.color π.difference q := by
  cases q <;> rfl

/-- Every branch uses only its own mapped physical query list. -/
theorem branchTest_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π π' : Proof F n m c t) (i : Fin 7) (s : BranchSeed F n m c t i)
    (h : ∀ q ∈ branchQueries ρ nodes ζ H G i s, read π q = read π' q) :
    branchTest ρ nodes ζ H G π i s = branchTest ρ nodes ζ H G π' i s := by
  classical
  fin_cases i
  · apply EncodedLineLowDegreeTest.test_congr
    intro q hq
    simpa only [read_colorQuery] using h (colorQuery q) (List.mem_map_of_mem hq)
  · apply EncodedLineLowDegreeTest.test_congr
    intro q hq
    simpa only [read_validQuery] using h (validQuery q) (List.mem_map_of_mem hq)
  · apply EncodedLineLowDegreeTest.test_congr
    intro q hq
    simpa only [read_differenceQuery] using h (differenceQuery q) (List.mem_map_of_mem hq)
  · apply EncodedLineLowDegreeTest.test_congr
    intro q hq
    simpa only [read_properQuery] using h (properQuery q) (List.mem_map_of_mem hq)
  · apply congrArg (fun b : Option (ZMod 2 × ZMod 2) => decide (b = some (0, 0)))
    apply DerivedZeroOnGrid.check_congr
    intro q hq
    simpa only [read_validGridQuery] using h (validGridQuery q) (List.mem_map_of_mem hq)
  · apply congrArg (fun b : Option (ZMod 2 × ZMod 2) => decide (b = some (0, 0)))
    apply DerivedZeroOnGrid.check_congr
    intro q hq
    simpa only [read_properGridQuery] using h (properGridQuery q) (List.mem_map_of_mem hq)
  · apply congrArg (fun b : ZMod 2 => decide (b = 0))
    apply BinaryDifferenceConsistency.check_congr
    intro q hq
    simpa only [read_differenceCheckQuery] using
      h (differenceCheckQuery q) (List.mem_map_of_mem hq)

/-- Each branch's physical queries occur in the complete list. -/
theorem mem_queries_of_branch (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : Sample F n m c t) (i : Fin 7) {q : Query F n m c t}
    (hq : q ∈ branchQueries ρ nodes ζ H G i (s i)) : q ∈ queries ρ nodes ζ H G s := by
  apply List.mem_flatten.mpr
  exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hq⟩

/-- The complete verifier is determined by its stated physical oracle reads. -/
theorem test_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π π' : Proof F n m c t) (s : Sample F n m c t)
    (h : ∀ q ∈ queries ρ nodes ζ H G s, read π q = read π' q) :
    test ρ nodes ζ H G π s = test ρ nodes ζ H G π' s := by
  apply FiniteConjunction.test_congr
  intro i
  exact branchTest_congr ρ nodes ζ H G π π' i (s i)
    (fun _ hq => h _ (mem_queries_of_branch ρ nodes ζ H G s i hq))

/-- The combined verdict is exactly conjunction of the seven concrete verdicts. -/
theorem test_eq_true (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (s : Sample F n m c t) :
    test ρ nodes ζ H G π s = true ↔ ∀ i, branchTest ρ nodes ζ H G π i (s i) = true :=
  FiniteConjunction.test_eq_true _ _

/-- Per-branch query budgets in the same order as `BranchSeed`. -/
def branchQueryBound (c : ℕ) : Fin 7 → ℕ :=
  ![2 * c + 18, 2 * c + 14, 2 * c + 18, 2 * c + 14, 6 * c + 20, 6 * c + 20, 3]

/-- Each concrete branch has the claimed count, including fresh derived-read seeds. -/
theorem branchQueries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (i : Fin 7) (s : BranchSeed F n m c t i) :
    (branchQueries ρ nodes ζ H G i s).length ≤ branchQueryBound c i := by
  fin_cases i
  · change ((EncodedLineLowDegreeTest.queries (by omega : 1 ≤ 3) ρ nodes ζ s).map
      colorQuery).length ≤ 2 * c + 18
    rw [List.length_map]
    have h := EncodedLineLowDegreeTest.queries_length_le (by omega : 1 ≤ 3) ρ nodes ζ s
    omega
  · change ((EncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map
      validQuery).length ≤ 2 * c + 14
    rw [List.length_map]
    have h := EncodedLineLowDegreeTest.queries_length_le (le_refl 1) ρ nodes ζ s
    omega
  · change ((EncodedLineLowDegreeTest.queries (by omega : 1 ≤ 3) ρ nodes ζ s).map
      differenceQuery).length ≤ 2 * c + 18
    rw [List.length_map]
    have h := EncodedLineLowDegreeTest.queries_length_le (by omega : 1 ≤ 3) ρ nodes ζ s
    omega
  · change ((EncodedLineLowDegreeTest.queries (le_refl 1) ρ nodes ζ s).map
      properQuery).length ≤ 2 * c + 14
    rw [List.length_map]
    have h := EncodedLineLowDegreeTest.queries_length_le (le_refl 1) ρ nodes ζ s
    omega
  · change ((DerivedZeroOnGrid.queries ρ (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H s).map
        validGridQuery).length ≤ 6 * c + 20
    rw [List.length_map]
    exact DerivedZeroOnGrid.queries_length_le ρ _ _ nodes ζ H s
  · change ((DerivedZeroOnGrid.queries ρ
      (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
      nodes ζ H s).map properGridQuery).length ≤ 6 * c + 20
    rw [List.length_map]
    exact DerivedZeroOnGrid.queries_length_le ρ _ _ nodes ζ H s
  · rfl

/-- The complete list certifies a constant number of bit queries for fixed `c`. -/
theorem queries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : Sample F n m c t) : (queries ρ nodes ζ H G s).length ≤ 20 * c + 107 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => branchQueries_length_le ρ nodes ζ H G i (s i))
  simp [queries, branchQueryBound, Fin.sum_univ_succ] at h ⊢
  omega

section Finite

variable [Fintype F] [DecidableEq F]

local instance : Fintype (BinaryLocalCorrection.InnerPoint F m c) := inferInstance
local instance : Fintype (BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance {r : ℕ} : Fintype
    (Hadamard.TestRandomness t r × BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance {σ : Type*} [Fintype σ] [DecidableEq σ] {r : ℕ} :
    Fintype (EncodedLineLowDegreeTest.Sample F σ m c t r) := inferInstance
local instance {σ : Type*} [Fintype σ] [DecidableEq σ] :
    Fintype (BinaryZeroOnGridCorrection.CallSeed F σ m c t) := inferInstance
local instance {k : ℕ} : Fintype (DerivedZeroOnGrid.GridRandomness F k m c t) := inferInstance
local instance {k r : ℕ} : Fintype (DerivedZeroOnGrid.TestSample F k m c t r) := inferInstance

local instance : Nonempty (BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance {σ : Type*} :
    Nonempty (BinaryZeroOnGridCorrection.CallSeed F σ m c t) := inferInstance
local instance {k : ℕ} : Nonempty (DerivedZeroOnGrid.GridRandomness F k m c t) := inferInstance
local instance {k r : ℕ} : Nonempty (DerivedZeroOnGrid.TestSample F k m c t r) := inferInstance

/-- Each branch has its genuine finite uniform sample space. -/
noncomputable instance branchSeedFintype (i : Fin 7) : Fintype (BranchSeed F n m c t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  all_goals dsimp [BranchSeed]; infer_instance

/-- No branch loses its normalized marginal through an empty independent seed. -/
instance branchSeedNonempty (i : Fin 7) : Nonempty (BranchSeed F n m c t i) := by
  fin_cases i <;> dsimp [BranchSeed] <;> infer_instance

/-- Exact normalized rejection of the seven-check finite verifier. -/
noncomputable def rejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) : ℚ :=
  FiniteConjunction.rejectionRate (branchTest ρ nodes ζ H G π)

/-- The normalized rejection of one concrete branch on its own seed. -/
noncomputable def branchRejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (i : Fin 7) : ℚ :=
  relativeDistance (branchTest ρ nodes ζ H G π i) (fun _ => true)

theorem rejectionRate_nonneg (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) : 0 ≤ rejectionRate ρ nodes ζ H G π :=
  FiniteConjunction.rejectionRate_nonneg _

/-- Every actual branch rate is bounded by the combined rate, with no branch factor. -/
theorem branchRejectionRate_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (i : Fin 7) :
    branchRejectionRate ρ nodes ζ H G π i ≤ rejectionRate ρ nodes ζ H G π :=
  FiniteConjunction.branch_rejection_le _ i

@[simp] theorem branchRejectionRate_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 0 =
      EncodedLineLowDegreeTest.rejectionRate (by omega) ρ nodes ζ π.color π.colorLines := rfl

@[simp] theorem branchRejectionRate_one (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 1 =
      EncodedLineLowDegreeTest.rejectionRate (le_refl 1) ρ nodes ζ π.validCert π.validLines := rfl

@[simp] theorem branchRejectionRate_two (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 2 =
      EncodedLineLowDegreeTest.rejectionRate (by omega) ρ nodes ζ
        π.difference π.differenceLines := rfl

@[simp] theorem branchRejectionRate_three (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 3 =
      EncodedLineLowDegreeTest.rejectionRate (le_refl 1) ρ nodes ζ π.properCert π.properLines := rfl

@[simp] theorem branchRejectionRate_four (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 4 =
      DerivedZeroOnGrid.rejectionRate ρ (fun _ => HadamardDerivedOracle.cubic)
        (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H π.color π.validCert
        (validAuxiliary π) := by
  classical
  exact FiniteConjunction.distance_decide_eq _ _

@[simp] theorem branchRejectionRate_five (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 5 =
      DerivedZeroOnGrid.rejectionRate ρ
        (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
        (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
        nodes ζ H (flatDifference π) π.properCert (properAuxiliary π) := by
  classical
  exact FiniteConjunction.distance_decide_eq _ _

@[simp] theorem branchRejectionRate_six (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    branchRejectionRate ρ nodes ζ H G π 6 =
      BinaryDifferenceConsistency.rejectionRate (by omega) π.color π.difference := by
  classical
  exact (FiniteConjunction.distance_decide_eq
    (fun s : (Vertex F n × Vertex F n) × (Fin t → ZMod 2) =>
      BinaryDifferenceConsistency.check (by omega) π.color π.difference s.1.1 s.1.2 s.2) 0).trans
    (BinaryDifferenceConsistency.rejectionRate_eq_check_distance
      (by omega) π.color π.difference).symm

end Finite

end PCP.Algebraic.ThreeColorVerifier
