import PCP.Complexity.StandardCorrectionSite
import PCP.Complexity.HadamardRowLocation
import PCP.Algebraic.ComputableBinaryLocalCorrection

/-!
# The four physical outer encoded-line tests

The descriptor fixes the genuine primary table, its coordinate ordering and
Hadamard degree, and the matching auxiliary line table. No address embedding is
supplied by a caller.
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic ThreeColorVerifier BinaryPolynomialSpace

inductive Kind
  | color
  | valid
  | difference
  | proper
  deriving DecidableEq

def Kind.degree : Kind → ℕ
  | .color | .difference => 3
  | .valid | .proper => 1

def Kind.Coordinates (n : ℕ) : Kind → Type
  | .color => Fin n
  | .valid | .difference => Fin n ⊕ Fin n
  | .proper => Fin (n + n) ⊕ Fin (n + n)

def Kind.dimension (n : ℕ) : Kind → ℕ
  | .color => n
  | .valid | .difference => n+n
  | .proper => (n + n)+(n + n)

def Kind.coordinateEquiv (n : ℕ) (k : Kind) : k.Coordinates n ≃ Fin (k.dimension n) :=
  match k with
  | .color => Equiv.refl _
  | .valid | .difference | .proper => finSumFinEquiv

theorem Kind.degree_pos (k : Kind) : 1 ≤ k.degree := by cases k <;> decide

theorem Kind.degree_le (k : Kind) : k.degree ≤ 3 := by cases k <;> decide

def Kind.primary {F : Type*} {n m : ℕ} (k : Kind) (x : k.Coordinates n → F) :
    HadamardRow.Location F n m 4 k.degree :=
  match k with
  | .color => .color x
  | .valid => .validCert x
  | .difference => .difference x
  | .proper => .properCert x

def Kind.line {F : Type*} {n : ℕ} (k : Kind)
    (uv : (k.Coordinates n → F) × (k.Coordinates n → F)) : StandardCorrection.Site F n :=
  match k with
  | .color => .color uv
  | .valid => .valid uv
  | .difference => .difference uv
  | .proper => .proper uv

def Kind.query {F : Type*} {n m t : ℕ} (k : Kind) :
    EncodedLineLowDegreeTest.Query F (k.Coordinates n) m 4 t k.degree → Query F n m 4 t :=
  fun q => match q with
  | .inl (x, label) => (k.primary x).query label
  | .inr (uv, x, label) => (k.line uv).query x label

theorem Kind.query_color {F : Type*} {n m t : ℕ}
    (q : EncodedLineLowDegreeTest.Query F (Fin n) m 4 t 3) :
    Kind.color.query q = ThreeColorVerifier.colorQuery q := by cases q <;> rfl

theorem Kind.query_valid {F : Type*} {n m t : ℕ}
    (q : EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m 4 t 1) :
    Kind.valid.query q = ThreeColorVerifier.validQuery q := by cases q <;> rfl

theorem Kind.query_difference {F : Type*} {n m t : ℕ}
    (q : EncodedLineLowDegreeTest.Query F (Fin n ⊕ Fin n) m 4 t 3) :
    Kind.difference.query q = ThreeColorVerifier.differenceQuery q := by cases q <;> rfl

theorem Kind.query_proper {F : Type*} {n m t : ℕ}
    (q : EncodedLineLowDegreeTest.Query F (Fin (n + n) ⊕ Fin (n + n)) m 4 t 1) :
    Kind.proper.query q = ThreeColorVerifier.properQuery q := by cases q <;> rfl

def Kind.vector {F : Type*} {n : ℕ} (k : Kind) (x : k.Coordinates n → F) :
    Fin (k.dimension n) → F := x ∘ (k.coordinateEquiv n).symm

theorem Kind.vector_point {F : Type*} [Field F] {n : ℕ} (k : Kind)
    (u v : k.Coordinates n → F) (z : F) :
    k.vector (PolynomialLine.point u v z) =
      PolynomialLine.point (k.vector u) (k.vector v) z := rfl

/-- Numeric coordinate code used by the actual primary table address. -/
def Kind.pointCode {F : Type*} {n q : ℕ} (k : Kind) (eF : F ≃ Fin q)
    (x : k.Coordinates n → F) : ℕ := (finFunctionFinEquiv (eF ∘ k.vector x)).val

theorem Kind.primary_pointCode {F : Type*} {n m t q : ℕ} (k : Kind)
    (eF : F ≃ Fin q) (x : k.Coordinates n → F) :
    (k.primary (m := m) x).payload (t := t) eF 7 = k.pointCode eF x := by
  cases k <;> rfl

/-- The exact physical query list of the original outer test, for each of its four constructors. -/
def Kind.queries {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {n m t : ℕ} (k : Kind) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin 5 → F) (ζ : F)
    (s : EncodedLineLowDegreeTest.Sample F (k.Coordinates n) m 4 t k.degree) :
    List (Query F n m 4 t) :=
  (ComputableEncodedLineLowDegreeTest.queries k.degree_pos ρ nodes ζ s).map k.query

theorem Kind.queries_parts {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {n m t : ℕ} (k : Kind) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin 5 → F) (ζ : F)
    (s : EncodedLineLowDegreeTest.Sample F (k.Coordinates n) m 4 t k.degree) :
    k.queries ρ nodes ζ s =
      (ComputableHadamardTest.queries k.degree_pos s.2.2.2.1).map (k.primary s.1.1).query ++
      (ComputableBinaryLowDegreeTest.queries (le_refl 1) ρ nodes s.2.2.2.2).map
        (fun p => (k.line s.1).query p.1 p.2) ++
      (k.line s.1).queries ζ ρ (SetMultilinear.evaluationPoint m 4 s.2.1)
        s.2.2.1.1 s.2.2.1.2 ++
      [(k.primary (PolynomialLine.point s.1.1 s.1.2 s.2.1)).query
        (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2)] := by
  simp only [Kind.queries, ComputableEncodedLineLowDegreeTest.queries, List.map_append,
    List.map_map, List.map_singleton, StandardCorrection.Site.queries]
  rfl

end PCP.Lang.OuterBranch
