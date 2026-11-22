import PCP.Complexity.DerivedCallLang
import PCP.Algebraic.ComputableThreeColorVerifier

/-!
# The two actual derived-grid sites and their complete physical query traces

The valid constraint reads the color table. The proper constraint reads the
flattened difference table. Both certificate calls retain their original point,
independent seed, shared line table and fresh coefficient mask.
-/

namespace PCP.Lang.DerivedGrid

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def baseDimension (k : Certificate) (n : ℕ) : ℕ :=
  match k with
  | .valid => n
  | .proper => n+n

def weighted : Certificate → Bool
  | .valid => false
  | .proper => true

abbrev Sample (k : Certificate) (t n m : ℕ) [NeZero t] :=
  DerivedZeroOnGrid.TestSample (OuterBranch.Field t) (baseDimension k n) m 4 t 3

abbrev RawSample (k : Certificate) (t n m : ℕ) [NeZero t] :=
  ThreeColorFullFieldSampling.RawDerivedSample (OuterBranch.Field t) (baseDimension k n) m 4 t 3

def certificatePoint (k : Certificate)
    (x : BinaryZeroOnGridCorrection.CertificatePoint (OuterBranch.Field t) (baseDimension k n)) :
    k.Point t n := by cases k <;> exact x

def certificateSeed (k : Certificate)
    (s : BinaryZeroOnGridCorrection.CallSeed (OuterBranch.Field t)
      (Fin (baseDimension k n) ⊕ Fin (baseDimension k n)) m 4 t) : k.Seed t n m := by
  cases k <;> exact s

def firstPoint (k : Certificate) (s : Sample k t n m) : k.Point t n :=
  certificatePoint k (BinaryZeroOnGrid.zeroPoint s.1)

def secondPoint (k : Certificate) (H : Finset (OuterBranch.Field t)) (s : Sample k t n m) :
    k.Point t n := certificatePoint k (FieldQueryArithmetic.recoveryPoint H s.1)

def firstSeed (k : Certificate) (s : Sample k t n m) : k.Seed t n m := certificateSeed k s.2.1.2.1

def secondSeed (k : Certificate) (s : Sample k t n m) : k.Seed t n m := certificateSeed k s.2.1.2.2

def primaryLocation (k : Certificate) (x : Fin (baseDimension k n) → OuterBranch.Field t) :
    HadamardRow.Location (OuterBranch.Field t) n m 4 3 := by
  cases k with
  | valid => exact .color x
  | proper => exact .difference (x ∘ ThreeColorVerifier.flatten n)

def physical (k : Certificate) :
    DerivedZeroOnGrid.Query (OuterBranch.Field t) (baseDimension k n) m 4 t 3 →
      ThreeColorVerifier.Query (OuterBranch.Field t) n m 4 t := by
  cases k with
  | valid => exact ThreeColorVerifier.validGridQuery
  | proper => exact ThreeColorVerifier.properGridQuery

def transform (k : Certificate) (weight : OuterBranch.Field t) :
    (Fin (baseDimension k n) → OuterBranch.Field t) → Coefficients t 1 → Coefficients t 3 :=
  fun _ => BinaryCubicQueryLang.translated (weighted k) weight

def queries (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : Sample k t n m) : List ℕ :=
  (ComputableDerivedZeroOnGrid.queries (BinaryMaterializedField.coordinates t)
    (transform k weight) nodes ζ H s).map (fun q => queryCode (physical k q))

/-- The three executed segments are exactly the named derived-grid query list. -/
theorem queries_parts (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : Sample k t n m) :
    queries k nodes ζ H weight s =
      DerivedCall.primaryQueries (weighted k) weight s.2.1.1 s.2.2
        (primaryLocation (m := m) k s.1) ++
      DerivedCall.callQueries k nodes ζ (firstPoint k s) s.2.1.1 (firstSeed k s) ++
      DerivedCall.callQueries k nodes ζ (secondPoint k H s) s.2.1.1 (secondSeed k s) := by
  cases k <;>
    simp only [queries, ComputableDerivedZeroOnGrid.queries, DerivedCall.primaryQueries,
      DerivedCall.callQueries, ComputableDerivedZeroOnGrid.callQueries, firstPoint, secondPoint,
      firstSeed, secondSeed, certificatePoint, certificateSeed, primaryLocation, physical,
      transform, DerivedCall.primaryLabel, List.map_append, List.map_cons, List.map_nil,
      List.map_map, Function.comp_def]
  all_goals rfl

end PCP.Lang.DerivedGrid
