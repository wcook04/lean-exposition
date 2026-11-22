import PCP.Complexity.LangQueryAddressState
import PCP.Complexity.BooleanAffineList
import PCP.Algebraic.ComputableHadamardTest
import PCP.Verifier.QueryListAlgorithm

/-!
# Physical line-table sites of the standard local corrector

A site contains an actual constructor and its two outer points. Its nine fixed
numeric payload entries are exactly the production proof-address prefix.
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic ThreeColorVerifier BinaryPolynomialSpace

variable {F : Type*} {q n m t C1 C3 : ℕ}

inductive Site (F : Type*) (n : ℕ)
  | color (uv : Vertex F n × Vertex F n)
  | valid (uv : PairPoint F n × PairPoint F n)
  | difference (uv : PairPoint F n × PairPoint F n)
  | proper (uv : ProperPoint F n × ProperPoint F n)

def Site.query (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4)
    (w : Coefficients t 1) : Query F n m 4 t :=
  match s with
  | .color xy => .colorLine xy u w
  | .valid xy => .validLine xy u w
  | .difference xy => .differenceLine xy u w
  | .proper xy => .properLine xy u w

def Site.prefix (eF : F ≃ Fin q) (C1 C3 m : ℕ) (s : Site F n) : Fin 9 → ℕ :=
  match s with
  | .color xy => ![4, q^n, q^(n+n), q^((n+n)+(n+n)), q^(4*m), C1, C3,
      (ThreeColorQueryIndex.vertexIndex eF n xy.1).val,
      (ThreeColorQueryIndex.vertexIndex eF n xy.2).val]
  | .valid xy => ![5, q^n, q^(n+n), q^((n+n)+(n+n)), q^(4*m), C1, C3,
      (ThreeColorQueryIndex.pairIndex eF n xy.1).val,
      (ThreeColorQueryIndex.pairIndex eF n xy.2).val]
  | .difference xy => ![6, q^n, q^(n+n), q^((n+n)+(n+n)), q^(4*m), C1, C3,
      (ThreeColorQueryIndex.pairIndex eF n xy.1).val,
      (ThreeColorQueryIndex.pairIndex eF n xy.2).val]
  | .proper xy => ![7, q^n, q^(n+n), q^((n+n)+(n+n)), q^(4*m), C1, C3,
      (ThreeColorQueryIndex.properIndex eF n xy.1).val,
      (ThreeColorQueryIndex.properIndex eF n xy.2).val]

theorem Site.inputs_prefix (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1)
    (i : Fin 9) :
    QueryAddress.inputs eF e1 e3 (s.query u w) (i.castAdd 2) = s.prefix eF C1 C3 m i := by
  cases s <;> fin_cases i <;> rfl

theorem Site.inputs_inner (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1) :
    QueryAddress.inputs eF e1 e3 (s.query u w) 9 =
      (ThreeColorQueryIndex.innerIndex eF m 4 u).val := by cases s <;> rfl

theorem Site.inputs_label (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1) :
    QueryAddress.inputs eF e1 e3 (s.query u w) 10 = (e1 w).val := by cases s <;> rfl

/-- Flattening uses the exact inner coordinate equivalence of the production address codec. -/
def vector (u : BinaryLocalCorrection.InnerPoint F m 4) : Fin (4*m) → F :=
  u ∘ finProdFinEquiv.symm

theorem vector_index (eF : F ≃ Fin q) (u : BinaryLocalCorrection.InnerPoint F m 4) :
    finFunctionFinEquiv (fun i => eF (vector u i)) = ThreeColorQueryIndex.innerIndex eF m 4 u := rfl

section Field

variable [Field F]

theorem vector_point (u v : BinaryLocalCorrection.InnerPoint F m 4) (a : F) :
    vector (PolynomialLine.point u v a) = PolynomialLine.point (vector u) (vector v) a := rfl

/-- The actual five physical queries, retaining their constructor and their semantic order. -/
def Site.queries [Algebra (ZMod 2) F] (s : Site F n) (ζ : F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (u v : BinaryLocalCorrection.InnerPoint F m 4) (w : Fin t → ZMod 2) :
    List (Query F n m 4 t) :=
  (ComputableBinaryStandardLocalCorrection.queries 4 ζ ρ u v w).map
    (fun p => s.query p.1 p.2)

theorem Site.queries_ofFn [Algebra (ZMod 2) F] (s : Site F n) (ζ : F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (u v : BinaryLocalCorrection.InnerPoint F m 4) (w : Fin t → ZMod 2) :
    s.queries ζ ρ u v w = List.ofFn (fun i : Fin 5 =>
      s.query (PolynomialLine.point u v (ζ^(i.val+1)))
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1)
          (FieldQueryArithmetic.scaleLabel ρ (FieldQueryArithmetic.interpolationWeight
            (GeneratorLowDegreeTest.nodes 4 ζ) 0 i) w))) := by
  simp [Site.queries, ComputableBinaryStandardLocalCorrection.queries]

/-- Physical answer-history reads keep the verifier's first-occurrence precedence. -/
def Site.oracle (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (qs : List ℕ) (bs : List Bool)
    (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1) : ZMod 2 :=
  (QueryTree.answersOracle qs bs (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val).toNat

omit [Field F] in
theorem Site.oracle_val (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (qs : List ℕ) (bs : List Bool)
    (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1) :
    (s.oracle eF e1 e3 qs bs u w).val =
      (QueryTree.answersOracle qs bs
        (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val).toNat := by
  unfold Site.oracle
  cases QueryTree.answersOracle qs bs (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val <;>
    decide

end Field

end PCP.Lang.StandardCorrection
