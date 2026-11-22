/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorOracle
import Mathlib.Algebra.BigOperators.Fin

/-!
# Explicit mixed-radix indexing of the eight physical proof tables

The eight query constructors are mapped to a balanced tagged sum. Field tuples,
products and sums are then encoded with the standard explicit finite arithmetic
equivalences. This gives an actual address codec relative to supplied codecs for
field elements and degree-one/degree-three coefficient vectors. There is no
chosen finite enumeration of the query type and no efficiency claim about the
supplied field codec.
-/

namespace PCP.Algebraic.ThreeColorQueryIndex

open BinaryPolynomialSpace ThreeColorVerifier

variable {F : Type*} {n m c t q C1 C3 : ℕ}

/-- The exact number of physical bit addresses, arranged by the four primary
tables and four auxiliary line tables. -/
def addressLength (q n m c C1 C3 : ℕ) : ℕ :=
  (q ^ n + q ^ (n + n)) * C3 +
    (q ^ (n + n) + q ^ ((n + n) + (n + n))) * C1 +
    ((q ^ n) ^ 2 + 2 * (q ^ (n + n)) ^ 2 +
      (q ^ ((n + n) + (n + n))) ^ 2) * q ^ (c * m) * C1

abbrev PrimaryPayload (F : Type*) (n t : ℕ) :=
  ((Vertex F n × Coefficients t 3) ⊕ (PairPoint F n × Coefficients t 1)) ⊕
    ((PairPoint F n × Coefficients t 3) ⊕ (ProperPoint F n × Coefficients t 1))

abbrev LinePayload (F : Type*) (n m c t : ℕ) :=
  (((Vertex F n × Vertex F n) × (BinaryLocalCorrection.InnerPoint F m c ×
      Coefficients t 1)) ⊕
    ((PairPoint F n × PairPoint F n) × (BinaryLocalCorrection.InnerPoint F m c ×
      Coefficients t 1))) ⊕
  (((PairPoint F n × PairPoint F n) × (BinaryLocalCorrection.InnerPoint F m c ×
      Coefficients t 1)) ⊕
    ((ProperPoint F n × ProperPoint F n) × (BinaryLocalCorrection.InnerPoint F m c ×
      Coefficients t 1)))

/-- An explicit, balanced eight-way sum in constructor order. -/
abbrev Payload (F : Type*) (n m c t : ℕ) :=
  PrimaryPayload F n t ⊕ LinePayload F n m c t

def toPayload : Query F n m c t → Payload F n m c t
  | .color x z => .inl (.inl (.inl (x, z)))
  | .validCert x z => .inl (.inl (.inr (x, z)))
  | .difference x z => .inl (.inr (.inl (x, z)))
  | .properCert x z => .inl (.inr (.inr (x, z)))
  | .colorLine uv x z => .inr (.inl (.inl (uv, (x, z))))
  | .validLine uv x z => .inr (.inl (.inr (uv, (x, z))))
  | .differenceLine uv x z => .inr (.inr (.inl (uv, (x, z))))
  | .properLine uv x z => .inr (.inr (.inr (uv, (x, z))))

def ofPayload : Payload F n m c t → Query F n m c t
  | .inl (.inl (.inl (x, z))) => .color x z
  | .inl (.inl (.inr (x, z))) => .validCert x z
  | .inl (.inr (.inl (x, z))) => .difference x z
  | .inl (.inr (.inr (x, z))) => .properCert x z
  | .inr (.inl (.inl (uv, (x, z)))) => .colorLine uv x z
  | .inr (.inl (.inr (uv, (x, z)))) => .validLine uv x z
  | .inr (.inr (.inl (uv, (x, z)))) => .differenceLine uv x z
  | .inr (.inr (.inr (uv, (x, z)))) => .properLine uv x z

/-- Constructor matching, with no generated proxy or finite enumeration. -/
def payloadEquiv : Query F n m c t ≃ Payload F n m c t where
  toFun := toPayload
  invFun := ofPayload
  left_inv z := by cases z <;> rfl
  right_inv z := by
    rcases z with ((z | z) | (z | z)) | ((z | z) | (z | z))
    all_goals rfl

/-- Concatenate two coded blocks using the explicit finite sum codec. -/
def sumIndex {A B : Type*} {a b : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) := (Equiv.sumCongr eA eB).trans finSumFinEquiv

/-- Encode two coordinates by the explicit mixed-radix product codec. -/
def prodIndex {A B : Type*} {a b : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) :
    A × B ≃ Fin (a * b) := (Equiv.prodCongr eA eB).trans finProdFinEquiv

/-- Encode a field tuple after an explicit coordinate reindexing. -/
def tupleIndex {σ : Type*} {d : ℕ} (eσ : σ ≃ Fin d) (eF : F ≃ Fin q) :
    (σ → F) ≃ Fin (q ^ d) := (Equiv.arrowCongr eσ eF).trans finFunctionFinEquiv

def vertexIndex (eF : F ≃ Fin q) (n : ℕ) : Vertex F n ≃ Fin (q ^ n) :=
  tupleIndex (Equiv.refl _) eF

def pairIndex (eF : F ≃ Fin q) (n : ℕ) : PairPoint F n ≃ Fin (q ^ (n + n)) :=
  tupleIndex finSumFinEquiv eF

def properIndex (eF : F ≃ Fin q) (n : ℕ) :
    ProperPoint F n ≃ Fin (q ^ ((n + n) + (n + n))) :=
  tupleIndex finSumFinEquiv eF

def innerIndex (eF : F ≃ Fin q) (m c : ℕ) :
    BinaryLocalCorrection.InnerPoint F m c ≃ Fin (q ^ (c * m)) :=
  tupleIndex finProdFinEquiv eF

private def taggedLength (q n m c C1 C3 : ℕ) : ℕ :=
  ((q ^ n * C3 + q ^ (n + n) * C1) +
      (q ^ (n + n) * C3 + q ^ ((n + n) + (n + n)) * C1)) +
    (((q ^ n * q ^ n) * (q ^ (c * m) * C1) +
        (q ^ (n + n) * q ^ (n + n)) * (q ^ (c * m) * C1)) +
      ((q ^ (n + n) * q ^ (n + n)) * (q ^ (c * m) * C1) +
        (q ^ ((n + n) + (n + n)) * q ^ ((n + n) + (n + n))) *
          (q ^ (c * m) * C1)))

private theorem taggedLength_eq (q n m c C1 C3 : ℕ) :
    taggedLength q n m c C1 C3 = addressLength q n m c C1 C3 := by
  unfold taggedLength addressLength
  ring

private def payloadIndex (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3) :
    Payload F n m c t ≃ Fin (taggedLength q n m c C1 C3) :=
  sumIndex
    (sumIndex
      (sumIndex (prodIndex (vertexIndex eF n) e3) (prodIndex (pairIndex eF n) e1))
      (sumIndex (prodIndex (pairIndex eF n) e3) (prodIndex (properIndex eF n) e1)))
    (sumIndex
      (sumIndex
        (prodIndex (prodIndex (vertexIndex eF n) (vertexIndex eF n))
          (prodIndex (innerIndex eF m c) e1))
        (prodIndex (prodIndex (pairIndex eF n) (pairIndex eF n))
          (prodIndex (innerIndex eF m c) e1)))
      (sumIndex
        (prodIndex (prodIndex (pairIndex eF n) (pairIndex eF n))
          (prodIndex (innerIndex eF m c) e1))
        (prodIndex (prodIndex (properIndex eF n) (properIndex eF n))
          (prodIndex (innerIndex eF m c) e1))))

/-- The actual constructor-based address codec, relative to the supplied component codecs. -/
def equiv (eF : F ≃ Fin q) (e1 : Coefficients t 1 ≃ Fin C1)
    (e3 : Coefficients t 3 ≃ Fin C3) :
    Query F n m c t ≃ Fin (addressLength q n m c C1 C3) :=
  payloadEquiv.trans ((payloadIndex eF e1 e3).trans (finCongr (taggedLength_eq _ _ _ _ _ _)))

@[simp] theorem decode_encode (eF : F ≃ Fin q) (e1 : Coefficients t 1 ≃ Fin C1)
    (e3 : Coefficients t 3 ≃ Fin C3) (z : Query F n m c t) :
    (equiv eF e1 e3).symm (equiv eF e1 e3 z) = z := (equiv eF e1 e3).symm_apply_apply z

@[simp] theorem encode_decode (eF : F ≃ Fin q) (e1 : Coefficients t 1 ≃ Fin C1)
    (e3 : Coefficients t 3 ≃ Fin C3) (z : Fin (addressLength q n m c C1 C3)) :
    equiv eF e1 e3 ((equiv eF e1 e3).symm z) = z := (equiv eF e1 e3).apply_symm_apply z

/-- The explicit codec proves the exact address-space cardinality. -/
theorem card_addressLength [Fintype F] (eF : F ≃ Fin q) (e1 : Coefficients t 1 ≃ Fin C1)
    (e3 : Coefficients t 3 ≃ Fin C3) :
    Fintype.card (Query F n m c t) = addressLength q n m c C1 C3 := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (equiv eF e1 e3)

end PCP.Algebraic.ThreeColorQueryIndex
