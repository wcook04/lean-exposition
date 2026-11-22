/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowQueries
import PCP.Complexity.LangQueryAddressState

/-!
# All eight physical locations for a Hadamard row

A location fixes the table and point payload. Only the coefficient code varies;
the shared physical address formula retains the actual production table offsets.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace HadamardLabel ThreeColorVerifier

variable {F : Type*} {n m c t q r : ℕ}

inductive Location (F : Type*) (n m c : ℕ) : ℕ → Type _
  | color (x : Fin n → F) : Location F n m c 3
  | validCert (x : PairPoint F n) : Location F n m c 1
  | difference (x : PairPoint F n) : Location F n m c 3
  | properCert (x : ProperPoint F n) : Location F n m c 1
  | colorLine (uv : (Fin n → F) × (Fin n → F))
      (x : BinaryLocalCorrection.InnerPoint F m c) :
      Location F n m c 1
  | validLine (uv : (PairPoint F n) × (PairPoint F n))
      (x : BinaryLocalCorrection.InnerPoint F m c) :
      Location F n m c 1
  | differenceLine (uv : (PairPoint F n) × (PairPoint F n))
      (x : BinaryLocalCorrection.InnerPoint F m c) :
      Location F n m c 1
  | properLine (uv : (ProperPoint F n) ×
      (ProperPoint F n))
      (x : BinaryLocalCorrection.InnerPoint F m c) : Location F n m c 1

def Location.query : {r : ℕ} → Location F n m c r → Coefficients t r → Query F n m c t
  | _, .color x, p => .color x p
  | _, .validCert x, p => .validCert x p
  | _, .difference x, p => .difference x p
  | _, .properCert x, p => .properCert x p
  | _, .colorLine uv x, p => .colorLine uv x p
  | _, .validLine uv x, p => .validLine uv x p
  | _, .differenceLine uv x, p => .differenceLine uv x p
  | _, .properLine uv x, p => .properLine uv x p

def Location.payload (eF : F ≃ Fin q) (loc : Location F n m c r) : Fin 10 → ℕ :=
  fun i => QueryAddress.inputs eF (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query 0) i.castSucc

def address (payload : Fin 10 → ℕ) (label : ℕ) : ℕ :=
  QueryAddress.term.eval (Fin.lastCases label payload)

theorem Location.inputs_eq (eF : F ≃ Fin q) (loc : Location F n m c r)
    (p : Coefficients t r) :
    QueryAddress.inputs eF (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query p) =
        Fin.lastCases (code p) (loc.payload (t := t) eF) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · cases loc <;> rfl
  · cases loc <;> fin_cases j <;> rfl

theorem Location.address_eq (eF : F ≃ Fin q) (loc : Location F n m c r)
    (p : Coefficients t r) :
    address (loc.payload (t := t) eF) (code p) =
      (ThreeColorQueryIndex.equiv eF (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query p)).val := by
  rw [address, ← loc.inputs_eq eF p, QueryAddress.term_eq]

end PCP.Lang.HadamardRow
