/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorVerifier
import Mathlib.Tactic.DeriveFintype

/-!
# One binary oracle for the eight physical three-color proof tables

The tagged query type is an exact address space for all eight received tables.
Reading a proof and splitting an arbitrary binary oracle into its tables are
inverse operations. This identifies the actual verifier with a single binary
oracle and makes its finite proof address space explicit; no polynomial-size,
sampling or running-time claim is made here.
-/

namespace PCP.Algebraic.ThreeColorVerifier

open BinaryPolynomialSpace

variable {F : Type*} {n m c t : ℕ}

/-- Split one binary oracle into exactly the verifier's eight physical tables. -/
def ofOracle (b : Query F n m c t → ZMod 2) : Proof F n m c t where
  color x q := b (.color x q)
  validCert x q := b (.validCert x q)
  difference x q := b (.difference x q)
  properCert x q := b (.properCert x q)
  colorLines uv x q := b (.colorLine uv x q)
  validLines uv x q := b (.validLine uv x q)
  differenceLines uv x q := b (.differenceLine uv x q)
  properLines uv x q := b (.properLine uv x q)

@[simp] theorem read_ofOracle (b : Query F n m c t → ZMod 2) (q : Query F n m c t) :
    read (ofOracle b) q = b q := by
  cases q <;> rfl

@[simp] theorem ofOracle_read (π : Proof F n m c t) : ofOracle (read π) = π := by
  cases π
  rfl

/-- The eight-table presentation is exactly a single binary oracle on physical addresses. -/
def oracleEquiv : Proof F n m c t ≃ (Query F n m c t → ZMod 2) where
  toFun := read
  invFun := ofOracle
  left_inv := ofOracle_read
  right_inv b := funext (read_ofOracle b)

private noncomputable def queryProxyEquiv := proxy_equiv% (Query F n m c t)

private noncomputable instance queryProxyFintype [Fintype F] :
    Fintype (Query.proxyType F n m c t) := by
  classical
  letI : Fintype (Vertex F n) := inferInstance
  letI : Fintype (PairPoint F n) := inferInstance
  letI : Fintype (ProperPoint F n) := inferInstance
  letI : Fintype (BinaryLocalCorrection.InnerPoint F m c) := inferInstance
  unfold Query.proxyType
  repeat' first | infer_instance | refine @instFintypeSum _ _ ?_ ?_

/-- The actual physical address space is finite whenever the field alphabet is finite. -/
noncomputable instance queryFintype [Fintype F] : Fintype (Query F n m c t) :=
  Fintype.ofEquiv _ queryProxyEquiv

/-- Exact address count: two cubic primary tables, two affine primary tables,
and four affine line tables, including the two distinct tables on pair points. -/
theorem card_query [Fintype F] :
    Fintype.card (Query F n m c t) =
      (Fintype.card F ^ n + Fintype.card F ^ (n + n)) * Fintype.card (Coefficients t 3) +
      (Fintype.card F ^ (n + n) + Fintype.card F ^ ((n + n) + (n + n))) *
        Fintype.card (Coefficients t 1) +
      ((Fintype.card F ^ n) ^ 2 + 2 * (Fintype.card F ^ (n + n)) ^ 2 +
        (Fintype.card F ^ ((n + n) + (n + n))) ^ 2) *
          Fintype.card F ^ (c * m) * Fintype.card (Coefficients t 1) := by
  classical
  rw [← Fintype.card_congr (queryProxyEquiv (F := F) (n := n) (m := m) (c := c) (t := t))]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Vertex, PairPoint, ProperPoint, BinaryLocalCorrection.InnerPoint, SetMultilinear.Variables,
    Fintype.card_fun, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]
  ring

/-- A finite indexing identifies the same proof with a binary word of the exact
address-space length. The chosen indexing carries no efficiency claim. -/
noncomputable def indexedOracleEquiv [Fintype F] :
    Proof F n m c t ≃ (Fin (Fintype.card (Query F n m c t)) → ZMod 2) :=
  oracleEquiv.trans (Equiv.arrowCongr (Fintype.equivFin (Query F n m c t)) (Equiv.refl _))

end PCP.Algebraic.ThreeColorVerifier
