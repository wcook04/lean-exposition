/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteDomainConstraints
import PCP.Reduction.FiniteBooleanEncoding

/-!
# Graph bitstrings for constraints over a fixed finite alphabet

Explicit source indices, followed by sum and product codecs, identify the one-hot
variables and constraints with natural intervals. The complete reduction preserves
satisfiability and has quadratic output length for fixed alphabet and relation arity.
-/

namespace PCP.Reduction.FiniteDomainEncoding

open FiniteDomainConstraints

variable {V C : Type*} {v c a d : ℕ}

/-- One-hot blocks follow the supplied source-variable order, with one dummy block last. -/
def variableCode (eV : V ≃ Fin v) : Variable V a ≃ Fin ((v + 1) * a) :=
  (Equiv.prodCongr
    ((Equiv.sumCongr eV (Equiv.equivPUnit (Fin 1)).symm).trans finSumFinEquiv)
    (Equiv.refl (Fin a))).trans finProdFinEquiv

/-- Relation constraints precede the one-hot validity constraints. -/
def constraintCode (eV : V ≃ Fin v) (eC : C ≃ Fin c) : Constraint V C ≃ Fin (c + v) :=
  (Equiv.sumCongr eC eV).trans finSumFinEquiv

def indexedRelation (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) :
    Fin (c + v) → FiniteBooleanConstraints.Pattern (arity a d) → Bool :=
  fun e => relation R ((constraintCode eV eC).symm e)

def indexedScope (eV : V ≃ Fin v) (eC : C ≃ Fin c) (s : C → Fin d → V) :
    Fin (c + v) → Fin (arity a d) → Fin ((v + 1) * a) :=
  fun e i => variableCode eV (scope s ((constraintCode eV eC).symm e) i)

theorem indexed_holds_iff (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V)
    (b : Fin ((v + 1) * a) → Bool) :
    FiniteBooleanConstraints.LocalHolds (indexedRelation eV eC R) (indexedScope eV eC s) b ↔
      FiniteBooleanConstraints.LocalHolds (relation R) (scope s) (b ∘ variableCode eV) := by
  constructor
  · intro h e
    simpa only [indexedRelation, indexedScope, Equiv.symm_apply_apply, Function.comp_def]
      using h (constraintCode eV eC e)
  · intro h e
    exact h ((constraintCode eV eC).symm e)

theorem indexed_satisfiable_iff (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :
    (∃ b, FiniteBooleanConstraints.LocalHolds
      (indexedRelation eV eC R) (indexedScope eV eC s) b) ↔
        ∃ x : V → Fin a, Holds R s x := by
  rw [← FiniteDomainConstraints.satisfiable_iff R s]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b ∘ variableCode eV, (indexed_holds_iff eV eC R s b).mp hb⟩
  · rintro ⟨b, hb⟩
    refine ⟨b ∘ (variableCode eV).symm, (indexed_holds_iff eV eC R s _).mpr ?_⟩
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hb

/-- The actual adjacency-matrix input consumed by the repaired PCP verifier. -/
def encode (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) : List Bool :=
  FiniteBooleanEncoding.encode (indexedRelation eV eC R) (indexedScope eV eC s)

theorem decode_colorable_iff (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :
    (Algebraic.ThreeColorEncoding.graph (encode eV eC R s)).Colorable 3 ↔
      ∃ x : V → Fin a, Holds R s x :=
  (FiniteBooleanEncoding.decode_colorable_iff _ _).trans (indexed_satisfiable_iff eV eC R s)

/-- For fixed alphabet and local arity, this is quadratic in the source instance size. -/
theorem length_encode_le (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :
    (encode eV eC R s).length ≤
      64 * ((v + 1) * a + (c + v) * 2 ^ arity a d * (arity a d + 1) +
        (c + v) * 2 ^ arity a d * (3 * arity a d + 2) + 1) ^ 2 :=
  FiniteBooleanEncoding.length_encode_le _ _

open Polynomial in
/-- Uniform output-size polynomial for any polynomially bounded family of source instances. -/
noncomputable def outputPoly (a d : ℕ) (pvars pcons : Polynomial ℕ) : Polynomial ℕ :=
  64 * ((pvars + 1) * Polynomial.C a +
    (pcons + pvars) * Polynomial.C (2 ^ arity a d * (4 * arity a d + 3)) + 1) ^ 2

theorem length_encode_le_polynomial (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V)
    (pvars pcons : Polynomial ℕ) (n : ℕ)
    (hv : v ≤ pvars.eval n) (hc : c ≤ pcons.eval n) :
    (encode eV eC R s).length ≤ (outputPoly a d pvars pcons).eval n := by
  apply (length_encode_le eV eC R s).trans
  simp only [outputPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_C]
  have h : (v + 1) * a + (c + v) * 2 ^ arity a d * (arity a d + 1) +
      (c + v) * 2 ^ arity a d * (3 * arity a d + 2) + 1 =
      (v + 1) * a + (c + v) * (2 ^ arity a d * (4 * arity a d + 3)) + 1 := by ring
  rw [h]
  gcongr

end PCP.Reduction.FiniteDomainEncoding
