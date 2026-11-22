/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteBooleanConstraints
import PCP.Reduction.ThreeSATGraphEncoding

/-!
# Numeric encoding of fixed-arity Boolean constraints

Explicit finite-function, sum and product codecs index all source variables,
comparison flags and ternary clauses. The resulting graph bitstring is the exact
input format of the three-color verifier. No enumeration is chosen at run time.
-/

namespace PCP.Reduction.FiniteBooleanEncoding

open NAEThreeColor FiniteBooleanConstraints

/-- Numeric order on the `k` comparison bits. -/
def patternCode (k : ℕ) : Pattern k ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) ThreeSATGraphEncoding.boolCode).trans
    (@finFunctionFinEquiv 2 k)

/-- Constraint number, input pattern, then position in its comparison chain. -/
def auxCode (c k : ℕ) : Aux (Fin c) k ≃ Fin (c * 2 ^ k * (k + 1)) :=
  ((Equiv.prodCongr (Equiv.refl (Fin c))
    ((Equiv.prodCongr (patternCode k) (Equiv.refl (Fin (k + 1)))).trans
      finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by ring))

/-- Source variables precede the freshly introduced flags. -/
def variableCode (v c k : ℕ) : Variable (Fin v) (Fin c) k ≃
    Fin (v + c * 2 ^ k * (k + 1)) :=
  (Equiv.sumCongr (Equiv.refl (Fin v)) (auxCode c k)).trans finSumFinEquiv

/-- Gate clauses precede the two endpoint clauses within each comparison chain. -/
def clauseCode (c k : ℕ) : Clause (Fin c) k ≃ Fin (c * 2 ^ k * (3 * k + 2)) :=
  ((Equiv.prodCongr (Equiv.refl (Fin c))
    ((Equiv.prodCongr (patternCode k)
      (((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finSumFinEquiv).trans
        (finCongr (show k * 3 + 2 = 3 * k + 2 by omega)))).trans finProdFinEquiv)).trans
          finProdFinEquiv).trans (finCongr (by ring))

variable {v c k : ℕ}

/-- The finite Boolean constraint compiler with completely numeric variable and clause indices. -/
def indexedClauses (relation : Fin c → Pattern k → Bool) (scope : Fin c → Fin k → Fin v) :
    Fin (c * 2 ^ k * (3 * k + 2)) → Fin 3 → Literal (Fin (v + c * 2 ^ k * (k + 1))) :=
  fun j i => ThreeSATToColor.mapLiteral (variableCode v c k)
    (clauses relation scope ((clauseCode c k).symm j) i)

theorem indexedClauses_satisfies_iff (relation : Fin c → Pattern k → Bool)
    (scope : Fin c → Fin k → Fin v) (a : Fin (v + c * 2 ^ k * (k + 1)) → Bool) :
    ThreeSATToColor.Satisfies (indexedClauses relation scope) a ↔
      ThreeSATToColor.Satisfies (clauses relation scope) (a ∘ variableCode v c k) := by
  constructor
  · intro h j
    simpa only [indexedClauses, Equiv.symm_apply_apply, ThreeSATToColor.eval_mapLiteral]
      using h (clauseCode c k j)
  · intro h j
    simpa only [indexedClauses, ThreeSATToColor.eval_mapLiteral]
      using h ((clauseCode c k).symm j)

theorem indexedClauses_satisfiable_iff (relation : Fin c → Pattern k → Bool)
    (scope : Fin c → Fin k → Fin v) :
    (∃ a, ThreeSATToColor.Satisfies (indexedClauses relation scope) a) ↔
      ∃ a : Fin v → Bool, LocalHolds relation scope a := by
  rw [← FiniteBooleanConstraints.satisfiable_iff relation scope]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ variableCode v c k, (indexedClauses_satisfies_iff relation scope a).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ (variableCode v c k).symm, ?_⟩
    apply (indexedClauses_satisfies_iff relation scope _).mpr
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using ha

/-- The actual bitstring consumed by the algebraic three-color verifier. -/
def encode (relation : Fin c → Pattern k → Bool) (scope : Fin c → Fin k → Fin v) :
    List Bool := ThreeSATGraphEncoding.encode (indexedClauses relation scope)

/-- Exact source satisfiability after constructing and decoding the graph bitstring. -/
theorem decode_colorable_iff (relation : Fin c → Pattern k → Bool)
    (scope : Fin c → Fin k → Fin v) :
    (Algebraic.ThreeColorEncoding.graph (encode relation scope)).Colorable 3 ↔
      ∃ a : Fin v → Bool, LocalHolds relation scope a :=
  (ThreeSATGraphEncoding.decode_colorable_iff _).trans
    (indexedClauses_satisfiable_iff relation scope)

/-- Quadratic output size in the explicitly counted variables and ternary clauses. -/
theorem length_encode_le (relation : Fin c → Pattern k → Bool)
    (scope : Fin c → Fin k → Fin v) :
    (encode relation scope).length ≤
      64 * (v + c * 2 ^ k * (k + 1) + c * 2 ^ k * (3 * k + 2) + 1) ^ 2 :=
  ThreeSATGraphEncoding.length_encode_le _

end PCP.Reduction.FiniteBooleanEncoding
