/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.BooleanClauseSource
import PCP.Reduction.ThreeSATNumericClauses

/-!
# Arithmetic syntax for all clause-literal operations

These terms use only ordinary arithmetic, comparisons, and conditionals. The
truth-table and scope entries are scalar inputs supplied by bounded stored reads.
-/

namespace PCP.Reduction.BooleanClauseTerms

open PCP.Lang.ArithmeticExpression

variable {n : ℕ}

private theorem bit_test (p : Prop) [Decidable p] :
    ((if p then 1 else 0) : ℕ) ≠ 0 ↔ p := by by_cases h : p <;> simp [h]

def negative (a : Term n) : Term n :=
  .cond (.bin .lt a (.const 3)) (.bin .sub (.const 1) a)
    (.cond (.bin .eq (.bin .mod (.bin .sub a (.const 3)) (.const 2)) (.const 0))
      (.bin .add a (.const 1)) (.bin .sub a (.const 1)))

private def negativeN (a : ℕ) : ℕ :=
  if (if a < 3 then 1 else 0) ≠ 0 then 1 - a else
    if (if (a - 3) % 2 = 0 then 1 else 0) ≠ 0 then a + 1 else a - 1

private theorem negativeN_eq (a : ℕ) : negativeN a = BooleanClauseArithmetic.negative a := by
  simp only [negativeN, bit_test, BooleanClauseArithmetic.negative]

theorem negative_eval (a : Term n) (r : Fin n → ℕ) :
    (negative a).eval r = BooleanClauseArithmetic.negative (a.eval r) :=
  negativeN_eq (a.eval r)

def flag (k : ℕ) (v e p i : Term n) : Term n :=
  .bin .add (.const 3) (.bin .mul (.const 2)
    (.bin .add (.bin .add v
      (.bin .mul (.bin .add (.bin .mul e (.const (2 ^ k))) p) (.const (k + 1)))) i))

theorem flag_eval (k : ℕ) (v e p i : Term n) (r : Fin n → ℕ) :
    (flag k v e p i).eval r = BooleanClauseArithmetic.flag
      (v.eval r) k (e.eval r) (p.eval r) (i.eval r) := rfl

def gate (z x y j i : Term n) : Term n :=
  .cond (.bin .eq j (.const 0))
    (.cond (.bin .eq i (.const 0)) z (.cond (.bin .eq i (.const 1)) (negative x) (.const 0)))
    (.cond (.bin .eq j (.const 1))
      (.cond (.bin .eq i (.const 0)) z (.cond (.bin .eq i (.const 1)) (negative y) (.const 0)))
      (.cond (.bin .eq i (.const 0)) (negative z) (.cond (.bin .eq i (.const 1)) x y)))

private def gateN (z x y j i : ℕ) : ℕ :=
  if (if j = 0 then 1 else 0) ≠ 0 then
    if (if i = 0 then 1 else 0) ≠ 0 then z else
      if (if i = 1 then 1 else 0) ≠ 0 then negativeN x else 0
  else if (if j = 1 then 1 else 0) ≠ 0 then
    if (if i = 0 then 1 else 0) ≠ 0 then z else
      if (if i = 1 then 1 else 0) ≠ 0 then negativeN y else 0
  else if (if i = 0 then 1 else 0) ≠ 0 then negativeN z else
    if (if i = 1 then 1 else 0) ≠ 0 then x else y

private theorem gateN_eq (z x y j i : ℕ) : gateN z x y j i =
    BooleanClauseArithmetic.gate z x y j i := by
  simp only [gateN, bit_test, negativeN_eq, BooleanClauseArithmetic.gate]

theorem gate_eval (z x y j i : Term n) (r : Fin n → ℕ) :
    (gate z x y j i).eval r = BooleanClauseArithmetic.gate
      (z.eval r) (x.eval r) (y.eval r) (j.eval r) (i.eval r) :=
  gateN_eq _ _ _ _ _

/-- Local-clause evaluation uses the three already loaded scalar table entries. -/
def localValue (v k e p q i scope pattern relation : ℕ) : ℕ :=
  BooleanClauseArithmetic.localAddress v k e p q i (fun _ => scope) (fun _ => pattern) relation

def localTerm (k : ℕ) (v e p q i scope pattern relation : Term n) : Term n :=
  .cond (.bin .lt q (.const (3 * k)))
    (gate (flag k v e p (.bin .add (.bin .div q (.const 3)) (.const 1)))
      (flag k v e p (.bin .div q (.const 3)))
      (.bin .add (.const 3) (.bin .add (.bin .mul (.const 2) scope) pattern))
      (.bin .mod q (.const 3)) i)
    (.cond (.bin .eq q (.const (3 * k)))
      (.cond (.bin .eq i (.const 0)) (negative (flag k v e p (.const 0))) (.const 0))
      (.cond (.bin .eq i (.const 0)) relation
        (.cond (.bin .eq i (.const 1)) (flag k v e p (.const k)) (.const 0))))

private def localN (v k e p q i scope pattern relation : ℕ) : ℕ :=
  if (if q < 3 * k then 1 else 0) ≠ 0 then
    gateN (BooleanClauseArithmetic.flag v k e p (q / 3 + 1))
      (BooleanClauseArithmetic.flag v k e p (q / 3))
      (3 + (2 * scope + pattern)) (q % 3) i
  else if (if q = 3 * k then 1 else 0) ≠ 0 then
    if (if i = 0 then 1 else 0) ≠ 0 then negativeN (BooleanClauseArithmetic.flag v k e p 0) else 0
  else if (if i = 0 then 1 else 0) ≠ 0 then relation else
    if (if i = 1 then 1 else 0) ≠ 0 then BooleanClauseArithmetic.flag v k e p k else 0

private theorem localN_eq (v k e p q i scope pattern relation : ℕ) :
    localN v k e p q i scope pattern relation = localValue v k e p q i scope pattern relation := by
  simp only [localN, bit_test, gateN_eq, negativeN_eq,
    localValue, BooleanClauseArithmetic.localAddress]

theorem localTerm_eval (k : ℕ) (v e p q i scope pattern relation : Term n) (r : Fin n → ℕ) :
    (localTerm k v e p q i scope pattern relation).eval r =
      localValue (v.eval r) k (e.eval r) (p.eval r) (q.eval r) (i.eval r)
        (scope.eval r) (pattern.eval r) (relation.eval r) :=
  localN_eq _ _ _ _ _ _ _ _ _

def splitValue (v e i original : ℕ) : ℕ :=
  if e % 2 = 0 then if i < 2 then original else 3 + 2 * (v + e / 2) else
    if i = 0 then 3 + (2 * (v + e / 2) + 1) else if i = 1 then original else 0

def splitTerm (v e i original : Term n) : Term n :=
  .cond (.bin .eq (.bin .mod e (.const 2)) (.const 0))
    (.cond (.bin .lt i (.const 2)) original
      (.bin .add (.const 3) (.bin .mul (.const 2) (.bin .add v (.bin .div e (.const 2))))))
    (.cond (.bin .eq i (.const 0))
      (.bin .add (.const 3) (.bin .add
        (.bin .mul (.const 2) (.bin .add v (.bin .div e (.const 2)))) (.const 1)))
      (.cond (.bin .eq i (.const 1)) original (.const 0)))

private def splitN (v e i original : ℕ) : ℕ :=
  if (if e % 2 = 0 then 1 else 0) ≠ 0 then
    if (if i < 2 then 1 else 0) ≠ 0 then original else 3 + 2 * (v + e / 2)
  else if (if i = 0 then 1 else 0) ≠ 0 then 3 + (2 * (v + e / 2) + 1) else
    if (if i = 1 then 1 else 0) ≠ 0 then original else 0

private theorem splitN_eq (v e i original : ℕ) :
    splitN v e i original = splitValue v e i original := by
  simp only [splitN, bit_test, splitValue]

theorem splitTerm_eval (v e i original : Term n) (r : Fin n → ℕ) :
    (splitTerm v e i original).eval r = splitValue (v.eval r) (e.eval r) (i.eval r)
      (original.eval r) := splitN_eq _ _ _ _

theorem splitValue_eq (v : ℕ) (lookup : ℕ → ℕ → ℕ) (e i : ℕ) :
    splitValue v e i (lookup (e / 2) (if e % 2 = 0 then i else 2)) =
      ThreeSATNumericClauses.address v lookup e i := by
  by_cases h : e % 2 = 0 <;> simp [splitValue, ThreeSATNumericClauses.address, h]

end PCP.Reduction.BooleanClauseTerms
