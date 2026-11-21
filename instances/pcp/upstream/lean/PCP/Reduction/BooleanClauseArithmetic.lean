/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteBooleanEncoding
import PCP.Reduction.ThreeColorNumericAdjacency

/-!
# Arithmetic literal addresses for the local Boolean constraint compiler

The clause index exposes its source constraint, fixed Boolean pattern, comparison
gate, and gate-literal position. Every resulting graph-literal address is obtained
by natural arithmetic and the local scope/relation table entries.
-/

namespace PCP.Reduction.BooleanClauseArithmetic

open NAEThreeColor FiniteBooleanConstraints ThreeColorNumericAdjacency

/-- Negate a valid constant or variable literal address. -/
def negative (a : ℕ) : ℕ :=
  if a < 3 then 1 - a else if (a - 3) % 2 = 0 then a + 1 else a - 1

theorem negative_literal {v : ℕ} (l : Literal (Fin v)) :
    negative (literalAddress l) = literalAddress (negate l) := by
  cases l with
  | const b => cases b <;> rfl
  | var i b => cases b <;> simp [negative, literalAddress, negate, Nat.add_assoc]

theorem map_negate {V W : Type*} (f : V → W) (l : Literal V) :
    ThreeSATToColor.mapLiteral f (negate l) = negate (ThreeSATToColor.mapLiteral f l) := by
  cases l <;> rfl

/-- The three gate clauses, in the exact source-compiler order. -/
def gate (z x y j i : ℕ) : ℕ :=
  if j = 0 then if i = 0 then z else if i = 1 then negative x else 0 else
  if j = 1 then if i = 0 then z else if i = 1 then negative y else 0 else
    if i = 0 then negative z else if i = 1 then x else y

theorem gate_correct {v : ℕ} (z x y : Literal (Fin v)) (j i : Fin 3) :
    gate (literalAddress z) (literalAddress x) (literalAddress y) j.val i.val =
      literalAddress (orGate z x y j i) := by
  fin_cases j <;> fin_cases i <;> simp [gate, orGate, negative_literal] <;> rfl

theorem map_orGate {V W : Type*} (f : V → W) (z x y : Literal V) (j i : Fin 3) :
    ThreeSATToColor.mapLiteral f (orGate z x y j i) =
      orGate (ThreeSATToColor.mapLiteral f z) (ThreeSATToColor.mapLiteral f x)
        (ThreeSATToColor.mapLiteral f y) j i := by
  fin_cases j <;> fin_cases i <;> simp [orGate, map_negate] <;> rfl

def flag (v k e p i : ℕ) : ℕ := 3 + 2 * (v + (e * 2 ^ k + p) * (k + 1) + i)

theorem auxCode_val {c k : ℕ} (e : Fin c) (p : Pattern k) (i : Fin (k + 1)) :
    (FiniteBooleanEncoding.auxCode c k (e, p, i)).val =
      (e.val * 2 ^ k + (FiniteBooleanEncoding.patternCode k p).val) * (k + 1) + i.val := by
  simp [FiniteBooleanEncoding.auxCode, finProdFinEquiv]
  ring

theorem flag_correct {v c k : ℕ} (e : Fin c) (p : Pattern k) (i : Fin (k + 1)) :
    flag v k e.val (FiniteBooleanEncoding.patternCode k p).val i.val =
      literalAddress (ThreeSATToColor.mapLiteral (FiniteBooleanEncoding.variableCode v c k)
        (flagLiteral e p i)) := by
  change flag v k e.val (FiniteBooleanEncoding.patternCode k p).val i.val =
    3 + 2 * (v + (FiniteBooleanEncoding.auxCode c k (e, p, i)).val)
  rw [auxCode_val]
  unfold flag
  ring

theorem difference_correct {v c k : ℕ} (scope : Fin c → Fin k → Fin v)
    (e : Fin c) (p : Pattern k) (i : Fin k) :
    3 + (2 * (scope e i).val + (p i).toNat) =
      literalAddress (ThreeSATToColor.mapLiteral (FiniteBooleanEncoding.variableCode v c k)
        (differenceLiteral scope e p i)) := by
  rfl

/-- Arithmetic address of one ternary literal within one pattern's comparison chain. -/
def localAddress (v k e p q i : ℕ) (scope : ℕ → ℕ) (pattern : ℕ → ℕ) (relation : ℕ) : ℕ :=
  if q < 3 * k then
    gate (flag v k e p (q / 3 + 1)) (flag v k e p (q / 3))
      (3 + (2 * scope (q / 3) + pattern (q / 3))) (q % 3) i
  else if q = 3 * k then
    if i = 0 then negative (flag v k e p 0) else 0
  else if i = 0 then relation else if i = 1 then flag v k e p k else 0

/-- Position within the pattern block, independent of source constraint count. -/
def localCode {k : ℕ} : (Fin k × Fin 3) ⊕ Fin 2 → ℕ
  | .inl (i, j) => 3 * i.val + j.val
  | .inr j => 3 * k + j.val

theorem localAddress_correct {v c k : ℕ}
    (relation : Fin c → Pattern k → Bool) (scope : Fin c → Fin k → Fin v)
    (e : Fin c) (p : Pattern k) (q : (Fin k × Fin 3) ⊕ Fin 2) (i : Fin 3)
    (scopeNat patternNat : ℕ → ℕ)
    (hscope : ∀ j : Fin k, scopeNat j.val = (scope e j).val)
    (hpattern : ∀ j : Fin k, patternNat j.val = (p j).toNat) :
    localAddress v k e.val (FiniteBooleanEncoding.patternCode k p).val (localCode q) i.val
        scopeNat patternNat (relation e p).toNat =
      literalAddress (ThreeSATToColor.mapLiteral (FiniteBooleanEncoding.variableCode v c k)
        (clauses relation scope (e, p, q) i)) := by
  rcases q with ⟨j, g⟩ | b
  · have hq : 3 * j.val + g.val < 3 * k := by omega
    have hdiv : (3 * j.val + g.val) / 3 = j.val := by omega
    have hmod : (3 * j.val + g.val) % 3 = g.val := by omega
    simp only [localAddress, localCode, ite_eq_left hq, hdiv, hmod, hscope, hpattern,
      clauses, map_orGate]
    rw [← gate_correct, ← difference_correct, ← flag_correct, ← flag_correct]
    rfl
  · fin_cases b <;> fin_cases i <;>
      simp [localAddress, localCode, clauses, flag, flagLiteral, ThreeSATToColor.mapLiteral,
        FiniteBooleanEncoding.variableCode, FiniteBooleanEncoding.auxCode, finProdFinEquiv,
        finSumFinEquiv, literalAddress, negate, negative] <;> ring_nf

theorem localCode_lt {k : ℕ} (q : (Fin k × Fin 3) ⊕ Fin 2) : localCode q < 3 * k + 2 := by
  rcases q with ⟨i, j⟩ | b <;> simp only [localCode] <;> omega

theorem clauseCode_val {c k : ℕ} (e : Fin c) (p : Pattern k)
    (q : (Fin k × Fin 3) ⊕ Fin 2) :
    (FiniteBooleanEncoding.clauseCode c k (e, p, q)).val =
      (e.val * 2 ^ k + (FiniteBooleanEncoding.patternCode k p).val) * (3 * k + 2) +
        localCode q := by
  rcases q with ⟨i, j⟩ | b <;>
    simp [FiniteBooleanEncoding.clauseCode, localCode, finProdFinEquiv, finSumFinEquiv] <;> ring

/-- The complete natural-index decoder for one compiled ternary literal. -/
def address (v k clauseIndex i : ℕ) (scope : ℕ → ℕ → ℕ)
    (pattern : ℕ → ℕ → ℕ) (relation : ℕ → ℕ → ℕ) : ℕ :=
  let chain := clauseIndex / (3 * k + 2)
  localAddress v k (chain / 2 ^ k) (chain % 2 ^ k) (clauseIndex % (3 * k + 2)) i
    (scope (chain / 2 ^ k)) (pattern (chain % 2 ^ k))
      (relation (chain / 2 ^ k) (chain % 2 ^ k))

/-- The arithmetic decoder agrees with the actual indexed ternary-clause compiler. -/
theorem address_correct {v c k : ℕ}
    (relation : Fin c → Pattern k → Bool) (scope : Fin c → Fin k → Fin v)
    (scopeNat patternNat relationNat : ℕ → ℕ → ℕ)
    (hscope : ∀ (e : Fin c) (j : Fin k), scopeNat e.val j.val = (scope e j).val)
    (hpattern : ∀ (p : Pattern k) (j : Fin k),
      patternNat (FiniteBooleanEncoding.patternCode k p).val j.val = (p j).toNat)
    (hrelation : ∀ (e : Fin c) (p : Pattern k),
      relationNat e.val (FiniteBooleanEncoding.patternCode k p).val = (relation e p).toNat)
    (j : Fin (c * 2 ^ k * (3 * k + 2))) (i : Fin 3) :
    address v k j.val i.val scopeNat patternNat relationNat =
      literalAddress (FiniteBooleanEncoding.indexedClauses relation scope j i) := by
  obtain ⟨⟨e, p, q⟩, rfl⟩ := (FiniteBooleanEncoding.clauseCode c k).surjective j
  have hq := localCode_lt q
  have hp := (FiniteBooleanEncoding.patternCode k p).isLt
  have htwo : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hdiv : (FiniteBooleanEncoding.clauseCode c k (e, p, q)).val / (3 * k + 2) =
      e.val * 2 ^ k + (FiniteBooleanEncoding.patternCode k p).val := by
    rw [clauseCode_val, Nat.mul_comm _ (3 * k + 2), Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt hq, Nat.add_zero]
  have hmod : (FiniteBooleanEncoding.clauseCode c k (e, p, q)).val % (3 * k + 2) =
      localCode q := by
    rw [clauseCode_val]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hq]
  have he : (e.val * 2 ^ k + (FiniteBooleanEncoding.patternCode k p).val) / 2 ^ k = e.val := by
    rw [Nat.mul_comm e.val, Nat.mul_add_div htwo, Nat.div_eq_of_lt hp, Nat.add_zero]
  have hp' : (e.val * 2 ^ k + (FiniteBooleanEncoding.patternCode k p).val) % 2 ^ k =
      (FiniteBooleanEncoding.patternCode k p).val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hp]
  simp only [address, hdiv, hmod, he, hp', hrelation,
    FiniteBooleanEncoding.indexedClauses, Equiv.symm_apply_apply]
  exact localAddress_correct relation scope e p q i _ _ (hscope e) (hpattern p)

end PCP.Reduction.BooleanClauseArithmetic
